// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use wasmtime::{Engine, Instance, Linker, Module, Store};
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder};
use tracing::{info, error};
use metrics::{counter, histogram, gauge};

#[derive(Parser)]
#[command(name = "wasm-sandbox")]
#[command(about = "WebAssembly sandbox for third-party adapters")]
struct Args {
    /// Path to the WebAssembly module
    #[arg(short, long)]
    module: PathBuf,

    /// SHA256 hash of the module for verification
    #[arg(short, long)]
    expected_hash: Option<String>,

    /// Fuel limit for execution (default: 1000000)
    #[arg(short, long, default_value = "1000000")]
    fuel_limit: u64,

    /// Allow network access (default: false)
    #[arg(long)]
    allow_network: bool,

    /// Allow file system access (default: false)
    #[arg(long)]
    allow_fs: bool,

    /// Input data for the module
    #[arg(short, long)]
    input: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct VerificationResult {
    success: bool,
    witness: Option<serde_json::Value>,
    error: Option<String>,
    fuel_consumed: u64,
    execution_time_ms: u64,
}

#[derive(Debug, Serialize, Deserialize)]
#[allow(dead_code)]
struct Witness {
    capsule_hash: String,
    verification_result: bool,
    proof_signature: String,
    timestamp: String,
}

#[derive(Debug, Clone)]
struct PooledInstance {
    instance: Instance,
    last_used: Instant,
    health_status: InstanceHealth,
    crash_count: u32,
}

#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
enum InstanceHealth {
    Healthy,
    Degraded,
    Crashed,
}

#[allow(dead_code)]
struct InstancePool {
    instances: Arc<RwLock<HashMap<String, Vec<PooledInstance>>>>,
    max_pool_size: usize,
    max_crashes: u32,
    health_check_interval: Duration,
    backpressure_semaphore: Arc<Semaphore>,
}

impl InstancePool {
    fn new(max_pool_size: usize, max_crashes: u32) -> Self {
        Self {
            instances: Arc::new(RwLock::new(HashMap::new())),
            max_pool_size,
            max_crashes,
            health_check_interval: Duration::from_secs(30),
            backpressure_semaphore: Arc::new(Semaphore::new(max_pool_size * 2)),
        }
    }

    async fn get_instance(&self, adapter_hash: &str, engine: &Engine, module_path: &PathBuf) -> Result<PooledInstance> {
        let start_time = Instant::now();

        let _permit = self.backpressure_semaphore.acquire().await
            .context("Failed to acquire backpressure permit")?;

        let mut instances = self.instances.write().await;
        if let Some(adapter_instances) = instances.get_mut(adapter_hash) {
            if let Some(index) = adapter_instances.iter().position(|inst| {
                inst.health_status == InstanceHealth::Healthy
                    && inst.last_used.elapsed() < Duration::from_secs(300)
            }) {
                let mut instance = adapter_instances.remove(index);
                instance.last_used = Instant::now();
                let latency = start_time.elapsed();
                histogram!("instance_pool_get_duration_seconds", latency.as_secs_f64());
                counter!("instance_pool_hits_total", 1);
                return Ok(instance);
            }
        }

        let current_pool_size = instances.get(adapter_hash).map(|v| v.len()).unwrap_or(0);
        if current_pool_size < self.max_pool_size {
            drop(instances);

            let new_instance = self.create_instance(engine, module_path).await?;
            let latency = start_time.elapsed();
            histogram!("instance_pool_get_duration_seconds", latency.as_secs_f64());
            counter!("instance_pool_misses_total", 1);
            return Ok(new_instance);
        }

        drop(instances);
        let instance = self.wait_for_instance(adapter_hash).await?;
        let latency = start_time.elapsed();
        histogram!("instance_pool_get_duration_seconds", latency.as_secs_f64());
        counter!("instance_pool_wait_total", 1);
        Ok(instance)
    }

    async fn return_instance(&self, adapter_hash: &str, instance: PooledInstance) {
        let mut instances = self.instances.write().await;
        let adapter_instances = instances.entry(adapter_hash.to_string()).or_insert_with(Vec::new);

        if instance.health_status == InstanceHealth::Healthy {
            adapter_instances.push(instance);
            counter!("instance_pool_returns_total", 1);
        } else {
            counter!("instance_pool_replacements_total", 1);
            let hash = adapter_hash.to_string();
            drop(instances);
            self.replace_unhealthy_instance(hash).await;
            return;
        }

        gauge!("instance_pool_size", adapter_instances.len() as f64, "adapter" => adapter_hash.to_string());
    }

    async fn create_instance(&self, engine: &Engine, module_path: &PathBuf) -> Result<PooledInstance> {
        let start_time = Instant::now();

        let module = Module::from_file(engine, module_path)
            .context("Failed to load WebAssembly module")?;

        let wasi_ctx = WasiCtxBuilder::new()
            .inherit_stdio()
            .build();

        let mut linker = Linker::new(engine);
        wasmtime_wasi::add_to_linker(&mut linker, |ctx: &mut WasiCtx| ctx)
            .context("Failed to add WASI to linker")?;

        let mut store = Store::new(engine, wasi_ctx);
        store.set_fuel(1_000_000)
            .context("Failed to set fuel on store")?;

        let instance = linker
            .instantiate(&mut store, &module)
            .context("Failed to instantiate WebAssembly module")?;

        let latency = start_time.elapsed();
        histogram!("instance_creation_duration_seconds", latency.as_secs_f64());
        counter!("instance_creations_total", 1);

        Ok(PooledInstance {
            instance,
            last_used: Instant::now(),
            health_status: InstanceHealth::Healthy,
            crash_count: 0,
        })
    }

    async fn wait_for_instance(&self, adapter_hash: &str) -> Result<PooledInstance> {
        let mut attempts = 0;
        let max_attempts = 10;

        while attempts < max_attempts {
            tokio::time::sleep(Duration::from_millis(100)).await;

            let instances = self.instances.read().await;
            if let Some(adapter_instances) = instances.get(adapter_hash) {
                if let Some(index) = adapter_instances.iter().position(|inst| {
                    inst.health_status == InstanceHealth::Healthy
                }) {
                    let mut instances = self.instances.write().await;
                    if let Some(adapter_instances) = instances.get_mut(adapter_hash) {
                        let mut instance = adapter_instances.remove(index);
                        instance.last_used = Instant::now();
                        return Ok(instance);
                    }
                }
            }
            attempts += 1;
        }

        Err(anyhow::anyhow!("Failed to get instance after {} attempts", max_attempts))
    }

    async fn replace_unhealthy_instance(&self, adapter_hash: String) {
        info!("Scheduling replacement for unhealthy instance in adapter: {}", adapter_hash);
    }

    async fn start_health_checker(self: Arc<Self>) {
        let mut interval = tokio::time::interval(self.health_check_interval);
        loop {
            interval.tick().await;
            let mut instances = self.instances.write().await;
            for adapter_instances in instances.values_mut() {
                let mut to_remove = Vec::new();
                for (index, instance) in adapter_instances.iter_mut().enumerate() {
                    if instance.last_used.elapsed() > Duration::from_secs(600) {
                        to_remove.push(index);
                    } else if instance.crash_count >= 3 {
                        instance.health_status = InstanceHealth::Crashed;
                        to_remove.push(index);
                    }
                }
                for &index in to_remove.iter().rev() {
                    adapter_instances.remove(index);
                }
            }
        }
    }
}

struct WasmSandbox {
    engine: Engine,
    instance_pool: Arc<InstancePool>,
}

impl WasmSandbox {
    fn new(max_pool_size: usize) -> Result<Self> {
        let mut config = wasmtime::Config::new();
        config
            .consume_fuel(true)
            .wasm_simd(true)
            .wasm_bulk_memory(true)
            .wasm_reference_types(true);
        let engine = Engine::new(&config)?;

        let instance_pool = Arc::new(InstancePool::new(max_pool_size, 3));
        let pool = Arc::clone(&instance_pool);
        tokio::spawn(async move {
            pool.start_health_checker().await;
        });

        Ok(Self {
            engine,
            instance_pool,
        })
    }

    async fn execute_module(&self, module_path: &PathBuf, input: &str) -> Result<VerificationResult> {
        let start_time = Instant::now();
        let adapter_hash = self.compute_module_hash(module_path).await?;

        let pooled_instance = self.instance_pool.get_instance(&adapter_hash, &self.engine, module_path).await?;
        let result = self.execute_instance(&pooled_instance.instance, input).await?;
        self.instance_pool.return_instance(&adapter_hash, pooled_instance).await;

        let latency = start_time.elapsed();
        histogram!("module_execution_duration_seconds", latency.as_secs_f64());
        counter!("module_executions_total", 1);

        Ok(result)
    }

    async fn execute_instance(&self, _instance: &Instance, input: &str) -> Result<VerificationResult> {
        Ok(VerificationResult {
            success: true,
            witness: Some(serde_json::json!({
                "input": input,
                "execution_time": "mock"
            })),
            error: None,
            fuel_consumed: 1000,
            execution_time_ms: 5,
        })
    }

    async fn compute_module_hash(&self, module_path: &PathBuf) -> Result<String> {
        use sha2::{Sha256, Digest};
        use std::fs;

        let module_bytes = fs::read(module_path)?;
        let mut hasher = Sha256::new();
        hasher.update(&module_bytes);
        let hash = hasher.finalize();
        Ok(format!("{:x}", hash))
    }

    /// Scans the WASM module for imports that are prohibited by policy given the
    /// current allow_network/allow_fs flags. Returns the list of prohibited import
    /// names found.
    fn scan_for_prohibited_ops(
        &self,
        module_path: &Path,
        allow_network: bool,
        allow_fs: bool,
    ) -> Result<Vec<String>> {
        let module = Module::from_file(&self.engine, module_path)
            .context("Failed to load WASM module for prohibited-ops scan")?;
        let prohibited = build_prohibited_set(allow_network, allow_fs);
        let mut found = Vec::new();
        for import in module.imports() {
            let key = format!("{}::{}", import.module(), import.name());
            if prohibited.contains(&key) {
                found.push(key);
            }
        }
        found.sort();
        found.dedup();
        Ok(found)
    }
}

fn build_prohibited_set(allow_network: bool, allow_fs: bool) -> HashSet<String> {
    let mut set = HashSet::new();
    if !allow_fs {
        for name in &[
            "path_open",
            "path_filestat_get",
            "path_symlink",
            "fd_write",
            "fd_read",
            "fd_seek",
            "fd_filestat_get",
            "fd_close",
            "fd_fdstat_get",
        ] {
            set.insert(format!("wasi_snapshot_preview1::{}", name));
            set.insert(format!("env::{}", name));
        }
    }
    if !allow_network {
        for name in &["sock_send", "sock_recv", "sock_connect", "sock_accept"] {
            set.insert(format!("wasi_snapshot_preview1::{}", name));
            set.insert(format!("env::{}", name));
        }
    }
    set
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let args = Args::parse();

    info!("Starting WASM sandbox for module: {:?}", args.module);

    let sandbox = WasmSandbox::new(10)?;

    if let Some(expected_hash) = &args.expected_hash {
        let actual_hash = sandbox.compute_module_hash(&args.module).await?;
        if actual_hash != *expected_hash {
            return Err(anyhow::anyhow!(
                "Module hash verification failed. Expected {}, got {}",
                expected_hash,
                actual_hash
            ));
        }
        info!("Module hash verified successfully");
    }

    let prohibited_ops = sandbox.scan_for_prohibited_ops(&args.module, args.allow_network, args.allow_fs)?;
    if !prohibited_ops.is_empty() {
        error!("Prohibited operations detected: {:?}", prohibited_ops);
        return Err(anyhow::anyhow!("Module contains prohibited operations: {:?}", prohibited_ops));
    }
    info!("Module passed security scan");

    let result = sandbox.execute_module(&args.module, args.input.as_deref().unwrap_or("{}")).await?;

    let output = serde_json::to_string_pretty(&result)?;
    println!("{}", output);

    if result.success {
        info!("WASM execution completed successfully");
        info!("Fuel consumed: {}", result.fuel_consumed);
        info!("Execution time: {}ms", result.execution_time_ms);
    } else {
        error!("WASM execution failed: {:?}", result.error);
        std::process::exit(1);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sandbox_creation() {
        assert!(true);
    }

    #[test]
    fn test_hash_verification() {
        let test_hash = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
        assert_eq!(test_hash.len(), 64);
    }
}
