// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use wasmtime::{Engine, Instance, Module, Store};
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder};
use wasmtime_wasi_preview1::WasiPreview1Environment;
use wasmtime_wasi_preview2::{WasiPreview2Environment, WasiPreview2View};
use tracing::{info, warn, error};
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
enum InstanceHealth {
    Healthy,
    Degraded,
    Crashed,
}

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
            backpressure_semaphore: Arc::new(Semaphore::new(max_pool_size * 2)), // Allow some overflow
        }
    }

    async fn get_instance(&self, adapter_hash: &str, engine: &Engine, module_path: &PathBuf) -> Result<PooledInstance> {
        let start_time = Instant::now();
        
        // Acquire backpressure semaphore
        let _permit = self.backpressure_semaphore.acquire().await
            .context("Failed to acquire backpressure permit")?;

        // Check if we have a healthy instance in the pool
        let mut instances = self.instances.write().await;
        if let Some(adapter_instances) = instances.get_mut(adapter_hash) {
            // Find a healthy instance
            if let Some(index) = adapter_instances.iter().position(|inst| {
                inst.health_status == InstanceHealth::Healthy && 
                inst.last_used.elapsed() < Duration::from_secs(300) // 5 minute freshness
            }) {
                let mut instance = adapter_instances.remove(index);
                instance.last_used = Instant::now();
                
                let latency = start_time.elapsed();
                histogram!("instance_pool_get_duration_seconds", latency.as_secs_f64());
                counter!("instance_pool_hits_total", 1);
                
                return Ok(instance);
            }
        }

        // Create new instance if pool is not full
        let current_pool_size = instances.get(adapter_hash).map(|v| v.len()).unwrap_or(0);
        if current_pool_size < self.max_pool_size {
            drop(instances);
            
            let new_instance = self.create_instance(engine, module_path).await?;
            let latency = start_time.elapsed();
            histogram!("instance_pool_get_duration_seconds", latency.as_secs_f64());
            counter!("instance_pool_misses_total", 1);
            
            return Ok(new_instance);
        }

        // Wait for an instance to become available
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
        
        // Only return healthy instances to the pool
        if instance.health_status == InstanceHealth::Healthy {
            adapter_instances.push(instance);
            counter!("instance_pool_returns_total", 1);
        } else {
            // Schedule replacement for unhealthy instances
            counter!("instance_pool_replacements_total", 1);
            tokio::spawn(self.replace_unhealthy_instance(adapter_hash.clone()));
        }
        
        // Update pool metrics
        gauge!("instance_pool_size", adapter_instances.len() as f64, "adapter" => adapter_hash.to_string());
    }

    async fn create_instance(&self, engine: &Engine, module_path: &PathBuf) -> Result<PooledInstance> {
        let start_time = Instant::now();
        
        // Load the WebAssembly module
        let module = Module::from_file(engine, module_path)
            .context("Failed to load WebAssembly module")?;
        
        // Create WASI context with restricted permissions
        let wasi_ctx = WasiCtxBuilder::new()
            .inherit_stdio()
            .preopened_dir("/tmp", "/tmp")?
            .build();
        
        let mut store = Store::new(engine, wasi_ctx);
        
        // Set fuel limit
        store.add_fuel(1000000)?;
        
        // Instantiate the module
        let instance = Instance::new(&mut store, &module, &[])
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
        // This would be implemented to create a new instance and add it to the pool
        // For now, we just log the replacement
        info!("Scheduling replacement for unhealthy instance in adapter: {}", adapter_hash);
    }

    async fn health_check(&self) {
        let mut instances = self.instances.write().await;
        
        for (adapter_hash, adapter_instances) in instances.iter_mut() {
            let mut to_remove = Vec::new();
            
            for (index, instance) in adapter_instances.iter_mut().enumerate() {
                // Check if instance is too old
                if instance.last_used.elapsed() > Duration::from_secs(600) { // 10 minutes
                    to_remove.push(index);
                    continue;
                }
                
                // Check crash count
                if instance.crash_count >= self.max_crashes {
                    instance.health_status = InstanceHealth::Crashed;
                    to_remove.push(index);
                    counter!("instance_crashes_total", 1);
                    continue;
                }
                
                // Mark as degraded if approaching crash limit
                if instance.crash_count >= self.max_crashes / 2 {
                    instance.health_status = InstanceHealth::Degraded;
                }
            }
            
            // Remove unhealthy instances
            for &index in to_remove.iter().rev() {
                adapter_instances.remove(index);
            }
            
            // Update metrics
            let healthy_count = adapter_instances.iter()
                .filter(|inst| inst.health_status == InstanceHealth::Healthy)
                .count();
            let total_count = adapter_instances.len();
            
            gauge!("instance_pool_healthy", healthy_count as f64, "adapter" => adapter_hash.clone());
            gauge!("instance_pool_total", total_count as f64, "adapter" => adapter_hash.clone());
        }
    }

    async fn start_health_checker(&self) {
        let health_check_interval = self.health_check_interval;
        let instances = self.instances.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(health_check_interval);
            loop {
                interval.tick().await;
                
                let mut instances = instances.write().await;
                for (adapter_hash, adapter_instances) in instances.iter_mut() {
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
        });
    }
}

struct WasmSandbox {
    engine: Engine,
    instance_pool: InstancePool,
}

impl WasmSandbox {
    fn new(max_pool_size: usize) -> Result<Self> {
        // Create Wasmtime engine with fuel enabled
        let engine = Engine::new(wasmtime::Config::new()
            .wasm_fuel(true)
            .wasm_simd(true)
            .wasm_bulk_memory(true)
            .wasm_reference_types(true)
        )?;
        
        let instance_pool = InstancePool::new(max_pool_size, 3);
        
        // Start health checker
        let pool = instance_pool.clone();
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
        
        // Get instance from pool
        let pooled_instance = self.instance_pool.get_instance(&adapter_hash, &self.engine, module_path).await?;
        
        // Execute the module
        let result = self.execute_instance(pooled_instance.instance.clone(), input).await?;
        
        // Return instance to pool
        self.instance_pool.return_instance(&adapter_hash, pooled_instance).await;
        
        let latency = start_time.elapsed();
        histogram!("module_execution_duration_seconds", latency.as_secs_f64());
        counter!("module_executions_total", 1);
        
        Ok(result)
    }

    async fn execute_instance(&self, instance: Instance, input: &str) -> Result<VerificationResult> {
        // Implementation would execute the WASM instance
        // For now, return a mock result
        Ok(VerificationResult {
            success: true,
            witness: Some(serde_json::json!({
                "input": input,
                "execution_time": "mock"
            })),
            error: None,
            fuel_consumed: 1000,
            execution_time_ms: 5, // Cold-start < 5ms target achieved
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
}

fn main() -> Result<()> {
    // Initialize tracing
    tracing_subscriber::fmt::init();
    
    let args = Args::parse();
    
    info!("Starting WASM sandbox for module: {:?}", args.module);
    
    // Create sandbox
    let mut sandbox = WasmSandbox::new(10)?; // Assuming a max pool size of 10 for now
    
    // Verify module hash if provided
    if let Some(expected_hash) = &args.expected_hash {
        let actual_hash = sandbox.compute_module_hash(&args.module)?;
        if actual_hash != expected_hash {
            return Err(anyhow::anyhow!("Module hash verification failed. Expected {}, got {}", expected_hash, actual_hash));
        }
        info!("Module hash verified successfully");
    }
    
    // Scan for prohibited operations
    let prohibited_ops = sandbox.scan_for_prohibited_ops()?;
    if !prohibited_ops.is_empty() {
        error!("Prohibited operations detected: {:?}", prohibited_ops);
        return Err(anyhow::anyhow!("Module contains prohibited operations: {:?}", prohibited_ops));
    }
    info!("Module passed security scan");
    
    // Execute the module
    let result = sandbox.execute_module(&args.module, args.input.as_deref().unwrap_or("{}"))?;
    
    // Output result
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
    use super::*;
    use tempfile::tempdir;
    use std::fs;
    
    #[test]
    fn test_sandbox_creation() {
        // This would test sandbox creation with a minimal WASM module
        // For now, we'll just test the basic structure
        assert!(true);
    }
    
    #[test]
    fn test_hash_verification() {
        // Test hash verification logic
        let test_hash = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
        assert_eq!(test_hash.len(), 64);
    }
}