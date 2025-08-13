// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use std::collections::VecDeque;
use std::sync::Arc;
use tokio::sync::{mpsc, Mutex, Semaphore};
use tracing::{debug, info, warn, error};
use wasmtime::{Engine, Instance, Module, Store};

/// WASM worker pool for high-performance cryptographic operations
pub struct WasmPool {
    /// Engine for running WASM modules
    engine: Engine,
    /// Pool of available workers
    workers: Arc<Mutex<VecDeque<WasmWorker>>>,
    /// Semaphore to limit concurrent workers
    semaphore: Arc<Semaphore>,
    /// Configuration for the pool
    config: WasmPoolConfig,
}

/// Configuration for the WASM pool
#[derive(Debug, Clone)]
pub struct WasmPoolConfig {
    /// Maximum number of concurrent workers
    pub max_workers: usize,
    /// Initial number of workers to pre-warm
    pub initial_workers: usize,
    /// Maximum memory per worker (in MB)
    pub max_memory_mb: usize,
    /// Worker idle timeout (in seconds)
    pub idle_timeout_secs: u64,
    /// Enable JIT compilation
    pub enable_jit: bool,
}

impl Default for WasmPoolConfig {
    fn default() -> Self {
        Self {
            max_workers: 16,
            initial_workers: 4,
            max_memory_mb: 64,
            idle_timeout_secs: 300,
            enable_jit: true,
        }
    }
}

/// Individual WASM worker
struct WasmWorker {
    /// Unique worker ID
    id: String,
    /// WASM store for this worker
    store: Store<()>,
    /// WASM instance
    instance: Instance,
    /// Last used timestamp
    last_used: std::time::Instant,
    /// Current memory usage
    memory_usage: usize,
}

/// Task to be executed by a WASM worker
#[derive(Debug)]
pub struct WasmTask {
    /// Task ID
    pub id: String,
    /// Function name to call
    pub function: String,
    /// Input parameters
    pub params: Vec<Vec<u8>>,
    /// Expected output type
    pub output_type: String,
}

/// Result of WASM task execution
#[derive(Debug)]
pub struct WasmResult {
    /// Task ID
    pub id: String,
    /// Success status
    pub success: bool,
    /// Output data
    pub output: Option<Vec<u8>>,
    /// Error message if failed
    pub error: Option<String>,
    /// Execution time
    pub execution_time: std::time::Duration,
}

impl WasmPool {
    /// Create a new WASM pool
    pub async fn new(config: WasmPoolConfig) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let engine = if config.enable_jit {
            Engine::default()
        } else {
            Engine::new(wasmtime::Config::new().wasm_simd(false))?
        };

        let pool = Self {
            engine,
            workers: Arc::new(Mutex::new(VecDeque::new())),
            semaphore: Arc::new(Semaphore::new(config.max_workers)),
            config,
        };

        // Pre-warm workers
        pool.pre_warm_workers().await?;

        Ok(pool)
    }

    /// Pre-warm workers for better performance
    async fn pre_warm_workers(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        info!("Pre-warming {} WASM workers", self.config.initial_workers);
        
        for i in 0..self.config.initial_workers {
            let worker = self.create_worker(&format!("prewarm_{}", i)).await?;
            let mut workers = self.workers.lock().await;
            workers.push_back(worker);
        }
        
        info!("Pre-warmed {} WASM workers", self.config.initial_workers);
        Ok(())
    }

    /// Create a new WASM worker
    async fn create_worker(&self, id: &str) -> Result<WasmWorker, Box<dyn std::error::Error + Send + Sync>> {
        // Load default cryptographic WASM module
        let wasm_bytes = include_bytes!("../../wasm/crypto.wasm");
        let module = Module::new(&self.engine, wasm_bytes)?;
        
        let mut store = Store::new(&self.engine, ());
        let instance = Instance::new(&mut store, &module, &[])?;
        
        Ok(WasmWorker {
            id: id.to_string(),
            store,
            instance,
            last_used: std::time::Instant::now(),
            memory_usage: 0,
        })
    }

    /// Execute a task using the WASM pool
    pub async fn execute_task(&self, task: WasmTask) -> Result<WasmResult, Box<dyn std::error::Error + Send + Sync>> {
        let _permit = self.semaphore.acquire().await?;
        let start_time = std::time::Instant::now();
        
        // Get available worker
        let worker = self.get_worker().await?;
        
        // Execute task
        let result = self.execute_on_worker(worker, task).await?;
        
        let execution_time = start_time.elapsed();
        let mut wasm_result = result;
        wasm_result.execution_time = execution_time;
        
        Ok(wasm_result)
    }

    /// Get an available worker from the pool
    async fn get_worker(&self) -> Result<WasmWorker, Box<dyn std::error::Error + Send + Sync>> {
        let mut workers = self.workers.lock().await;
        
        // Try to get an existing worker
        if let Some(worker) = workers.pop_front() {
            // Check if worker is still valid
            if worker.is_valid() {
                return Ok(worker);
            }
        }
        
        // Create new worker if needed
        drop(workers);
        let new_worker = self.create_worker(&format!("worker_{}", uuid::Uuid::new_v4())).await?;
        Ok(new_worker)
    }

    /// Execute a task on a specific worker
    async fn execute_on_worker(&self, mut worker: WasmWorker, task: WasmTask) -> Result<WasmResult, Box<dyn std::error::Error + Send + Sync>> {
        // Update worker usage
        worker.last_used = std::time::Instant::now();
        
        // Execute WASM function
        let result = match self.call_wasm_function(&mut worker, &task).await {
            Ok(output) => WasmResult {
                id: task.id,
                success: true,
                output: Some(output),
                error: None,
                execution_time: std::time::Duration::ZERO, // Will be set by caller
            },
            Err(e) => WasmResult {
                id: task.id,
                success: false,
                output: None,
                error: Some(e.to_string()),
                execution_time: std::time::Duration::ZERO, // Will be set by caller
            },
        };
        
        // Return worker to pool if successful
        if result.success {
            let mut workers = self.workers.lock().await;
            workers.push_back(worker);
        }
        
        Ok(result)
    }

    /// Call a WASM function
    async fn call_wasm_function(&self, worker: &mut WasmWorker, task: &WasmTask) -> Result<Vec<u8>, Box<dyn std::error::Error + Send + Sync>> {
        // Get function from instance
        let func = worker.instance.get_func(&mut worker.store, &task.function)
            .ok_or_else(|| format!("Function '{}' not found", task.function))?;
        
        // Convert parameters to WASM values
        let params: Vec<wasmtime::Val> = task.params.iter()
            .map(|param| wasmtime::Val::I32(param.len() as i32))
            .collect();
        
        // Call function
        let results = func.call(&mut worker.store, &params, &mut vec![])?;
        
        // Process results
        if let Some(result) = results.first() {
            match result {
                wasmtime::Val::I32(len) => {
                    // In a real implementation, you'd read memory from the WASM instance
                    // For now, return a placeholder
                    Ok(vec![0u8; *len as usize])
                },
                _ => Err("Unexpected return type".into()),
            }
        } else {
            Err("No return value".into())
        }
    }

    /// Clean up idle workers
    pub async fn cleanup_idle_workers(&self) {
        let mut workers = self.workers.lock().await;
        let now = std::time::Instant::now();
        let timeout = std::time::Duration::from_secs(self.config.idle_timeout_secs);
        
        let initial_count = workers.len();
        workers.retain(|worker| {
            let idle_time = now.duration_since(worker.last_used);
            idle_time < timeout
        });
        
        let removed_count = initial_count - workers.len();
        if removed_count > 0 {
            info!("Cleaned up {} idle WASM workers", removed_count);
        }
    }

    /// Get pool statistics
    pub async fn get_stats(&self) -> WasmPoolStats {
        let workers = self.workers.lock().await;
        let available_workers = workers.len();
        let total_memory: usize = workers.iter().map(|w| w.memory_usage).sum();
        
        WasmPoolStats {
            total_workers: self.config.max_workers,
            available_workers,
            busy_workers: self.config.max_workers - available_workers,
            total_memory_mb: total_memory / (1024 * 1024),
            max_memory_mb: self.config.max_memory_mb,
        }
    }

    /// Shutdown the pool
    pub async fn shutdown(&self) {
        info!("Shutting down WASM pool");
        let mut workers = self.workers.lock().await;
        workers.clear();
        info!("WASM pool shutdown complete");
    }
}

impl WasmWorker {
    /// Check if worker is still valid
    fn is_valid(&self) -> bool {
        // Check memory usage
        if self.memory_usage > self.get_max_memory() {
            return false;
        }
        
        // Check if worker has been idle too long
        let idle_time = std::time::Instant::now().duration_since(self.last_used);
        let max_idle = std::time::Duration::from_secs(3600); // 1 hour
        idle_time < max_idle
    }
    
    /// Get maximum memory for this worker
    fn get_max_memory(&self) -> usize {
        64 * 1024 * 1024 // 64 MB default
    }
}

/// Statistics about the WASM pool
#[derive(Debug, Clone)]
pub struct WasmPoolStats {
    pub total_workers: usize,
    pub available_workers: usize,
    pub busy_workers: usize,
    pub total_memory_mb: usize,
    pub max_memory_mb: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_wasm_pool_creation() {
        let config = WasmPoolConfig::default();
        let pool = WasmPool::new(config).await;
        assert!(pool.is_ok());
    }

    #[tokio::test]
    async fn test_wasm_pool_stats() {
        let config = WasmPoolConfig::default();
        let pool = WasmPool::new(config).await.unwrap();
        
        let stats = pool.get_stats().await;
        assert_eq!(stats.total_workers, 16);
        assert!(stats.available_workers >= 4); // At least pre-warmed workers
    }

    #[tokio::test]
    async fn test_wasm_pool_cleanup() {
        let config = WasmPoolConfig::default();
        let pool = WasmPool::new(config).await.unwrap();
        
        // Initial stats
        let initial_stats = pool.get_stats().await;
        
        // Cleanup
        pool.cleanup_idle_workers().await;
        
        // Stats should remain the same (no idle workers yet)
        let final_stats = pool.get_stats().await;
        assert_eq!(initial_stats.available_workers, final_stats.available_workers);
    }
}
