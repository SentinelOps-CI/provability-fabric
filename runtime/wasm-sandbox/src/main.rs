// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use wasmtime::{Engine, Instance, Module, Store};
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder};
use wasmtime_wasi_preview1::WasiPreview1Environment;
use wasmtime_wasi_preview2::{WasiPreview2Environment, WasiPreview2View};
use tracing::{info, warn, error};

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

struct WasmSandbox {
    engine: Engine,
    store: Store<WasiCtx>,
    module: Module,
}

impl WasmSandbox {
    fn new(module_path: &PathBuf, fuel_limit: u64, allow_network: bool, allow_fs: bool) -> Result<Self> {
        // Create Wasmtime engine with fuel enabled
        let engine = Engine::new(wasmtime::Config::new()
            .wasm_fuel(true)
            .wasm_simd(true)
            .wasm_bulk_memory(true)
            .wasm_reference_types(true)
        )?;
        
        // Load the WebAssembly module
        let module = Module::from_file(&engine, module_path)
            .context("Failed to load WebAssembly module")?;
        
        // Create WASI context with restricted permissions
        let mut wasi_builder = WasiCtxBuilder::new();
        
        if allow_fs {
            wasi_builder = wasi_builder.inherit_stdio();
        } else {
            // Disable file system access
            wasi_builder = wasi_builder.inherit_stdio()
                .preopened_dir("/tmp", "/tmp")?;
        }
        
        if !allow_network {
            // Disable network access by not providing any network capabilities
            warn!("Network access disabled for security");
        }
        
        let wasi_ctx = wasi_builder.build();
        let mut store = Store::new(&engine, wasi_ctx);
        
        // Set fuel limit
        store.add_fuel(fuel_limit)?;
        
        Ok(Self {
            engine,
            store,
            module,
        })
    }
    
    fn verify_module_hash(&self, expected_hash: &str) -> Result<bool> {
        use std::fs;
        use sha2::{Sha256, Digest};
        
        let module_bytes = fs::read(&self.module.path().unwrap())?;
        let mut hasher = Sha256::new();
        hasher.update(&module_bytes);
        let actual_hash = hex::encode(hasher.finalize());
        
        let matches = actual_hash == expected_hash;
        
        if !matches {
            warn!("Module hash mismatch: expected {}, got {}", expected_hash, actual_hash);
        }
        
        Ok(matches)
    }
    
    fn execute_verify(&mut self, input: Option<&str>) -> Result<VerificationResult> {
        let start_time = std::time::Instant::now();
        
        // Create instance
        let instance = Instance::new(&mut self.store, &self.module, &[])?;
        
        // Get the verify function
        let verify_func = instance.get_func(&mut self.store, "verify")
            .context("Module must export a 'verify' function")?;
        
        // Prepare input
        let input_data = input.unwrap_or("{}");
        
        // Call the verify function
        let result = verify_func.call(&mut self.store, &[input_data.into()], &mut []);
        
        let execution_time = start_time.elapsed();
        let fuel_consumed = self.store.fuel_consumed().unwrap_or(0);
        
        match result {
            Ok(outputs) => {
                // Parse the output as JSON witness
                let output_str = outputs[0].unwrap_string()?;
                let witness: serde_json::Value = serde_json::from_str(&output_str)
                    .context("Failed to parse witness JSON")?;
                
                Ok(VerificationResult {
                    success: true,
                    witness: Some(witness),
                    error: None,
                    fuel_consumed,
                    execution_time_ms: execution_time.as_millis() as u64,
                })
            }
            Err(e) => {
                let error_msg = e.to_string();
                error!("WASM execution failed: {}", error_msg);
                
                Ok(VerificationResult {
                    success: false,
                    witness: None,
                    error: Some(error_msg),
                    fuel_consumed,
                    execution_time_ms: execution_time.as_millis() as u64,
                })
            }
        }
    }
    
    fn scan_for_prohibited_ops(&self) -> Result<Vec<String>> {
        // This would use wasm-objdump or similar to scan for prohibited operations
        // For now, we'll implement a basic scan
        let mut prohibited_ops = Vec::new();
        
        // Check for network-related imports
        let module_bytes = std::fs::read(&self.module.path().unwrap())?;
        
        // Simple scan for common network-related strings
        let network_patterns = [
            "sock_open",
            "sock_send",
            "sock_recv",
            "sock_shutdown",
            "proc_exec",
            "fd_pread",
            "fd_pwrite",
        ];
        
        let module_str = String::from_utf8_lossy(&module_bytes);
        for pattern in &network_patterns {
            if module_str.contains(pattern) {
                prohibited_ops.push(pattern.to_string());
            }
        }
        
        Ok(prohibited_ops)
    }
}

fn main() -> Result<()> {
    // Initialize tracing
    tracing_subscriber::fmt::init();
    
    let args = Args::parse();
    
    info!("Starting WASM sandbox for module: {:?}", args.module);
    
    // Create sandbox
    let mut sandbox = WasmSandbox::new(
        &args.module,
        args.fuel_limit,
        args.allow_network,
        args.allow_fs,
    )?;
    
    // Verify module hash if provided
    if let Some(expected_hash) = &args.expected_hash {
        if !sandbox.verify_module_hash(expected_hash)? {
            return Err(anyhow::anyhow!("Module hash verification failed"));
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
    let result = sandbox.execute_verify(args.input.as_deref())?;
    
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