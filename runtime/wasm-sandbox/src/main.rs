// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{ensure, Context, Result};
use clap::Parser;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::Instant;
use wasmtime::{Config, Engine, Instance, Module, Store, StoreLimits, StoreLimitsBuilder};

const MAX_MODULE_BYTES: u64 = 16 * 1024 * 1024;
const MAX_LINEAR_MEMORY_BYTES: usize = 64 * 1024 * 1024;
const MAX_TABLE_ELEMENTS: usize = 10_000;

#[derive(Parser)]
#[command(name = "wasm-sandbox")]
#[command(about = "Execute an import-free core WebAssembly command")]
struct Args {
    /// Path to a binary WebAssembly module exporting _start: () -> ().
    #[arg(short, long)]
    module: PathBuf,

    /// Expected SHA256 digest of the exact bytes to execute.
    #[arg(short, long)]
    expected_hash: Option<String>,

    /// Fuel budget, including module instantiation and entrypoint execution.
    #[arg(short, long, default_value = "1000000")]
    fuel_limit: u64,

    /// Reserved; rejected because host network capabilities are unsupported.
    #[arg(long)]
    allow_network: bool,

    /// Reserved; rejected because host filesystem capabilities are unsupported.
    #[arg(long)]
    allow_fs: bool,

    /// Reserved; rejected until a guest input ABI is implemented.
    #[arg(short, long)]
    input: Option<String>,
}

#[derive(Debug, Serialize)]
struct ExecutionResult {
    success: bool,
    witness: Option<serde_json::Value>,
    error: Option<String>,
    fuel_consumed: u64,
    execution_time_ms: u64,
}

fn read_module(path: &Path) -> Result<Vec<u8>> {
    let file = File::open(path).context("open WebAssembly module")?;
    ensure!(file.metadata()?.is_file(), "module must be a regular file");
    let mut bytes = Vec::new();
    file.take(MAX_MODULE_BYTES + 1).read_to_end(&mut bytes)?;
    ensure!(bytes.len() as u64 <= MAX_MODULE_BYTES, "module exceeds size limit");
    Ok(bytes)
}

fn validate_request(args: &Args) -> Result<()> {
    ensure!(args.fuel_limit > 0, "fuel limit must be positive");
    ensure!(!args.allow_fs, "host filesystem access is unsupported");
    ensure!(!args.allow_network, "host network access is unsupported");
    ensure!(args.input.is_none(), "guest input ABI is unsupported");
    Ok(())
}

fn verify_bytes(bytes: &[u8], expected: Option<&str>) -> Result<()> {
    ensure!(bytes.len() as u64 <= MAX_MODULE_BYTES, "module exceeds size limit");
    ensure!(bytes.starts_with(b"\0asm\x01\0\0\0"), "expected a binary core WebAssembly module");
    if let Some(expected) = expected {
        let actual = hex::encode(Sha256::digest(bytes));
        ensure!(expected == actual, "module SHA256 mismatch");
    }
    Ok(())
}

fn engine() -> Result<Engine> {
    let mut config = Config::new();
    config.consume_fuel(true);
    Engine::new(&config)
}

fn execute(engine: &Engine, module: &Module, fuel: u64) -> Result<ExecutionResult> {
    ensure!(fuel > 0, "fuel limit must be positive");
    // No WASI or host functions are linked, including during instantiation.
    ensure!(module.imports().next().is_none(), "guest imports are unsupported");
    let limits = StoreLimitsBuilder::new()
        .memory_size(MAX_LINEAR_MEMORY_BYTES)
        .table_elements(MAX_TABLE_ELEMENTS)
        .instances(1)
        .memories(1)
        .tables(1)
        .trap_on_grow_failure(true)
        .build();
    let mut store = Store::new(engine, limits);
    store.limiter(|limits: &mut StoreLimits| limits);
    store.set_fuel(fuel)?;

    let start = Instant::now();
    let outcome = (|| -> Result<()> {
        let instance = Instance::new(&mut store, module, &[]).context("instantiate guest")?;
        let entry = instance
            .get_typed_func::<(), ()>(&mut store, "_start")
            .context("guest must export _start: () -> ()")?;
        entry.call(&mut store, ()).context("guest execution failed")?;
        Ok(())
    })();
    let consumed = fuel.checked_sub(store.get_fuel()?).context("invalid fuel accounting")?;
    Ok(ExecutionResult {
        success: outcome.is_ok(),
        // A successful return is execution evidence, not a proof witness.
        witness: None,
        error: outcome.err().map(|error| format!("{error:#}")),
        fuel_consumed: consumed,
        execution_time_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
    })
}

fn main() -> Result<()> {
    let args = Args::parse();
    validate_request(&args)?;
    // Hash and compile the same immutable byte buffer; do not reopen the path.
    let bytes = read_module(&args.module)?;
    verify_bytes(&bytes, args.expected_hash.as_deref())?;
    let engine = engine()?;
    let module = Module::from_binary(&engine, &bytes).context("compile guest")?;
    let result = execute(&engine, &module, args.fuel_limit)?;
    println!("{}", serde_json::to_string_pretty(&result)?);
    if !result.success {
        std::process::exit(1);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(wat: &str, fuel: u64) -> Result<ExecutionResult> {
        let engine = engine()?;
        let module = Module::new(&engine, wat)?;
        execute(&engine, &module, fuel)
    }

    #[test]
    fn real_entrypoint_executes_and_reports_fuel() {
        let result = run("(module (func (export \"_start\") nop))", 1000).unwrap();
        assert!(result.success);
        assert!(result.fuel_consumed > 0 && result.fuel_consumed <= 1000);
        assert!(result.witness.is_none());
        assert!(result.error.is_none());
    }

    #[test]
    fn guest_trap_is_not_reported_as_success() {
        let result = run("(module (func (export \"_start\") unreachable))", 1000).unwrap();
        assert!(!result.success);
        assert!(result.error.is_some());
        assert!(result.witness.is_none());
    }

    #[test]
    fn entrypoint_fuel_exhaustion_fails() {
        let result = run("(module (func (export \"_start\") (loop br 0)))", 100).unwrap();
        assert!(!result.success);
        assert!(result.fuel_consumed <= 100);
    }

    #[test]
    fn instantiation_fuel_exhaustion_fails() {
        let result = run("(module (func $init (loop br 0)) (start $init) (func (export \"_start\")))", 100).unwrap();
        assert!(!result.success);
        assert!(result.fuel_consumed <= 100);
    }

    #[test]
    fn all_guest_imports_are_rejected() {
        for import in ["wasi_snapshot_preview1", "env", "unknown"] {
            let wat = format!("(module (import \"{import}\" \"f\" (func)) (func (export \"_start\")))");
            assert!(run(&wat, 1000).is_err());
        }
    }

    #[test]
    fn missing_and_wrong_entrypoints_fail() {
        for wat in ["(module)", "(module (func (export \"_start\") (param i32)))"] {
            assert!(!run(wat, 1000).unwrap().success);
        }
    }

    #[test]
    fn memory_limits_apply_at_instantiation_and_growth() {
        assert!(!run("(module (memory 1025) (func (export \"_start\")))", 1000).unwrap().success);
        assert!(!run("(module (memory 1) (func (export \"_start\") i32.const 1024 memory.grow drop))", 100_000).unwrap().success);
    }

    #[test]
    fn binary_and_hash_validation_bind_the_exact_bytes() {
        let bytes = b"\0asm\x01\0\0\0";
        let digest = hex::encode(Sha256::digest(bytes));
        assert!(verify_bytes(bytes, Some(&digest)).is_ok());
        assert!(verify_bytes(bytes, Some("incorrect")).is_err());
        assert!(verify_bytes(b"(module)", None).is_err());
    }

    #[test]
    fn unsupported_capabilities_and_input_fail_closed() {
        let mut args = Args {
            module: PathBuf::from("unused.wasm"),
            expected_hash: None,
            fuel_limit: 1000,
            allow_network: false,
            allow_fs: false,
            input: None,
        };
        assert!(validate_request(&args).is_ok());
        args.allow_network = true;
        assert!(validate_request(&args).is_err());
        args.allow_network = false;
        args.allow_fs = true;
        assert!(validate_request(&args).is_err());
        args.allow_fs = false;
        args.input = Some("{}".into());
        assert!(validate_request(&args).is_err());
        args.input = None;
        args.fuel_limit = 0;
        assert!(validate_request(&args).is_err());
    }
}
