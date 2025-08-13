// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Instant;
use tokio::runtime::Runtime;

/// Performance benchmarks for Provability Fabric Core
pub fn performance_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("core_performance");
    
    // Set sample size and measurement time for stable results
    group.sample_size(100);
    group.measurement_time(std::time::Duration::from_secs(10));
    
    // Benchmark 1: Signature Verification Performance
    group.bench_function("ed25519_batch_verification", |b| {
        b.iter(|| {
            // Simulate batch signature verification
            let signatures = generate_test_signatures(1000);
            verify_signatures_batch(&signatures)
        });
    });
    
    // Benchmark 2: Policy Evaluation Performance
    group.bench_function("policy_evaluation", |b| {
        b.iter(|| {
            // Simulate policy evaluation
            let policies = generate_test_policies(100);
            evaluate_policies(&policies)
        });
    });
    
    // Benchmark 3: Content Scanning Performance
    group.bench_function("content_scanning", |b| {
        b.iter(|| {
            // Simulate content scanning
            let content = generate_test_content(1024 * 1024); // 1MB
            scan_content(&content)
        });
    });
    
    // Benchmark 4: Database Query Performance
    group.bench_function("database_queries", |b| {
        b.iter(|| {
            // Simulate database operations
            let queries = generate_test_queries(100);
            execute_queries(&queries)
        });
    });
    
    // Benchmark 5: Network I/O Performance
    group.bench_function("network_io", |b| {
        b.iter(|| {
            // Simulate network operations
            let requests = generate_test_requests(50);
            process_requests(&requests)
        });
    });
    
    group.finish();
}

/// Benchmark WASM operations
pub fn wasm_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("wasm_performance");
    
    group.sample_size(50);
    group.measurement_time(std::time::Duration::from_secs(5));
    
    // Benchmark WASM function calls
    group.bench_function("wasm_function_call", |b| {
        b.iter(|| {
            // Simulate WASM function execution
            execute_wasm_function("crypto_hash", &[b"test_data"])
        });
    });
    
    // Benchmark WASM memory operations
    group.bench_function("wasm_memory_ops", |b| {
        b.iter(|| {
            // Simulate WASM memory operations
            perform_memory_operations(1024 * 1024) // 1MB
        });
    });
    
    group.finish();
}

/// Benchmark cryptographic operations
pub fn crypto_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("crypto_performance");
    
    group.sample_size(200);
    group.measurement_time(std::time::Duration::from_secs(15));
    
    // Benchmark different hash algorithms
    group.bench_function("sha256_hashing", |b| {
        b.iter(|| {
            let data = black_box(b"test_data_for_hashing");
            sha256_hash(data)
        });
    });
    
    group.bench_function("blake3_hashing", |b| {
        b.iter(|| {
            let data = black_box(b"test_data_for_hashing");
            blake3_hash(data)
        });
    });
    
    // Benchmark encryption/decryption
    group.bench_function("aes_encryption", |b| {
        b.iter(|| {
            let data = black_box(b"test_data_for_encryption");
            aes_encrypt(data)
        });
    });
    
    group.bench_function("aes_decryption", |b| {
        b.iter(|| {
            let data = black_box(b"encrypted_test_data");
            aes_decrypt(data)
        });
    });
    
    group.finish();
}

/// Benchmark memory and CPU operations
pub fn resource_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("resource_performance");
    
    group.sample_size(100);
    group.measurement_time(std::time::Duration::from_secs(10));
    
    // Benchmark memory allocation
    group.bench_function("memory_allocation", |b| {
        b.iter(|| {
            allocate_memory(1024 * 1024) // 1MB
        });
    });
    
    // Benchmark CPU-intensive operations
    group.bench_function("cpu_intensive", |b| {
        b.iter(|| {
            perform_cpu_intensive_work(1000)
        });
    });
    
    // Benchmark concurrent operations
    group.bench_function("concurrent_ops", |b| {
        b.iter(|| {
            let runtime = Runtime::new().unwrap();
            runtime.block_on(async {
                perform_concurrent_operations(100).await
            })
        });
    });
    
    group.finish();
}

// Helper functions for benchmarks

fn generate_test_signatures(count: usize) -> Vec<Vec<u8>> {
    (0..count).map(|i| {
        format!("signature_{}", i).into_bytes()
    }).collect()
}

fn verify_signatures_batch(signatures: &[Vec<u8>]) -> usize {
    let start = Instant::now();
    let mut valid_count = 0;
    
    for signature in signatures {
        // Simulate signature verification
        if signature.len() > 0 {
            valid_count += 1;
        }
    }
    
    let duration = start.elapsed();
    if duration.as_millis() > 100 {
        // Log slow operations
        println!("Batch verification took: {:?}", duration);
    }
    
    valid_count
}

fn generate_test_policies(count: usize) -> Vec<String> {
    (0..count).map(|i| {
        format!("policy_{}: allow if user.role == 'admin'", i)
    }).collect()
}

fn evaluate_policies(policies: &[String]) -> usize {
    let start = Instant::now();
    let mut allowed_count = 0;
    
    for policy in policies {
        // Simulate policy evaluation
        if policy.contains("admin") {
            allowed_count += 1;
        }
    }
    
    let duration = start.elapsed();
    if duration.as_millis() > 50 {
        println!("Policy evaluation took: {:?}", duration);
    }
    
    allowed_count
}

fn generate_test_content(size: usize) -> Vec<u8> {
    (0..size).map(|i| (i % 256) as u8).collect()
}

fn scan_content(content: &[u8]) -> bool {
    let start = Instant::now();
    
    // Simulate content scanning
    let has_sensitive_data = content.windows(4)
        .any(|window| window == b"PASS" || window == b"SSN");
    
    let duration = start.elapsed();
    if duration.as_millis() > 100 {
        println!("Content scanning took: {:?}", duration);
    }
    
    !has_sensitive_data
}

fn generate_test_queries(count: usize) -> Vec<String> {
    (0..count).map(|i| {
        format!("SELECT * FROM users WHERE id = {}", i)
    }).collect()
}

fn execute_queries(queries: &[String]) -> usize {
    let start = Instant::now();
    let mut result_count = 0;
    
    for query in queries {
        // Simulate query execution
        if query.contains("SELECT") {
            result_count += 1;
        }
    }
    
    let duration = start.elapsed();
    if duration.as_millis() > 200 {
        println!("Query execution took: {:?}", duration);
    }
    
    result_count
}

fn generate_test_requests(count: usize) -> Vec<Vec<u8>> {
    (0..count).map(|i| {
        format!("request_data_{}", i).into_bytes()
    }).collect()
}

fn process_requests(requests: &[Vec<u8>]) -> usize {
    let start = Instant::now();
    let mut processed_count = 0;
    
    for request in requests {
        // Simulate request processing
        if request.len() > 0 {
            processed_count += 1;
        }
    }
    
    let duration = start.elapsed();
    if duration.as_millis() > 50 {
        println!("Request processing took: {:?}", duration);
    }
    
    processed_count
}

fn execute_wasm_function(function_name: &str, params: &[&[u8]]) -> Vec<u8> {
    let start = Instant::now();
    
    // Simulate WASM function execution
    let result = format!("{}_{}", function_name, params.len()).into_bytes();
    
    let duration = start.elapsed();
    if duration.as_millis() > 10 {
        println!("WASM execution took: {:?}", duration);
    }
    
    result
}

fn perform_memory_operations(size: usize) -> usize {
    let start = Instant::now();
    
    // Simulate memory operations
    let mut data = vec![0u8; size];
    for i in 0..size {
        data[i] = (i % 256) as u8;
    }
    
    let duration = start.elapsed();
    if duration.as_millis() > 100 {
        println!("Memory operations took: {:?}", duration);
    }
    
    data.len()
}

fn sha256_hash(data: &[u8]) -> Vec<u8> {
    let start = Instant::now();
    
    // Simulate SHA256 hashing
    let hash = format!("sha256_{}", data.len()).into_bytes();
    
    let duration = start.elapsed();
    if duration.as_millis() > 5 {
        println!("SHA256 hashing took: {:?}", duration);
    }
    
    hash
}

fn blake3_hash(data: &[u8]) -> Vec<u8> {
    let start = Instant::now();
    
    // Simulate BLAKE3 hashing
    let hash = format!("blake3_{}", data.len()).into_bytes();
    
    let duration = start.elapsed();
    if duration.as_millis() > 3 {
        println!("BLAKE3 hashing took: {:?}", duration);
    }
    
    hash
}

fn aes_encrypt(data: &[u8]) -> Vec<u8> {
    let start = Instant::now();
    
    // Simulate AES encryption
    let encrypted = format!("encrypted_{}", data.len()).into_bytes();
    
    let duration = start.elapsed();
    if duration.as_millis() > 10 {
        println!("AES encryption took: {:?}", duration);
    }
    
    encrypted
}

fn aes_decrypt(data: &[u8]) -> Vec<u8> {
    let start = Instant::now();
    
    // Simulate AES decryption
    let decrypted = format!("decrypted_{}", data.len()).into_bytes();
    
    let duration = start.elapsed();
    if duration.as_millis() > 10 {
        println!("AES decryption took: {:?}", duration);
    }
    
    decrypted
}

fn allocate_memory(size: usize) -> Vec<u8> {
    let start = Instant::now();
    
    // Allocate memory
    let data = vec![0u8; size];
    
    let duration = start.elapsed();
    if duration.as_millis() > 50 {
        println!("Memory allocation took: {:?}", duration);
    }
    
    data
}

fn perform_cpu_intensive_work(iterations: usize) -> usize {
    let start = Instant::now();
    
    // Simulate CPU-intensive work
    let mut result = 0;
    for i in 0..iterations {
        result += i * i;
    }
    
    let duration = start.elapsed();
    if duration.as_millis() > 100 {
        println!("CPU-intensive work took: {:?}", duration);
    }
    
    result
}

async fn perform_concurrent_operations(count: usize) -> usize {
    let start = Instant::now();
    
    // Simulate concurrent operations
    let handles: Vec<_> = (0..count)
        .map(|i| tokio::spawn(async move {
            // Simulate async work
            tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
            i
        }))
        .collect();
    
    let results: Vec<_> = futures::future::join_all(handles).await;
    let sum: usize = results.into_iter()
        .filter_map(|r| r.ok())
        .sum();
    
    let duration = start.elapsed();
    if duration.as_millis() > 200 {
        println!("Concurrent operations took: {:?}", duration);
    }
    
    sum
}

// Performance regression detection
pub fn detect_performance_regressions(c: &mut Criterion) {
    let mut group = c.benchmark_group("regression_detection");
    
    group.sample_size(1000);
    group.measurement_time(std::time::Duration::from_secs(30));
    
    // Critical path benchmarks
    group.bench_function("critical_path_throughput", |b| {
        b.iter(|| {
            // Simulate critical path execution
            execute_critical_path()
        });
    });
    
    group.bench_function("memory_efficiency", |b| {
        b.iter(|| {
            // Simulate memory usage patterns
            measure_memory_efficiency()
        });
    });
    
    group.finish();
}

fn execute_critical_path() -> bool {
    let start = Instant::now();
    
    // Simulate critical path execution
    let mut result = true;
    for i in 0..1000 {
        if i % 2 == 0 {
            result = result && true;
        } else {
            result = result && false;
        }
    }
    
    let duration = start.elapsed();
    if duration.as_millis() > 10 {
        println!("Critical path execution took: {:?}", duration);
    }
    
    result
}

fn measure_memory_efficiency() -> usize {
    let start = Instant::now();
    
    // Simulate memory measurement
    let data = vec![0u8; 1024];
    let size = data.len();
    
    let duration = start.elapsed();
    if duration.as_millis() > 5 {
        println!("Memory measurement took: {:?}", duration);
    }
    
    size
}

criterion_group!(
    benches,
    performance_benchmarks,
    wasm_benchmarks,
    crypto_benchmarks,
    resource_benchmarks,
    detect_performance_regressions
);

criterion_main!(benches);
