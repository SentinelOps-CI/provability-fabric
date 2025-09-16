// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::time::Instant;
use std::sync::Arc;
use tokio::runtime::Runtime;
use sidecar_watcher::{
    dfa::{OptimizedDFA, Event, EventKind, DFATable, Transition, RateLimit},
    ifc_labels::OptimizedIFCManager,
    ratelimit::{OptimizedRateLimiter, RateLimitConfig, BucketedRateLimiter},
    crypto::{AsyncSigningPipeline, SigningWorkerConfig, CertCore, SigningRequest},
    concurrency::{LockFreeRingBuffer, EpochPolicyManager, EventIngress},
};
use ed25519_dalek::{SigningKey, Signer};
use rand::rngs::OsRng;

/// Performance benchmarks for Provability Fabric Core
pub fn performance_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("hot_path_performance");
    
    // Set sample size and measurement time for stable results
    group.sample_size(1000);
    group.measurement_time(std::time::Duration::from_secs(30));
    
    // Benchmark 1: Optimized DFA Hot Path
    group.bench_function("dfa_hot_path_step", |b| {
        let table = create_test_dfa_table();
        let dfa = OptimizedDFA::from_table(table).unwrap();
        let event = Event::new(EventKind::Call, 1, 0, "tool1".to_string());
        
        b.iter(|| {
            black_box(dfa.step(0, &event))
        });
    });
    
    // Benchmark 2: IFC Fast Path Operations
    group.bench_function("ifc_declassify_operation", |b| {
        let mut manager = OptimizedIFCManager::new().unwrap();
        let secret_id = manager.get_label("secret").unwrap().id;
        let internal_id = manager.get_label("internal").unwrap().id;
        
        b.iter(|| {
            black_box(manager.declassify(secret_id, internal_id, 0))
        });
    });
    
    // Benchmark 3: Optimized Rate Limiting
    group.bench_function("rate_limit_check", |b| {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 10000,
            epsilon_ms: 10,
        };
        let limiter = OptimizedRateLimiter::new(config);
        let current_time = 1000;
        
        b.iter(|| {
            black_box(limiter.check(current_time))
        });
    });
    
    // Benchmark 4: Lock-Free Ring Buffer Operations
    group.bench_function("ring_buffer_push_pop", |b| {
        let buffer = LockFreeRingBuffer::new(1024);
        
        b.iter(|| {
            let _ = black_box(buffer.push(42));
            let _ = black_box(buffer.pop());
        });
    });
    
    // Benchmark 5: ArcSwap Policy Updates
    group.bench_function("arcswap_policy_update", |b| {
        let manager = EpochPolicyManager::new("initial".to_string());
        
        b.iter(|| {
            black_box(manager.update_policy("updated".to_string()))
        });
    });
    
    group.finish();
}

/// Sub-millisecond performance benchmarks
pub fn sub_millisecond_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("sub_millisecond_performance");
    
    group.sample_size(10000);
    group.measurement_time(std::time::Duration::from_secs(60));
    
    // Benchmark 1: DFA Step Performance (target: <100μs)
    group.bench_function("dfa_step_100k_ops", |b| {
        let table = create_test_dfa_table();
        let dfa = OptimizedDFA::from_table(table).unwrap();
        let event = Event::new(EventKind::Call, 1, 0, "tool1".to_string());
        
        b.iter(|| {
            for _ in 0..100_000 {
                black_box(dfa.step(0, &event));
            }
        });
    });
    
    // Benchmark 2: IFC Bitset Operations (target: <50μs)
    group.bench_function("ifc_bitset_operations", |b| {
        let mut manager = OptimizedIFCManager::new().unwrap();
        let secret_id = manager.get_label("secret").unwrap().id;
        let internal_id = manager.get_label("internal").unwrap().id;
        let required_labels = vec![secret_id];
        
        // Pre-declassify
        manager.declassify(secret_id, internal_id, 0);
        
        b.iter(|| {
            for _ in 0..100_000 {
                black_box(manager.is_output_allowed(internal_id, 0, &required_labels));
            }
        });
    });
    
    // Benchmark 3: Rate Limiting Hot Path (target: <10μs)
    group.bench_function("rate_limit_hot_path", |b| {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 10000,
            epsilon_ms: 10,
        };
        let limiter = OptimizedRateLimiter::new(config);
        let current_time = 1000;
        
        b.iter(|| {
            for _ in 0..100_000 {
                black_box(limiter.check(current_time));
            }
        });
    });
    
    // Benchmark 4: Ring Buffer High Throughput (target: <5μs)
    group.bench_function("ring_buffer_high_throughput", |b| {
        let buffer = LockFreeRingBuffer::new(10000);
        
        b.iter(|| {
            for i in 0..100_000 {
                let _ = black_box(buffer.push(i));
                if i % 2 == 0 {
                    let _ = black_box(buffer.pop());
                }
            }
        });
    });
    
    // Benchmark 5: Async Signing Pipeline (target: <1ms per 1000 ops)
    group.bench_function("async_signing_pipeline", |b| {
        let config = SigningWorkerConfig {
            max_queue_size: 10000,
            worker_count: 4,
            batch_size: 32,
            batch_timeout: std::time::Duration::from_millis(1),
            backpressure_threshold: 8000,
        };
        
        let mut pipeline = AsyncSigningPipeline::new(config);
        let mut rng = OsRng;
        let signing_key = SigningKey::generate(&mut rng);
        
        b.iter(|| {
            let rt = Runtime::new().unwrap();
            rt.block_on(async {
                for i in 0..1000 {
                    let cert_core = CertCore {
                        content_hash: [i as u8; 32],
                        timestamp: 1000 + i,
                        issuer: format!("issuer_{}", i),
                        subject: format!("subject_{}", i),
                        request_id: format!("request_{}", i),
                    };
                    
                    let request = SigningRequest {
                        cert_core,
                        signing_key: signing_key.clone(),
                        priority: 0,
                    };
                    
                    let _ = pipeline.submit_request(request).await;
                }
                
                // Collect results
                for _ in 0..1000 {
                    let _ = pipeline.get_result().await;
                }
            });
        });
    });
    
    group.finish();
}

/// Memory efficiency benchmarks
pub fn memory_efficiency_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_efficiency");
    
    group.sample_size(100);
    group.measurement_time(std::time::Duration::from_secs(30));
    
    // Benchmark 1: DFA Memory Layout
    group.bench_function("dfa_memory_layout", |b| {
        let table = create_large_dfa_table();
        let dfa = OptimizedDFA::from_table(table).unwrap();
        
        b.iter(|| {
            let event = Event::new(EventKind::Call, 1, 0, "tool1".to_string());
            for _ in 0..1000 {
                black_box(dfa.step(0, &event));
            }
        });
    });
    
    // Benchmark 2: IFC Bitset Memory Usage
    group.bench_function("ifc_bitset_memory", |b| {
        let mut manager = OptimizedIFCManager::new().unwrap();
        
        b.iter(|| {
            for i in 0..1000 {
                let label_id = manager.add_label(
                    format!("label_{}", i),
                    i % 10,
                    vec!["category".to_string()],
                    "tenant".to_string(),
                );
                manager.declassify(label_id, 0, 0);
            }
        });
    });
    
    // Benchmark 3: Ring Buffer Memory Efficiency
    group.bench_function("ring_buffer_memory", |b| {
        let buffer = LockFreeRingBuffer::new(10000);
        
        b.iter(|| {
            for i in 0..10000 {
                let _ = black_box(buffer.push(i));
                if i % 2 == 0 {
                    let _ = black_box(buffer.pop());
                }
            }
        });
    });
    
    group.finish();
}

/// Concurrency performance benchmarks
pub fn concurrency_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrency_performance");
    
    group.sample_size(100);
    group.measurement_time(std::time::Duration::from_secs(30));
    
    // Benchmark 1: Multi-threaded DFA Processing
    group.bench_function("multithreaded_dfa", |b| {
        let table = create_test_dfa_table();
        let dfa = Arc::new(OptimizedDFA::from_table(table).unwrap());
        
        b.iter(|| {
            let handles: Vec<_> = (0..4)
                .map(|thread_id| {
                    let dfa = Arc::clone(&dfa);
                    std::thread::spawn(move || {
                        let event = Event::new(EventKind::Call, thread_id as u16, 0, "tool1".to_string());
                        for _ in 0..25000 {
                            black_box(dfa.step(0, &event));
                        }
                    })
                })
                .collect();
            
            for handle in handles {
                handle.join().unwrap();
            }
        });
    });
    
    // Benchmark 2: Concurrent Rate Limiting
    group.bench_function("concurrent_rate_limiting", |b| {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 10000,
            epsilon_ms: 10,
        };
        let limiter = Arc::new(OptimizedRateLimiter::new(config));
        
        b.iter(|| {
            let handles: Vec<_> = (0..4)
                .map(|_| {
                    let limiter = Arc::clone(&limiter);
                    std::thread::spawn(move || {
                        for i in 0..25000 {
                            black_box(limiter.check(1000 + i));
                        }
                    })
                })
                .collect();
            
            for handle in handles {
                handle.join().unwrap();
            }
        });
    });
    
    // Benchmark 3: Lock-Free Ring Buffer Concurrency
    group.bench_function("concurrent_ring_buffer", |b| {
        let buffer = Arc::new(LockFreeRingBuffer::new(10000));
        
        b.iter(|| {
            let producer_handles: Vec<_> = (0..2)
                .map(|thread_id| {
                    let buffer = Arc::clone(&buffer);
                    std::thread::spawn(move || {
                        for i in 0..25000 {
                            while buffer.push(thread_id * 25000 + i).is_err() {
                                std::thread::yield_now();
                            }
                        }
                    })
                })
                .collect();
            
            let consumer_handles: Vec<_> = (0..2)
                .map(|_| {
                    let buffer = Arc::clone(&buffer);
                    std::thread::spawn(move || {
                        let mut count = 0;
                        while count < 25000 {
                            if let Some(_) = buffer.pop() {
                                count += 1;
                            } else {
                                std::thread::yield_now();
                            }
                        }
                    })
                })
                .collect();
            
            for handle in producer_handles {
                handle.join().unwrap();
            }
            for handle in consumer_handles {
                handle.join().unwrap();
            }
        });
    });
    
    group.finish();
}

/// Helper function to create test DFA table
fn create_test_dfa_table() -> DFATable {
    DFATable {
        states: vec![0, 1, 2, 3, 4, 5],
        start: 0,
        accepting: vec![0, 1, 2, 3, 4, 5],
        transitions: vec![
            Transition {
                from_state: 0,
                event: "call(tool1,1)".to_string(),
                to_state: 1,
            },
            Transition {
                from_state: 1,
                event: "emit(plan1)".to_string(),
                to_state: 2,
            },
            Transition {
                from_state: 2,
                event: "log(hash1)".to_string(),
                to_state: 3,
            },
        ],
        rate_limits: vec![
            RateLimit {
                tool: "tool1".to_string(),
                window_ms: 1000,
                bound: 100,
            },
        ],
    }
}

/// Helper function to create large DFA table for memory benchmarks
fn create_large_dfa_table() -> DFATable {
    let mut states = Vec::new();
    let mut transitions = Vec::new();
    
    // Create 100 states
    for i in 0..100 {
        states.push(i);
    }
    
    // Create transitions between states
    for i in 0..99 {
        transitions.push(Transition {
            from_state: i,
            event: format!("call(tool{},1)", i),
            to_state: i + 1,
        });
    }
    
    DFATable {
        states,
        start: 0,
        accepting: vec![99],
        transitions,
        rate_limits: vec![],
    }
}
    
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
    sub_millisecond_benchmarks,
    memory_efficiency_benchmarks,
    concurrency_benchmarks,
    wasm_benchmarks,
    crypto_benchmarks,
    resource_benchmarks,
    detect_performance_regressions
);

criterion_main!(benches);
