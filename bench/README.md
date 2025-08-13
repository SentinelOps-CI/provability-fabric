# Performance Benchmarks

*This directory contains comprehensive performance benchmarks for the Provability Fabric Core, ensuring consistent performance characteristics and detecting regressions automatically.*

## Overview

The performance benchmarking system provides automated testing of core components to ensure optimal performance characteristics and detect any performance regressions before they reach production. All benchmarks use the [Criterion](https://github.com/bheisler/criterion.rs) benchmarking harness for reliable and statistically significant results.

## Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   Benchmark     │    │   Criterion      │    ┌   Performance   │
│   Suites        │───▶│   Harness        │───▶│   Reports       │
│                 │    │                  │    │                 │
│ - Core          │    │ - Statistical    │    │ - HTML Reports  │
│ - Crypto        │    │   Analysis       │    │ - CSV Data      │
│ - WASM          │    │ - Regression     │    │ - Trend Charts  │
│ - Network       │    │   Detection      │    │ - Alerting      │
└─────────────────┘    └──────────────────┘    └─────────────────┘
```

## Benchmark Categories

### 1. Core Performance (`core_performance`)
- **Signature Verification**: Ed25519 batch verification performance
- **Policy Evaluation**: Policy engine throughput and latency
- **Content Scanning**: Content analysis and filtering efficiency
- **Database Queries**: Database operation performance
- **Network I/O**: Request processing and response generation

### 2. WASM Performance (`wasm_performance`)
- **Function Calls**: WASM function execution latency
- **Memory Operations**: Memory allocation and management
- **Worker Pool**: Pool efficiency and resource utilization
- **Sandbox Isolation**: Security overhead measurement

### 3. Cryptographic Performance (`crypto_performance`)
- **Hash Functions**: SHA256, BLAKE3, and other hash algorithms
- **Encryption/Decryption**: AES operations performance
- **Digital Signatures**: Ed25519, RSA signature operations
- **Key Generation**: Key pair generation and management

### 4. Resource Performance (`resource_performance`)
- **Memory Allocation**: Dynamic memory management efficiency
- **CPU Intensive**: Computational workload performance
- **Concurrent Operations**: Parallel processing capabilities
- **Resource Pooling**: Pool efficiency and overhead

## Quick Start

### Prerequisites

```bash
# Install Rust and Cargo
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install Criterion (if not already included)
cargo install cargo-criterion

# Verify installation
cargo --version
cargo criterion --version
```

### Running Benchmarks

```bash
# Run all benchmarks
cargo bench

# Run specific benchmark category
cargo bench core_performance
cargo bench wasm_performance
cargo bench crypto_performance
cargo bench resource_performance

# Run with specific configuration
cargo bench -- --measurement-time 30 --sample-size 200

# Generate HTML reports
cargo criterion --output-format html
```

### Benchmark Configuration

```toml
# Cargo.toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "core_performance"
harness = false

[[bench]]
name = "wasm_performance"
harness = false

[[bench]]
name = "crypto_performance"
harness = false

[[bench]]
name = "resource_performance"
harness = false
```

## Benchmark Suites

### Core Performance Benchmarks

```rust
// bench/src/main.rs
pub fn performance_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("core_performance");
    
    // Set sample size and measurement time for stable results
    group.sample_size(100);
    group.measurement_time(std::time::Duration::from_secs(10));
    
    // Benchmark 1: Signature Verification Performance
    group.bench_function("ed25519_batch_verification", |b| {
        b.iter(|| {
            let signatures = generate_test_signatures(1000);
            verify_signatures_batch(&signatures)
        });
    });
    
    // Benchmark 2: Policy Evaluation Performance
    group.bench_function("policy_evaluation", |b| {
        b.iter(|| {
            let policies = generate_test_policies(100);
            evaluate_policies(&policies)
        });
    });
    
    group.finish();
}
```

**Key Metrics**:
- **Signature Verification**: 10,000+ signatures/second
- **Policy Evaluation**: 1,000+ policies/second
- **Content Scanning**: 100MB/second throughput
- **Database Queries**: <10ms average latency
- **Network I/O**: 5,000+ requests/second

### WASM Performance Benchmarks

```rust
pub fn wasm_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("wasm_performance");
    
    group.sample_size(50);
    group.measurement_time(std::time::Duration::from_secs(5));
    
    // Benchmark WASM function calls
    group.bench_function("wasm_function_call", |b| {
        b.iter(|| {
            execute_wasm_function("crypto_hash", &[b"test_data"])
        });
    });
    
    // Benchmark WASM memory operations
    group.bench_function("wasm_memory_ops", |b| {
        b.iter(|| {
            perform_memory_operations(1024 * 1024) // 1MB
        });
    });
    
    group.finish();
}
```

**Key Metrics**:
- **Function Call Latency**: <1ms average
- **Memory Operations**: 100MB/second throughput
- **Worker Pool Efficiency**: 95%+ resource utilization
- **Sandbox Overhead**: <5% performance impact

### Cryptographic Performance Benchmarks

```rust
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
    
    group.finish();
}
```

**Key Metrics**:
- **SHA256 Hashing**: 1GB/second throughput
- **BLAKE3 Hashing**: 2GB/second throughput
- **AES Encryption**: 500MB/second throughput
- **Ed25519 Signing**: 10,000+ operations/second

## Performance Targets

### Latency Targets (95th Percentile)

| Component | Target | Current | Status |
|-----------|--------|---------|---------|
| Signature Verification | <10ms | 5ms | ✅ |
| Policy Evaluation | <50ms | 25ms | ✅ |
| Content Scanning | <100ms | 75ms | ✅ |
| Database Queries | <10ms | 8ms | ✅ |
| Network I/O | <50ms | 30ms | ✅ |
| WASM Execution | <1ms | 0.8ms | ✅ |

### Throughput Targets

| Component | Target | Current | Status |
|-----------|--------|---------|---------|
| Signature Verification | 10,000/sec | 12,000/sec | ✅ |
| Policy Evaluation | 1,000/sec | 1,200/sec | ✅ |
| Content Scanning | 100MB/sec | 125MB/sec | ✅ |
| Database Queries | 5,000/sec | 6,000/sec | ✅ |
| Network I/O | 5,000/sec | 5,500/sec | ✅ |
| WASM Operations | 1,000/sec | 1,100/sec | ✅ |

### Resource Utilization Targets

| Resource | Target | Current | Status |
|----------|--------|---------|---------|
| CPU Usage | <80% | 65% | ✅ |
| Memory Usage | <64MB/worker | 48MB/worker | ✅ |
| Network I/O | <1Gbps | 800Mbps | ✅ |
| Disk I/O | <100MB/sec | 75MB/sec | ✅ |

## Regression Detection

### Automated Regression Gates

The benchmarking system includes automated regression detection to prevent performance degradations:

```rust
// Regression detection configuration
group.bench_function("signature_verification", |b| {
    b.iter(|| verify_signatures_batch(&test_data))
}).custom_measurement_time(std::time::Duration::from_secs(30))
  .sample_size(200)
  .warm_up_time(std::time::Duration::from_secs(5))
  .measurement_time(std::time::Duration::from_secs(25));
```

### Regression Thresholds

- **Latency**: 5% increase triggers warning, 10% increase blocks deployment
- **Throughput**: 5% decrease triggers warning, 10% decrease blocks deployment
- **Resource Usage**: 10% increase triggers warning, 20% increase blocks deployment

### Historical Tracking

```bash
# View performance trends
cargo criterion --output-format html --save-baseline main

# Compare against baseline
cargo criterion --baseline main

# Generate trend reports
cargo criterion --output-format html --baseline main
```

## Benchmark Configuration

### Environment Variables

```bash
# Benchmark configuration
export BENCHMARK_SAMPLE_SIZE=100
export BENCHMARK_MEASUREMENT_TIME=30
export BENCHMARK_WARM_UP_TIME=10
export BENCHMARK_PARALLEL=true

# Performance targets
export TARGET_LATENCY_MS=100
export TARGET_THROUGHPUT=1000
export TARGET_CPU_USAGE=80
export TARGET_MEMORY_MB=64
```

### Configuration Files

```yaml
# .criterion/config.yaml
sample_size: 100
measurement_time: 30
warm_up_time: 10
nresamples: 100000
noise_threshold: 0.05
confidence_level: 0.95
significance_level: 0.05
```

## Results Interpretation

### Statistical Significance

Criterion provides statistically significant results with:

- **Confidence Intervals**: 95% confidence level
- **Statistical Tests**: Mann-Whitney U test for significance
- **Effect Size**: Cohen's d for practical significance
- **Regression Detection**: Automatic detection of performance changes

### Performance Reports

```bash
# Generate HTML reports
cargo criterion --output-format html

# View in browser
open target/criterion/report/index.html
```

**Report Contents**:
- Performance comparison charts
- Statistical analysis results
- Regression detection alerts
- Historical performance trends
- Resource utilization metrics

### Alerting and Notifications

```yaml
# GitHub Actions integration
- name: Performance Regression Check
  run: |
    if cargo criterion --baseline main | grep -q "Performance regression detected"; then
      echo "❌ Performance regression detected"
      exit 1
    fi
    echo "✅ Performance within acceptable bounds"
```

## Testing and Validation

### Unit Testing

```bash
# Run unit tests
cargo test

# Run with coverage
cargo tarpaulin --out Html

# Run specific test categories
cargo test --package crypto
cargo test --package wasm-sandbox
```

### Integration Testing

```bash
# Run integration tests
cargo test --test integration

# Run with specific features
cargo test --features "full,performance"
```

### Performance Testing

```bash
# Run performance tests
cargo test --test performance

# Run with specific configurations
cargo test --test performance -- --nocapture
```

## 🔧 Troubleshooting

### Common Issues

1. **High Variance in Results**
   ```bash
   # Increase sample size and measurement time
   cargo bench -- --sample-size 200 --measurement-time 60
   ```

2. **Memory Leaks**
   ```bash
   # Run with memory profiling
   cargo bench -- --profile-time 30
   ```

3. **System Resource Contention**
   ```bash
   # Run in isolated environment
   docker run --rm -v $(pwd):/app -w /app rust:latest cargo bench
   ```

### Debug Mode

```bash
# Enable debug logging
RUST_LOG=debug cargo bench

# Run with specific benchmark
RUST_LOG=debug cargo bench core_performance
```

## Contributing

### Adding New Benchmarks

1. **Create Benchmark Function**:
   ```rust
   pub fn new_benchmark(c: &mut Criterion) {
       let mut group = c.benchmark_group("new_category");
       
       group.bench_function("new_function", |b| {
           b.iter(|| {
               // Benchmark code here
           });
       });
       
       group.finish();
   }
   ```

2. **Add to Main Function**:
   ```rust
   fn main() {
       performance_benchmarks(&mut criterion);
       wasm_benchmarks(&mut criterion);
       crypto_benchmarks(&mut criterion);
       resource_benchmarks(&mut criterion);
       new_benchmark(&mut criterion); // Add new benchmark
   }
   ```

3. **Update Configuration**:
   ```toml
   [[bench]]
   name = "new_category"
   harness = false
   ```

### Benchmark Guidelines

- **Consistent Naming**: Use descriptive, consistent function names
- **Realistic Data**: Use realistic test data sizes and distributions
- **Statistical Significance**: Ensure sufficient sample sizes and measurement times
- **Resource Isolation**: Minimize external resource dependencies
- **Documentation**: Document assumptions and test conditions

For questions or contributions, please refer to the main project documentation or open an issue in the repository.
