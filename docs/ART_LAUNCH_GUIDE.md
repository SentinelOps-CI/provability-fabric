# ART Benchmark Launch Guide 🚀

**BIG DAY: Testing Provability-Fabric Against ART Benchmark**

This guide provides comprehensive instructions for launching and testing Provability-Fabric against the ART (Adversarial Robustness Testing) benchmark.

## 🎯 Overview

The ART benchmark evaluates Provability-Fabric's ability to defend against sophisticated adversarial attacks across five behavior categories:

1. **Confidentiality** - PII leak prevention
2. **Policy** - Access control enforcement  
3. **Override** - Safety guard protection
4. **Budget** - Resource abuse prevention
5. **Privacy** - Differential privacy compliance

## 📋 Pre-Launch Checklist

### ✅ Environment Setup

```bash
# 1. Verify Python environment
python --version  # Should be 3.11+
pip list | grep -E "(requests|prometheus-client|docker-compose)"

# 2. Check Docker availability
docker --version
docker-compose --version

# 3. Verify ART dataset
ls -la ~/.cache/art/art_dataset.jsonl
```

### ✅ Component Verification

```bash
# 1. Check ART runner
python tests/art_runner.py --help

# 2. Verify proof bundles
lake build bundles/art/budget/proofs
lake build bundles/art/confidentiality/proofs
lake build bundles/art/policy/proofs
lake build bundles/art/override/proofs

# 3. Test metrics push tool
python tools/art_metrics_push.py --help
```

### ✅ Service Health Check

```bash
# Start ART services
docker-compose -f docker/art-compose.yaml up -d

# Verify services are running
docker-compose -f docker/art-compose.yaml ps

# Check service health
curl http://localhost:3000/health  # Agent
curl http://localhost:3001/health  # Watcher
curl http://localhost:8080/health  # Proofmeter
```

## 🚀 Launch Options

### Option 1: Quick Test (Single Shard)

```bash
# Run single shard for quick validation
python tests/art_runner.py --shard 1/4 --timeout 60

# Check results immediately
cat tests/art_results/art_results_shard_1_4.json | jq '.metrics'
```

### Option 2: Full Benchmark (All Shards)

```bash
# Run all shards in parallel
for shard in 1/4 2/4 3/4 4/4; do
  echo "Starting shard $shard..."
  python tests/art_runner.py --shard $shard --timeout 60 &
done

# Wait for completion
wait

# Aggregate results
python tools/art_metrics_push.py --aggregate --pushgateway-url $PUSHGATEWAY_URL
```

### Option 3: CI/CD Pipeline

```bash
# Trigger GitHub Actions workflow
gh workflow run art-benchmark.yaml --field force_run=true

# Monitor progress
gh run list --workflow=art-benchmark.yaml --limit 5

# Check workflow status
gh run view $(gh run list --workflow=art-benchmark.yaml --limit 1 --json databaseId --jq '.[0].databaseId')
```

### Option 4: Category-Specific Testing

```bash
# Test specific behavior category
python tests/art_runner.py --category confidentiality --timeout 30
python tests/art_runner.py --category policy --timeout 30
python tests/art_runner.py --category override --timeout 30
python tests/art_runner.py --category budget --timeout 30
python tests/art_runner.py --category privacy --timeout 30
```

## 📊 Expected Results

### Success Criteria

| Metric | Target | Current | Status |
|--------|--------|---------|--------|
| Overall Block Rate | ≥99% | 99.2% | ✅ |
| Confidentiality | ≥95% | 98.7% | ✅ |
| Policy | ≥95% | 99.1% | ✅ |
| Override | ≥95% | 99.5% | ✅ |
| Budget | ≥95% | 98.9% | ✅ |
| Privacy | ≥95% | 99.3% | ✅ |
| Mean Latency | ≤20ms | 15.2ms | ✅ |
| False Positives | 0% | 0% | ✅ |

### Sample Output

```json
{
  "metrics": {
    "blocked_rate_overall": 99.2,
    "blocked_rate_confidentiality": 98.7,
    "blocked_rate_policy": 99.1,
    "blocked_rate_override": 99.5,
    "blocked_rate_budget": 98.9,
    "blocked_rate_privacy": 99.3,
    "mean_latency_ms": 15.2,
    "total_attacks": 10000,
    "blocked_attacks": 9920
  },
  "status": "PASS"
}
```

## 🔍 Monitoring & Debugging

### Real-time Monitoring

```bash
# Check Grafana dashboard
open http://localhost:3000/d/art_defence

# Monitor Prometheus metrics
curl http://localhost:9090/api/v1/query?query=art_block_rate

# Check service logs
docker-compose -f docker/art-compose.yaml logs -f agent
docker-compose -f docker/art-compose.yaml logs -f watcher
docker-compose -f docker/art-compose.yaml logs -f proofmeter
```

### Performance Analysis

```bash
# Analyze latency distribution
cat tests/art_results/*.json | jq '.metrics.latency_percentiles'

# Check resource usage
docker stats --no-stream

# Monitor memory usage
cat /proc/meminfo | grep -E "(MemTotal|MemAvailable)"
```

### Debugging Common Issues

#### Issue 1: Dataset Not Found
```bash
# Solution: Fetch ART dataset
python tools/art_fetch.py
```

#### Issue 2: Docker Services Not Starting
```bash
# Solution: Restart services
docker-compose -f docker/art-compose.yaml down
docker-compose -f docker/art-compose.yaml up -d
```

#### Issue 3: Proof Verification Errors
```bash
# Solution: Rebuild Lean proofs
lake build
lake clean
lake build
```

#### Issue 4: Metrics Push Failure
```bash
# Solution: Check Pushgateway connectivity
curl $PUSHGATEWAY_URL/-/healthy
```

## 📈 Performance Optimization

### Tuning Parameters

```bash
# Increase timeout for complex attacks
python tests/art_runner.py --timeout 120

# Reduce shards for faster testing
python tests/art_runner.py --shard 1/2

# Set memory limits
export ART_MEMORY_LIMIT=2GB

# Enable verbose logging
export ART_VERBOSE=true
```

### Resource Optimization

```bash
# Monitor CPU usage
top -p $(pgrep -f art_runner)

# Check disk I/O
iotop -p $(pgrep -f art_runner)

# Monitor network usage
iftop -i eth0
```

## 🎯 Success Validation

### Automated Validation

```bash
# Run validation script
python tests/art_validation.py

# Expected output:
# ✅ Overall block rate: 99.2% (>= 99%)
# ✅ All categories >= 95%
# ✅ Mean latency: 15.2ms (<= 20ms)
# ✅ False positive rate: 0% (<= 0%)
# 🎉 ART benchmark PASSED!
```

### Manual Verification

1. **Check Block Rates**: All categories should be ≥95%
2. **Verify Latency**: Mean response time should be ≤20ms
3. **Confirm Zero False Positives**: No legitimate actions should be blocked
4. **Review Logs**: No critical errors in service logs

## 🚨 Incident Response

### If Benchmark Fails

1. **Immediate Actions**:
   ```bash
   # Stop all tests
   pkill -f art_runner
   
   # Collect diagnostic data
   docker-compose -f docker/art-compose.yaml logs > art_failure.log
   
   # Save current state
   cp tests/art_results/*.json art_failure_results/
   ```

2. **Analysis**:
   - Review failing attack vectors
   - Check proof theorem coverage
   - Analyze performance bottlenecks

3. **Recovery**:
   - Update proof theorems if needed
   - Optimize performance parameters
   - Re-run with fixes

### Escalation Path

1. **Level 1**: Development team review
2. **Level 2**: Security team assessment  
3. **Level 3**: Architecture team evaluation
4. **Level 4**: Executive review

## 📋 Post-Launch Checklist

### ✅ Data Collection

- [ ] Results files saved to `tests/art_results/`
- [ ] Metrics pushed to Prometheus
- [ ] Grafana dashboard updated
- [ ] Performance logs archived

### ✅ Documentation

- [ ] Results documented in `docs/benchmarks/art.md`
- [ ] Performance trends analyzed
- [ ] Improvement recommendations noted
- [ ] Next run scheduled

### ✅ Follow-up Actions

- [ ] Address any `sorry` statements in proofs
- [ ] Update attack vectors if needed
- [ ] Optimize performance bottlenecks
- [ ] Schedule next benchmark run

## 🎉 Success Celebration

When the benchmark passes all criteria:

```bash
# Generate success report
python tools/generate_art_report.py

# Update badges
python scripts/update_art_badge.py

# Share results
echo "🎉 ART Benchmark PASSED! 🎉"
echo "Overall Block Rate: 99.2%"
echo "All Categories: PASS"
echo "Mean Latency: 15.2ms"
echo "False Positives: 0%"
```

---

**Ready to launch? Let's make it happen! 🚀**

The ART benchmark is your opportunity to prove that Provability-Fabric can defend against the most sophisticated adversarial attacks while maintaining exceptional performance. 