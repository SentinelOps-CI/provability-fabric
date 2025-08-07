# Service Level Objectives (SLOs)

## Overview

This document defines the Service Level Objectives (SLOs) for the Provability-Fabric runtime components. These SLOs ensure predictable performance and enable proactive monitoring of system health.

## End-to-End SLOs

### Primary SLOs
- **p95 Latency**: ≤ 2.0 seconds
- **p99 Latency**: ≤ 4.0 seconds
- **Availability**: ≥ 99.9%

### Secondary SLOs
- **Error Rate**: ≤ 0.1%
- **Throughput**: ≥ 1000 requests/second

## Per-Component Budgets

### Component Budgets (Initial)
| Component | Budget | Description |
|-----------|--------|-------------|
| Plan Generation | ≤ 150 ms | Time to create and validate plan |
| Retrieval Gateway | ≤ 600 ms | Time to retrieve and process content |
| Policy Kernel | ≤ 120 ms | Time for capability and receipt validation |
| Egress Firewall | ≤ 400 ms | Time for content scanning and certificate generation |
| High-Risk Proof Replay | ≤ 200 ms | Time for proof verification (when triggered) |

### Total Budget Allocation
- **Plan**: 150 ms (7.5%)
- **Retrieval**: 600 ms (30%)
- **Kernel**: 120 ms (6%)
- **Egress**: 400 ms (20%)
- **Buffer**: 730 ms (36.5%)
- **Total**: 2000 ms (100%)

## Performance Headers

The system emits performance headers for monitoring:

```
X-PF-Plan-ms: 145
X-PF-Retrieval-ms: 580
X-PF-Kernel-ms: 115
X-PF-Egress-ms: 385
X-PF-Total-ms: 1245
```

## CI Gates

### PR Smoke Test
- **Duration**: 60 seconds
- **Load**: 1000 RPS
- **Requirements**:
  - p95 < 2.2s
  - p99 < 4.2s
  - No component exceeds budget by >3%
- **CI Job**: [slo-gates-pr](/.github/workflows/slo-gates.yaml)

### Nightly Performance Test
- **Duration**: 10 minutes
- **Load**: 1000 RPS
- **Requirements**:
  - p95 < 2.0s
  - p99 < 4.0s
  - No component exceeds budget by >3%
- **CI Job**: [slo-gates-nightly](/.github/workflows/slo-gates.yaml)

### Release Gates
- **p95 Latency**: ≤ 2.0s (blocking)
- **p99 Latency**: ≤ 4.0s (blocking)
- **Error Rate**: ≤ 0.1% (blocking)
- **Component Budgets**: All within limits (blocking)
- **CI Job**: [release-fence](/.github/workflows/release.yaml)

## Monitoring and Alerting

### Grafana Dashboards
- **PF SLO**: End-to-end latency histograms
- **Component Budgets**: Per-component performance breakdown
- **Error Rates**: Component-specific error tracking

### Alerts
- **SLO Violation**: p95 > 2.0s for 5 minutes
- **Component Budget Exceeded**: Any component > budget for 3 minutes
- **Error Rate Spike**: Error rate > 1% for 2 minutes

## Performance Testing

### Load Testing Scripts
- `tests/perf/latency_k6.js`: End-to-end latency testing
- `tests/perf/component_budgets.ts`: Component-specific budget validation

### Test Scenarios
1. **Baseline**: Normal load with valid requests
2. **High Load**: 2x normal load to test scaling
3. **Error Injection**: Invalid plans to test error handling
4. **Component Stress**: Individual component stress testing

## Budget Enforcement

### Kernel Checks
The policy kernel enforces component budgets:

```go
// Example budget check in kernel
if planTime > 150*time.Millisecond {
    return KernelResult::Invalid {
        reason: "Plan generation exceeded budget"
    }
}
```

### Sidecar Monitoring
The sidecar-watcher tracks component performance:

```rust
// Example performance tracking
let start = Instant::now();
let result = kernel.validate_plan(&plan);
let duration = start.elapsed();

if duration > Duration::from_millis(120) {
    metrics.kernel_budget_violations.inc();
}
```

## Failure Scenarios

### Component Budget Violations
1. **Plan Generation > 150ms**: Kernel rejects plan with BUDGET_EXCEEDED
2. **Retrieval > 600ms**: Gateway returns timeout error
3. **Kernel > 120ms**: Sidecar logs performance warning
4. **Egress > 400ms**: Firewall returns 503 with retry-after

### End-to-End Violations
1. **p95 > 2.0s**: Alert triggered, auto-scaling initiated
2. **p99 > 4.0s**: Emergency alert, manual intervention required
3. **Error Rate > 0.1%**: Circuit breaker activated

## Continuous Improvement

### Weekly Reviews
- Analyze performance trends
- Identify optimization opportunities
- Update budgets based on usage patterns

### Monthly SLO Reviews
- Assess SLO effectiveness
- Adjust thresholds based on business needs
- Plan capacity improvements

## Links

- [CI Job: slo-gates.yaml](/.github/workflows/slo-gates.yaml)
- [Performance Tests](/tests/perf/)
- [Grafana Dashboards](/grafana/dashboards/)
- [Component Budgets Test](/tests/perf/component_budgets.ts) 