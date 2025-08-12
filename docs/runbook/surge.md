# Surge Runbook

## Overview

This runbook provides procedures for handling traffic spikes and system overload in Provability-Fabric, including strict mode activation, load-shedding, and recovery procedures.

## Traffic Spike Detection

### Automatic Triggers

The system automatically activates strict mode when:

1. **Queue Length Threshold**: Queue length exceeds 80% of maximum capacity
2. **Response Time Budget**: P95 response time breaches 500ms budget
3. **System Load**: CPU usage exceeds 85% for 5+ minutes

### Monitoring Dashboards

- **Queue Length**: Real-time queue depth across all services
- **Response Time**: P95, P99 response time trends
- **Strict Mode Status**: Current strict mode state and reason
- **Dropped Requests**: Count of requests dropped due to load-shedding
- **Critical Leaks**: Any critical security violations during strict mode

## Strict Mode Activation

### What Happens

When strict mode activates:

1. **Non-Critical Detectors Skipped**:
   - NLP-based detection
   - MinHash LSH similarity
   - Format entropy analysis
   - Near-duplicate detection

2. **Critical Detectors Maintained**:
   - PII detection (Aho-Corasick)
   - Secrets detection (Format analysis)
   - Policy enforcement

3. **Load-Shedding**:
   - Low-priority requests dropped
   - Queue backpressure applied
   - Response time budgets enforced

### Immediate Actions

1. **Alert Response**:
   - Acknowledge strict mode activation
   - Review activation reason
   - Assess current system state

2. **Team Notification**:
   - Page on-call engineer
   - Notify security team
   - Alert operations team

3. **Traffic Analysis**:
   - Identify traffic source
   - Check for DDoS indicators
   - Review recent deployments

## During Strict Mode

### Monitoring

- **Every 5 minutes**: Check queue length and response times
- **Every 15 minutes**: Review dropped request patterns
- **Every 30 minutes**: Assess recovery progress

### Manual Overrides

```bash
# Check current strict mode status
curl -X GET http://localhost:8080/health/backpressure

# Manually activate strict mode
curl -X POST http://localhost:8080/admin/strict-mode \
  -H "Content-Type: application/json" \
  -d '{"reason": "manual_activation", "duration_minutes": 30}'

# Manually deactivate strict mode
curl -X POST http://localhost:8080/admin/strict-mode/deactivate
```

### Emergency Procedures

1. **Critical Security Breach**:
   - Immediately deactivate strict mode
   - Enable all detectors
   - Accept performance degradation

2. **System Overload**:
   - Increase strict mode thresholds
   - Extend cooldown periods
   - Consider service restart

## Recovery Procedures

### Automatic Recovery

Strict mode automatically deactivates when:

1. **Queue Length**: Drops below 60% of maximum
2. **Response Time**: P95 returns below 500ms budget
3. **Cooldown Period**: 30 seconds have elapsed since activation

### Manual Recovery

1. **Verify System Health**:
   ```bash
   # Check all health endpoints
   curl http://localhost:8080/health
   curl http://localhost:8080/health/backpressure
   curl http://localhost:8080/metrics
   ```

2. **Gradual Detector Re-enabling**:
   - Start with format entropy analysis
   - Enable MinHash LSH similarity
   - Re-enable NLP processing last

3. **Monitor Recovery**:
   - Watch response time trends
   - Check queue length stability
   - Verify no critical leaks

### Recovery Validation

1. **Performance Check**:
   - P95 response time < 500ms
   - Queue length < 60% capacity
   - CPU usage < 70%

2. **Security Validation**:
   - Run security test suite
   - Verify no critical detectors skipped
   - Check audit logs for violations

3. **Load Testing**:
   - Gradual traffic increase
   - Monitor system stability
   - Verify SLO compliance

## Post-Incident Actions

### Documentation

1. **Incident Report**:
   - Root cause analysis
   - Timeline of events
   - Actions taken
   - Lessons learned

2. **Metrics Review**:
   - Traffic patterns analysis
   - Performance impact assessment
   - Cost analysis

3. **Process Updates**:
   - Update runbook procedures
   - Modify thresholds if needed
   - Improve monitoring

### Follow-up

1. **Team Review**:
   - Incident response effectiveness
   - Communication improvements
   - Tooling enhancements

2. **System Improvements**:
   - Capacity planning updates
   - Auto-scaling configuration
   - Alert threshold tuning

## Configuration

### Environment Variables

```bash
# Backpressure configuration
ENABLE_BACKPRESSURE=true
MAX_QUEUE_LENGTH=1000
P95_RESPONSE_TIME_BUDGET_MS=500
STRICT_MODE_THRESHOLD=0.8
STRICT_MODE_COOLDOWN_MS=30000

# Critical detectors (never skipped)
CRITICAL_DETECTORS=pii_detector,secrets_detector,policy_enforcement

# Non-critical detectors (skipped in strict mode)
NON_CRITICAL_DETECTORS=near_dupe_detector,nlp_detector,format_entropy_detector
```

### Service Configuration

```yaml
# egress-firewall configuration
pipeline:
  enable_backpressure: true
  max_queue_length: 1000
  p95_response_time_budget_ms: 500
  strict_mode_threshold: 0.8
  critical_detectors:
    - AhoCorasick
    - FormatEntropy
  non_critical_detectors:
    - SimHash64
    - MinHashLSH
    - NLP
```

## Metrics and Alerts

### Key Metrics

- `queue_length_current`: Current queue depth
- `queue_length_average`: Average queue length over time
- `strict_mode_active`: Boolean strict mode status
- `strict_mode_activations_total`: Count of activations
- `queue_dropped_total`: Count of dropped requests
- `p95_response_time_ms`: 95th percentile response time

### Alerting Rules

```yaml
# Strict mode activation alert
- alert: StrictModeActivated
  expr: strict_mode_active == 1
  for: 0m
  labels:
    severity: warning
  annotations:
    summary: "Strict mode activated"
    description: "System entered strict mode due to high load"

# Queue length alert
- alert: QueueLengthHigh
  expr: queue_length_current > 800
  for: 2m
  labels:
    severity: warning
  annotations:
    summary: "Queue length high"
    description: "Queue length is {{ $value }} (threshold: 800)"

# Response time alert
- alert: ResponseTimeHigh
  expr: p95_response_time_ms > 400
  for: 2m
  labels:
    severity: warning
  annotations:
    summary: "Response time high"
    description: "P95 response time is {{ $value }}ms (threshold: 400ms)"
```

## Troubleshooting

### Common Issues

1. **Strict Mode Not Activating**:
   - Check configuration values
   - Verify monitoring is working
   - Check log levels

2. **Performance Degradation**:
   - Review detector execution order
   - Check resource utilization
   - Analyze response time patterns

3. **False Positives**:
   - Adjust threshold values
   - Review traffic patterns
   - Update detector priorities

### Debug Commands

```bash
# Check backpressure state
curl http://localhost:8080/debug/backpressure

# View queue contents
curl http://localhost:8080/debug/queue

# Check detector performance
curl http://localhost:8080/debug/detectors

# View system metrics
curl http://localhost:8080/metrics | grep -E "(queue|strict_mode|response_time)"
```

## References

- [Backpressure Implementation](../optimization/backpressure.md)
- [System Architecture](../architecture/overview.md)
- [Performance SLOs](../slo/performance.md)
- [Security Policies](../security/policies.md)
- [Incident Response](../incident/response.md)
