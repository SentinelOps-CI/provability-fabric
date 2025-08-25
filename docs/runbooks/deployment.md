# Policy Enforcement Deployment Runbook

This runbook covers the deployment process for the Provability Fabric policy enforcement system, including staging, production, and rollback procedures.

## Prerequisites

- Access to the target environment (staging/production)
- Valid credentials for the container registry
- Access to the policy configuration repository
- Monitoring and alerting systems configured

## Staging Deployment

### 1. Pre-deployment Checks

```bash
# Verify staging environment health
kubectl get pods -n staging
kubectl get services -n staging

# Check policy configuration
git log --oneline -10 --grep="policy"
./pfctl config validate --env staging

# Verify DFA artifacts
ls -la artifact/dfa.json
sha256sum artifact/dfa.json
```

### 2. Deploy to Staging

```bash
# Deploy sidecar watcher
kubectl apply -f k8s/staging/sidecar-watcher.yaml

# Deploy policy adapter
kubectl apply -f k8s/staging/policy-adapter.yaml

# Deploy NI monitor
kubectl apply -f k8s/staging/ni-monitor.yaml

# Wait for deployment to complete
kubectl rollout status deployment/sidecar-watcher -n staging
kubectl rollout status deployment/policy-adapter -n staging
kubectl rollout status deployment/ni-monitor -n staging
```

### 3. Post-deployment Validation

```bash
# Check pod status
kubectl get pods -n staging

# Verify health checks
kubectl exec -n staging deployment/sidecar-watcher -- curl -f http://localhost:8080/health

# Check policy enforcement
./pfctl test --env staging --suite basic

# Monitor metrics
kubectl port-forward -n staging svc/grafana 3000:3000
# Open http://localhost:3000 and check policy enforcement dashboard
```

## Production Deployment

### 1. Pre-deployment Checklist

- [ ] Staging deployment validated for 24+ hours
- [ ] All critical alerts acknowledged
- [ ] Backup of current production configuration
- [ ] Rollback plan prepared
- [ ] Team notified of deployment window
- [ ] Monitoring team on standby

### 2. Production Deployment

```bash
# Create deployment backup
kubectl get deployment sidecar-watcher -n production -o yaml > backup/sidecar-watcher-$(date +%Y%m%d-%H%M%S).yaml

# Deploy with rolling update
kubectl set image deployment/sidecar-watcher -n production sidecar-watcher=registry/provability-fabric/sidecar-watcher:v1.2.0

# Monitor rollout
kubectl rollout status deployment/sidecar-watcher -n production --timeout=600s

# Deploy other components
kubectl set image deployment/policy-adapter -n production policy-adapter=registry/provability-fabric/policy-adapter:v1.2.0
kubectl set image deployment/ni-monitor -n production ni-monitor=registry/provability-fabric/ni-monitor:v1.2.0
```

### 3. Post-deployment Validation

```bash
# Verify all pods are running
kubectl get pods -n production

# Check health endpoints
for pod in $(kubectl get pods -n production -l app=sidecar-watcher -o jsonpath='{.items[*].metadata.name}'); do
  kubectl exec -n production $pod -- curl -f http://localhost:8080/health
done

# Run smoke tests
./pfctl test --env production --suite smoke

# Verify metrics are flowing
kubectl port-forward -n production svc/prometheus 9090:9090
# Check that policy enforcement metrics are being collected
```

## Clause-by-Clause Enforcement Rollout

### Phase 1: Shadow Mode (Week 1)

```bash
# Enable shadow mode for all clauses
kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"shadow"}}'

# Monitor for violations without blocking
kubectl logs -n production -l app=sidecar-watcher -f | grep "POLICY_VIOLATION"
```

### Phase 2: Monitor Mode (Week 2)

```bash
# Switch to monitor mode
kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"monitor"}}'

# Track violations and prepare for enforcement
./pfctl stats --env production --format json > violations-report-$(date +%Y%m%d).json
```

### Phase 3: Enforcement Mode (Week 3+)

```bash
# Enable enforcement for non-critical clauses
kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"enforce"}}'

# Monitor for any issues
kubectl logs -n production -l app=sidecar-watcher -f | grep "BLOCKED_ACTION"
```

## TTL Handling

### Automatic Expiration

```bash
# Check for expiring policies
./pfctl list --expiring --days 7

# Extend TTL for critical policies
./pfctl extend --policy-id POLICY_001 --ttl 30d
```

### Manual TTL Management

```bash
# List all active policies with TTL
./pfctl list --active --show-ttl

# Force expire a policy
./pfctl expire --policy-id POLICY_001 --reason "Manual expiration"
```

## Rollback Procedures

### Quick Rollback

```bash
# Rollback to previous version
kubectl rollout undo deployment/sidecar-watcher -n production

# Verify rollback
kubectl rollout status deployment/sidecar-watcher -n production
kubectl get pods -n production
```

### Configuration Rollback

```bash
# Restore previous configuration
kubectl apply -f backup/sidecar-watcher-$(date +%Y%m%d-%H%M%S).yaml

# Restart pods to pick up configuration
kubectl rollout restart deployment/sidecar-watcher -n production
```

### Emergency Rollback

```bash
# Disable policy enforcement entirely
kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"disabled"}}'

# Scale down sidecar
kubectl scale deployment sidecar-watcher -n production --replicas=0

# Notify security team immediately
```

## Monitoring and Alerts

### Key Metrics to Watch

- Certificate verification rate (should be > 99.9%)
- NI monitor reject rate (should be < 0.1/sec)
- Permission reject rate (should be < 0.05/sec)
- Monitor performance P95 (should be < 100ms)
- Replay determinism (should be > 99.9%)

### Alert Response

1. **Critical Alerts**: Immediate response required
   - Certificate verification failures
   - High assurance mode violations
   - Bridge guarantee failures

2. **Warning Alerts**: Investigate within 15 minutes
   - Performance degradation
   - Reject rate spikes
   - Witness validation failures

3. **Info Alerts**: Monitor and log
   - Enforcement mode changes
   - Configuration updates

## Troubleshooting

### Common Issues

1. **Policy Adapter Not Responding**
   ```bash
   kubectl logs -n production -l app=policy-adapter --tail=100
   kubectl exec -n production deployment/policy-adapter -- curl -f http://localhost:8080/health
   ```

2. **High Reject Rates**
   ```bash
   # Check policy configuration
   ./pfctl config show --env production
   
   # Analyze reject patterns
   kubectl logs -n production -l app=sidecar-watcher | grep "REJECT" | jq .
   ```

3. **Performance Issues**
   ```bash
   # Check resource usage
   kubectl top pods -n production
   
   # Analyze metrics
   kubectl port-forward -n production svc/prometheus 9090:9090
   ```

### Debug Mode

```bash
# Enable debug logging
kubectl patch configmap policy-config -n production --patch '{"data":{"log_level":"debug"}}'

# Restart pods
kubectl rollout restart deployment/sidecar-watcher -n production

# Collect debug logs
kubectl logs -n production -l app=sidecar-watcher --tail=1000 > debug-logs-$(date +%Y%m%d-%H%M%S).log
```

## Success Criteria

- [ ] All pods running and healthy
- [ ] Health checks passing
- [ ] Metrics flowing to monitoring systems
- [ ] Smoke tests passing
- [ ] No critical alerts firing
- [ ] Policy enforcement working as expected
- [ ] Performance within acceptable limits

## Post-Deployment

1. **Documentation Update**
   - Update deployment notes
   - Record any issues encountered
   - Update runbook based on lessons learned

2. **Team Notification**
   - Notify stakeholders of successful deployment
   - Schedule post-deployment review
   - Update status pages and dashboards

3. **Monitoring**
   - Continue monitoring for 24-48 hours
   - Watch for any delayed issues
   - Prepare for next deployment cycle
