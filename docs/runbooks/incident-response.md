# Policy Enforcement Incident Response Runbook

This runbook provides procedures for responding to incidents in the Provability Fabric policy enforcement system, including security violations, performance issues, and system failures.

## Incident Classification

### Severity Levels

1. **SEV-1 (Critical)**
   - Policy enforcement completely disabled
   - High assurance mode violations
   - Bridge guarantee failures
   - Certificate verification failures > 1%

2. **SEV-2 (High)**
   - Performance degradation > 50%
   - Reject rate spikes > 10x normal
   - Witness validation failures > 5%
   - NI monitor reject rate > 1/sec

3. **SEV-3 (Medium)**
   - Performance degradation 20-50%
   - Reject rate spikes 2-10x normal
   - Minor configuration issues
   - Non-critical alert thresholds exceeded

4. **SEV-4 (Low)**
   - Minor performance issues
   - Informational alerts
   - Documentation updates needed

## Initial Response

### 1. Incident Detection

```bash
# Check current alerts
kubectl get events -n production --sort-by='.lastTimestamp'

# Check policy enforcement status
./pfctl status --env production

# Verify system health
kubectl get pods -n production
kubectl top pods -n production
```

### 2. Incident Declaration

```bash
# Create incident ticket
./pfctl incident create --severity SEV-1 --description "Policy enforcement failure detected"

# Notify on-call team
curl -X POST $SLACK_WEBHOOK \
  -H 'Content-type: application/json' \
  -d '{"text":"🚨 SEV-1 Policy Enforcement Incident Declared"}'

# Update status page
./pfctl status update --status "investigating"
```

### 3. Initial Assessment

```bash
# Collect system state
./pfctl collect --env production --output incident-$(date +%Y%m%d-%H%M%S).tar.gz

# Check recent policy changes
git log --oneline --since="2 hours ago" --grep="policy"

# Analyze recent violations
kubectl logs -n production -l app=sidecar-watcher --since=1h | grep -E "(VIOLATION|REJECT|ERROR)" > violations-$(date +%Y%m%d-%H%M%S).log
```

## Incident Investigation

### 1. Policy Violation Analysis

```bash
# Analyze violation patterns
./pfctl analyze --violations violations-$(date +%Y%m%d-%H%M%S).log --output analysis-$(date +%Y%m%d-%H%M%S).json

# Check policy configuration
./pfctl config show --env production --format json > config-$(date +%Y%m%d-%H%M%S).json

# Verify DFA integrity
sha256sum artifact/dfa.json
./pfctl validate --dfa artifact/dfa.json
```

### 2. Performance Investigation

```bash
# Check resource usage
kubectl top pods -n production
kubectl describe nodes | grep -A 10 "Allocated resources"

# Analyze metrics
kubectl port-forward -n production svc/prometheus 9090:9090
# Query Prometheus for performance metrics

# Check for resource constraints
kubectl get events -n production | grep -E "(OOM|Evicted|FailedScheduling)"
```

### 3. Security Investigation

```bash
# Check for unauthorized access
kubectl logs -n production -l app=sidecar-watcher | grep -E "(UNAUTHORIZED|FORBIDDEN|AUTH_FAILED)"

# Verify certificate integrity
./pfctl certs verify --env production

# Check for policy bypass attempts
kubectl logs -n production -l app=sidecar-watcher | grep -E "(BYPASS|OVERRIDE|BREAK_GLASS)"
```

## Incident Response Actions

### 1. Immediate Mitigation

```bash
# For policy enforcement failures
if [ "$SEVERITY" = "SEV-1" ]; then
  # Disable enforcement temporarily
  kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"disabled"}}'
  
  # Scale down sidecar
  kubectl scale deployment sidecar-watcher -n production --replicas=0
  
  # Notify security team
  curl -X POST $SECURITY_WEBHOOK -d '{"text":"🚨 Policy enforcement disabled due to SEV-1 incident"}'
fi

# For performance issues
if [ "$SEVERITY" = "SEV-2" ]; then
  # Scale up resources
  kubectl scale deployment sidecar-watcher -n production --replicas=3
  
  # Enable performance mode
  kubectl patch configmap policy-config -n production --patch '{"data":{"performance_mode":"enabled"}}'
fi
```

### 2. Root Cause Analysis

```bash
# Collect system dumps
kubectl exec -n production deployment/sidecar-watcher -- pkill -USR1 sidecar-watcher

# Analyze logs for patterns
./pfctl logs analyze --since="2 hours ago" --pattern="error|violation|reject"

# Check configuration drift
./pfctl config diff --env production --baseline HEAD~1

# Verify external dependencies
./pfctl health check --env production --full
```

### 3. Policy Updates

```bash
# If policy configuration is the issue
git checkout -b hotfix/policy-incident-$(date +%Y%m%d-%H%M%S)

# Update policy configuration
./pfctl config update --env production --file hotfix-policy.yaml

# Test policy changes
./pfctl test --env production --suite incident-recovery

# Deploy policy updates
./pfctl config deploy --env production --file hotfix-policy.yaml
```

## Recovery Procedures

### 1. Policy Enforcement Recovery

```bash
# Re-enable enforcement gradually
kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"shadow"}}'

# Monitor for violations
kubectl logs -n production -l app=sidecar-watcher -f | grep "POLICY_VIOLATION"

# Switch to monitor mode
kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"monitor"}}'

# Finally, re-enable enforcement
kubectl patch configmap policy-config -n production --patch '{"data":{"enforcement_mode":"enforce"}}'
```

### 2. Performance Recovery

```bash
# Optimize resource allocation
kubectl patch deployment sidecar-watcher -n production --patch '{"spec":{"template":{"spec":{"containers":[{"name":"sidecar-watcher","resources":{"requests":{"memory":"512Mi","cpu":"500m"},"limits":{"memory":"1Gi","cpu":"1000m"}}}]}}}}'

# Enable performance optimizations
kubectl patch configmap policy-config -n production --patch '{"data":{"cache_size":"1024","batch_size":"100","async_processing":"true"}}'

# Restart with new configuration
kubectl rollout restart deployment/sidecar-watcher -n production
```

### 3. Security Recovery

```bash
# Rotate compromised credentials
./pfctl rotate --credentials --env production

# Update policy rules
./pfctl policy update --env production --file security-patch.yaml

# Verify security posture
./pfctl security audit --env production --full
```

## Post-Incident

### 1. Incident Documentation

```bash
# Create incident report
cat > incident-report-$(date +%Y%m%d-%H%M%S).md << EOF
# Policy Enforcement Incident Report

## Incident Details
- **Date**: $(date)
- **Severity**: $SEVERITY
- **Duration**: $DURATION
- **Impact**: $IMPACT

## Root Cause
$ROOT_CAUSE

## Actions Taken
$ACTIONS_TAKEN

## Lessons Learned
$LESSONS_LEARNED

## Follow-up Actions
$FOLLOW_UP_ACTIONS
EOF
```

### 2. Post-Mortem

```bash
# Schedule post-mortem meeting
./pfctl incident schedule-postmortem --incident-id $INCIDENT_ID --date "$(date -d '+2 days')"

# Prepare post-mortem materials
./pfctl incident prepare-postmortem --incident-id $INCIDENT_ID --output postmortem-$(date +%Y%m%d-%H%M%S).pdf
```

### 3. Process Improvements

```bash
# Update runbooks
git add docs/runbooks/
git commit -m "Update runbooks based on incident $INCIDENT_ID"

# Update monitoring and alerting
./pfctl monitoring update --based-on-incident $INCIDENT_ID

# Update policy configuration
./pfctl policy update --env production --file post-incident-improvements.yaml
```

## Communication

### 1. Stakeholder Updates

```bash
# Update status page
./pfctl status update --status "resolved" --message "Incident resolved. Normal operations resumed."

# Notify stakeholders
curl -X POST $STAKEHOLDER_WEBHOOK \
  -d '{"text":"Policy Enforcement Incident Resolved\n\nStatus: Normal operations resumed\nNext: Post-mortem scheduled for $(date -d '+2 days')"}'

# Update incident ticket
./pfctl incident update --incident-id $INCIDENT_ID --status "resolved" --resolution "Policy enforcement restored with improvements"
```

### 2. Team Communication

```bash
# Update team chat
curl -X POST $TEAM_WEBHOOK \
  -d '{"text":"📋 Incident $INCIDENT_ID Update\n\n- Status: Resolved\n- Post-mortem: $(date -d '+2 days')\n- Next steps: Process improvements and monitoring updates"}'

# Schedule follow-up meeting
./pfctl meeting schedule --topic "Incident $INCIDENT_ID Follow-up" --date "$(date -d '+1 week')"
```

## Prevention

### 1. Monitoring Improvements

```bash
# Add new alert rules
./pfctl monitoring add-alert --rule "policy_enforcement_failure" --threshold "0" --duration "1m"

# Update existing thresholds
./pfctl monitoring update-threshold --metric "cert_verification_rate" --new-threshold "99.5"

# Add predictive alerts
./pfctl monitoring add-predictive --metric "reject_rate" --prediction-window "10m"
```

### 2. Policy Hardening

```bash
# Review and update policies
./pfctl policy review --env production --output policy-review-$(date +%Y%m%d).json

# Add additional validation rules
./pfctl policy add-validation --rule "strict_witness_check" --enabled true

# Update declassification rules
./pfctl policy update-declass --file stricter-declass-rules.yaml
```

### 3. Testing Improvements

```bash
# Add incident recovery tests
./pfctl test add --suite incident-recovery --test "policy_enforcement_failure_recovery"

# Update chaos testing
./pfctl chaos update --scenario "policy_adapter_failure" --frequency "weekly"

# Add stress testing
./pfctl test add --suite stress --test "high_reject_rate_handling"
```

## Success Criteria

- [ ] Incident resolved within SLA
- [ ] Root cause identified and documented
- [ ] Immediate mitigation implemented
- [ ] Recovery procedures completed
- [ ] Post-mortem scheduled and conducted
- [ ] Process improvements implemented
- [ ] Monitoring and alerting updated
- [ ] Team communication completed
- [ ] Lessons learned documented
- [ ] Follow-up actions assigned and tracked
