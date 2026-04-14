# Operations Runbook

## Overview

This runbook provides step-by-step procedures for operating, monitoring, and troubleshooting the Provability-Fabric system. It follows the triage → receipts → certificates → proofs escalation path.

## Emergency Contacts

| Role | Primary | Secondary | Escalation |
|------|---------|-----------|------------|
| Security Incident | security@company.com | ciso@company.com | CEO |
| System Outage | sre@company.com | engineering@company.com | CTO |
| Data Privacy | privacy@company.com | legal@company.com | CPO |
| Compliance | compliance@company.com | audit@company.com | CCO |

## Incident Classification

### P0 - Critical
- System-wide outage
- Security breach confirmed
- Data loss or corruption
- Cross-tenant data exposure

**Response Time**: 15 minutes
**Resolution Time**: 4 hours

### P1 - High
- Single service outage
- Performance degradation >50%
- Security alert requiring investigation
- Compliance violation

**Response Time**: 1 hour
**Resolution Time**: 24 hours

### P2 - Medium
- Partial functionality impaired
- Performance degradation <50%
- Non-critical security finding
- Monitoring alert

**Response Time**: 4 hours
**Resolution Time**: 72 hours

### P3 - Low
- Minor bugs or enhancements
- Documentation updates
- Routine maintenance

**Response Time**: Next business day
**Resolution Time**: Next sprint

## Triage Procedures

### Initial Assessment (0-15 minutes)

1. **Identify the Problem**
   ```bash
   # Check system health
   kubectl get pods -A | grep -v Running
   curl -f http://health-check.internal/status
   
   # Check key metrics
   curl http://prometheus:9090/api/v1/query?query=up
   ```

2. **Determine Scope**
   - Single tenant affected?
   - Single service affected?
   - Multiple components affected?
   - External dependencies affected?

3. **Classify Severity**
   - Data exposure risk?
   - User impact level?
   - Business continuity impact?
   - Compliance implications?

4. **Assemble Response Team**
   ```bash
   # Page appropriate teams
   ./scripts/page-team.sh --severity P0 --component retrieval-gateway
   ```

### Information Gathering (15-30 minutes)

5. **Collect Initial Evidence**
   ```bash
   # Get recent logs
   kubectl logs -l app=retrieval-gateway --since=1h > logs/retrieval-$(date +%s).log
   kubectl logs -l app=egress-firewall --since=1h > logs/egress-$(date +%s).log
   
   # Get system metrics
   curl -s "http://prometheus:9090/api/v1/query_range?query=rate(http_requests_total[5m])&start=$(date -d '1 hour ago' +%s)&end=$(date +%s)&step=60" > metrics/requests.json
   ```

6. **Check Recent Changes**
   ```bash
   # Check recent deployments
   kubectl get deployments -A -o custom-columns=NAME:.metadata.name,READY:.status.readyReplicas,UP-TO-DATE:.status.updatedReplicas,AVAILABLE:.status.availableReplicas,AGE:.metadata.creationTimestamp
   
   # Check recent config changes
   git log --since="24 hours ago" --oneline
   ```

## Access Receipts Investigation

### Receipt Analysis

1. **Get Recent Receipts**
   ```bash
   # Query ledger for recent receipts
   curl -H "Authorization: Bearer $LEDGER_TOKEN" \
        "http://ledger:3000/receipts?since=$(date -d '1 hour ago' -Iseconds)" \
        | jq '.' > receipts.json
   ```

2. **Analyze Receipt Patterns**
   ```bash
   # Check for missing receipts
   python3 tools/analyze_receipts.py --file receipts.json --check-gaps
   
   # Check for cross-tenant violations
   python3 tools/analyze_receipts.py --file receipts.json --check-isolation
   
   # Check ABAC decision patterns
   python3 tools/analyze_receipts.py --file receipts.json --check-abac
   ```

3. **Verify Receipt Signatures**
   ```bash
   # Validate receipt signatures
   python3 tools/verify_receipts.py --file receipts.json --public-key keys/receipt-verify.pem
   ```

### Common Receipt Issues

#### Missing Receipts
**Symptoms**: Gaps in receipt timestamps
**Investigation**:
```bash
# Check retrieval gateway health
kubectl get pods -l app=retrieval-gateway
kubectl logs -l app=retrieval-gateway --tail=100

# Check ledger connectivity
curl -f http://ledger:3000/health
```

**Resolution**:
```bash
# Restart gateway if unhealthy
kubectl rollout restart deployment/retrieval-gateway

# Check and fix ledger issues
kubectl logs -l app=ledger --tail=100
```

#### Invalid Receipt Signatures
**Symptoms**: Signature verification failures
**Investigation**:
```bash
# Check signing key rotation
kubectl get secret receipt-signing-key -o yaml

# Check receipt format
jq '.signature' receipts.json | head -5
```

**Resolution**:
```bash
# Update signing keys if rotated
kubectl apply -f configs/receipt-signing-key.yaml

# Regenerate invalid receipts if needed
python3 tools/regenerate_receipts.py --timerange "2024-01-15T10:00:00Z/2024-01-15T11:00:00Z"
```

## Egress Certificates Investigation

### Certificate Analysis

1. **Get Recent Certificates**
   ```bash
   # Query ledger for certificates
   curl -H "Authorization: Bearer $LEDGER_TOKEN" \
        "http://ledger:3000/egress-certificates?since=$(date -d '1 hour ago' -Iseconds)" \
        | jq '.' > certificates.json
   ```

2. **Analyze Detection Patterns**
   ```bash
   # Check PII detection rates
   jq '[.[] | .detectors.pii] | add' certificates.json
   
   # Check secret detection rates  
   jq '[.[] | .detectors.secret] | add' certificates.json
   
   # Check policy hash consistency
   jq '[.[] | .policy_hash] | unique' certificates.json
   ```

3. **Verify Certificate Integrity**
   ```bash
   # Validate certificate signatures
   python3 tools/verify_certificates.py --file certificates.json
   
   # Check certificate completeness
   python3 tools/check_certificate_coverage.py --timerange "1hour"
   ```

### Common Certificate Issues

#### High False Positive Rate
**Symptoms**: Legitimate content being blocked
**Investigation**:
```bash
# Analyze detection patterns
python3 tools/analyze_certificates.py --file certificates.json --false-positives

# Check policy configuration
kubectl get configmap egress-policies -o yaml
```

**Resolution**:
```bash
# Update detection thresholds
kubectl patch configmap egress-policies --patch '{"data":{"pii_threshold":"0.8"}}'

# Restart egress firewall
kubectl rollout restart deployment/egress-firewall
```

#### Missing Certificates
**Symptoms**: Gaps in certificate generation
**Investigation**:
```bash
# Check firewall health
kubectl get pods -l app=egress-firewall
kubectl logs -l app=egress-firewall --tail=100

# Check certificate storage
curl -f http://ledger:3000/egress-certificates/count
```

**Resolution**:
```bash
# Restart firewall if needed
kubectl rollout restart deployment/egress-firewall

# Regenerate missing certificates
python3 tools/regenerate_certificates.py --timerange "1hour"
```

## Formal Proofs Investigation

### Proof Verification

1. **Check Lean Compilation**
   ```bash
   # Verify all proofs compile
   cd core/lean-libs
   lean --check Invariants.lean
   lean --check Plan.lean
   lean --check Capability.lean
   ```

2. **Run Invariant Gate**
   ```bash
   # Check invariant usage across bundles
   python3 tools/invariant_gate.py --project-root . --fail-on-warnings
   ```

3. **Verify Bundle Proofs**
   ```bash
   # Check specific bundle proofs
   cd bundles/my-agent/proofs
   lean --check Spec.lean
   
   # Check for sorry proofs
   grep -r "sorry" bundles/*/proofs/ || echo "No sorry proofs found"
   ```

### Common Proof Issues

#### Compilation Failures
**Symptoms**: Lean proof compilation errors
**Investigation**:
```bash
# Check for syntax errors
lean --check core/lean-libs/Invariants.lean 2>&1 | head -20

# Check dependencies
lean --deps core/lean-libs/Invariants.lean
```

**Resolution**:
```bash
# Fix syntax errors based on output
# Update imports if needed
# Regenerate proof if corrupted
```

#### Missing Invariant Usage
**Symptoms**: Invariant gate failures
**Investigation**:
```bash
# Check which bundles lack invariant imports
python3 tools/invariant_gate.py --verbose
```

**Resolution**:
```bash
# Add missing imports to bundle specs
echo "import Invariants" >> bundles/example/proofs/Spec.lean

# Verify invariant usage
python3 tools/invariant_gate.py
```

## Performance Troubleshooting

### High Latency

1. **Identify Bottleneck Component**
   ```bash
   # Check service latencies
   curl -s "http://prometheus:9090/api/v1/query?query=histogram_quantile(0.95,rate(http_request_duration_seconds_bucket[5m]))"
   ```

2. **Database Performance**
   ```bash
   # Check database connections
   kubectl exec -it postgres-0 -- psql -c "SELECT count(*) FROM pg_stat_activity;"
   
   # Check slow queries
   kubectl exec -it postgres-0 -- psql -c "SELECT query, mean_time FROM pg_stat_statements ORDER BY mean_time DESC LIMIT 10;"
   ```

3. **Resource Utilization**
   ```bash
   # Check CPU and memory
   kubectl top pods -A --sort-by=cpu
   kubectl top pods -A --sort-by=memory
   ```

### High Error Rates

1. **Check Error Distribution**
   ```bash
   # Get error breakdown by service
   curl -s "http://prometheus:9090/api/v1/query?query=rate(http_requests_total{status=~'5..'}[5m])"
   ```

2. **Analyze Error Logs**
   ```bash
   # Get recent errors
   kubectl logs -l app=retrieval-gateway --since=1h | grep ERROR
   kubectl logs -l app=egress-firewall --since=1h | grep ERROR
   ```

## Security Incident Response

### Data Exposure Incident

1. **Immediate Containment**
   ```bash
   # Isolate affected components
   kubectl scale deployment/retrieval-gateway --replicas=0
   
   # Block external traffic
   kubectl apply -f configs/emergency-network-policy.yaml
   ```

2. **Evidence Preservation**
   ```bash
   # Capture logs
   kubectl logs -l app=retrieval-gateway --since=24h > incident-logs-$(date +%s).log
   
   # Capture recent receipts and certificates
   curl -H "Authorization: Bearer $LEDGER_TOKEN" \
        "http://ledger:3000/receipts?since=$(date -d '24 hours ago' -Iseconds)" \
        > incident-receipts-$(date +%s).json
   ```

3. **Impact Assessment**
   ```bash
   # Analyze affected tenants
   python3 tools/analyze_exposure.py --logs incident-logs-*.log --receipts incident-receipts-*.json
   
   # Check for cross-tenant access
   python3 tools/check_tenant_isolation.py --receipts incident-receipts-*.json
   ```

### Capability Bypass Incident

1. **Identify Scope**
   ```bash
   # Check for authorization failures
   kubectl logs -l app=sidecar-watcher --since=1h | grep "capability"
   
   # Analyze capability tokens
   curl -H "Authorization: Bearer $LEDGER_TOKEN" \
        "http://ledger:3000/capability-tokens?status=active" \
        > active-tokens.json
   ```

2. **Revoke Compromised Tokens**
   ```bash
   # Revoke specific tokens
   curl -X POST -H "Authorization: Bearer $LEDGER_TOKEN" \
        "http://ledger:3000/capability-tokens/revoke" \
        -d '{"token_ids": ["token123", "token456"]}'
   ```

## Maintenance Procedures

### Planned Maintenance

1. **Pre-Maintenance Checklist**
   - [ ] Notify stakeholders 24h in advance
   - [ ] Verify backup procedures
   - [ ] Prepare rollback plan
   - [ ] Check system health baseline

2. **During Maintenance**
   ```bash
   # Enable maintenance mode
   kubectl apply -f configs/maintenance-mode.yaml
   
   # Monitor system health
   watch kubectl get pods -A
   ```

3. **Post-Maintenance Verification**
   ```bash
   # Run health checks
   python3 tests/health_check.py --full
   
   # Verify evidence generation
   python3 tools/check_evidence_continuity.py --since="1hour"
   
   # Run smoke tests
   python3 tests/smoke_test.py
   ```

### Certificate Rotation

1. **Backup Current Certificates**
   ```bash
   # Backup signing keys
   kubectl get secret -o yaml > backup/secrets-$(date +%s).yaml
   ```

2. **Generate New Certificates**
   ```bash
   # Generate new keys
   python3 tools/generate_keys.py --type receipt-signing
   python3 tools/generate_keys.py --type egress-signing
   ```

3. **Update System Configuration**
   ```bash
   # Update secrets
   kubectl apply -f configs/new-signing-keys.yaml
   
   # Rolling restart affected services
   kubectl rollout restart deployment/retrieval-gateway
   kubectl rollout restart deployment/egress-firewall
   ```

## Monitoring and Alerting

### Key Metrics Dashboard

Access the monitoring dashboard at: `https://grafana.internal/d/provability-fabric`

**Critical Alerts**:
- Cross-tenant access detected
- PII leak in egress
- Capability bypass attempt
- Evidence generation gap
- High error rate (>5%)
- High latency (P95 >2s)

### Alert Response Procedures

#### Cross-Tenant Access Alert
1. **Immediate**: Isolate affected tenant
2. **Investigation**: Analyze access receipts
3. **Resolution**: Fix isolation mechanism
4. **Follow-up**: Enhanced monitoring

#### PII Leak Alert
1. **Immediate**: Review egress certificates
2. **Investigation**: Analyze detection bypass
3. **Resolution**: Update detection rules
4. **Follow-up**: Red team testing

#### High Latency Alert
1. **Immediate**: Check resource utilization
2. **Investigation**: Identify bottleneck
3. **Resolution**: Scale or optimize
4. **Follow-up**: Capacity planning

## Escalation Procedures

### When to Escalate

- P0 incident not resolved in 4 hours
- Security breach confirmed
- Multiple component failures
- Regulatory compliance at risk

### Escalation Contacts

1. **Engineering Manager**: For technical complexity
2. **Security Team Lead**: For security incidents
3. **VP Engineering**: For customer-facing outages
4. **CISO**: For data breaches
5. **Legal**: For compliance violations

### Executive Communication

For P0 incidents, provide updates every 30 minutes with:
- Current status
- Actions taken
- Next steps
- ETA for resolution

## Documentation Updates

After any incident:
1. Update this runbook with lessons learned
2. Add new troubleshooting procedures
3. Update monitoring and alerting rules
4. Schedule post-mortem review

## Training and Drills

### Monthly Drills
- Incident response simulation
- Certificate rotation practice
- Backup/restore procedures
- Alert response training

### Quarterly Reviews
- Runbook accuracy validation
- Escalation procedure testing
- Contact information updates
- Tool effectiveness assessment