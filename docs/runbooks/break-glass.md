# Break-Glass Emergency Procedures Runbook

This runbook provides procedures for emergency policy bypass (break-glass) scenarios in the Provability Fabric policy enforcement system. These procedures should only be used in critical emergencies when normal policy enforcement would prevent essential operations.

## Break-Glass Scenarios

### 1. Critical System Access
- Emergency maintenance requiring elevated permissions
- Disaster recovery operations
- Security incident response requiring immediate access

### 2. Policy Enforcement Failure
- Complete policy enforcement system failure
- Critical bug preventing legitimate operations
- Emergency rollback requiring policy bypass

### 3. Business Continuity
- Critical business operations blocked by policy
- Emergency service restoration
- Compliance requirements for emergency access

## Pre-Break-Glass Checklist

### 1. Authorization Requirements
- [ ] **2-of-3 approvals** from authorized personnel:
  - Security team lead
  - System administrator
  - Business owner
- [ ] Incident ticket created and documented
- [ ] Business justification documented
- [ ] Risk assessment completed

### 2. Documentation Requirements
- [ ] Break-glass reason documented
- [ ] Expected duration specified
- [ ] Rollback plan prepared
- [ ] Stakeholders notified

### 3. Safety Measures
- [ ] Monitoring enhanced for break-glass period
- [ ] Audit logging enabled at maximum level
- [ ] Time limit set (maximum 2 hours)
- [ ] Emergency contacts on standby

## Break-Glass Procedures

### 1. Emergency Authorization

```bash
# Create break-glass ticket
./pfctl break-glass create \
  --reason "Emergency system maintenance" \
  --duration "2h" \
  --approvers "security-lead,admin-lead,business-owner" \
  --business-justification "Critical system failure requiring immediate access"

# Verify approvals
./pfctl break-glass status --ticket-id $BREAK_GLASS_ID

# Wait for 2-of-3 approvals
while [ "$(./pfctl break-glass approvals --ticket-id $BREAK_GLASS_ID | jq -r '.approved')" != "true" ]; do
  echo "Waiting for approvals..."
  sleep 30
done
```

### 2. Enable Break-Glass Mode

```bash
# Enable break-glass mode
./pfctl break-glass enable \
  --ticket-id $BREAK_GLASS_ID \
  --scope "global" \
  --ttl "2h"

# Verify break-glass mode is active
./pfctl status --env production | grep "Break-Glass Mode"

# Update monitoring
kubectl patch configmap monitoring-config -n production \
  --patch '{"data":{"break_glass_enabled":"true","audit_level":"maximum"}}'
```

### 3. Policy Bypass Configuration

```bash
# Temporarily disable policy enforcement
kubectl patch configmap policy-config -n production \
  --patch '{"data":{"enforcement_mode":"break_glass","break_glass_ticket":"'$BREAK_GLASS_ID'"}}'

# Restart sidecar to pick up configuration
kubectl rollout restart deployment/sidecar-watcher -n production

# Verify break-glass mode is active
kubectl logs -n production -l app=sidecar-watcher | grep "BREAK_GLASS_MODE"
```

## Break-Glass Operations

### 1. Emergency Access

```bash
# Grant emergency permissions
./pfctl break-glass grant \
  --ticket-id $BREAK_GLASS_ID \
  --principal "emergency-admin" \
  --permissions "admin,superuser" \
  --ttl "2h"

# Verify emergency access
./pfctl test --env production --suite emergency-access
```

### 2. Emergency Operations

```bash
# Perform emergency operations
# Example: Emergency database access
kubectl exec -n production deployment/emergency-tool -- \
  ./emergency-db-access --operation "restore" --backup "latest"

# Log all emergency operations
./pfctl break-glass log \
  --ticket-id $BREAK_GLASS_ID \
  --operation "database_restore" \
  --details "Emergency database restoration completed"
```

### 3. Enhanced Monitoring

```bash
# Enable maximum audit logging
kubectl patch configmap audit-config -n production \
  --patch '{"data":{"log_level":"debug","capture_all":"true","retention":"7d"}}'

# Monitor for any unauthorized access attempts
kubectl logs -n production -l app=sidecar-watcher -f | \
  grep -E "(UNAUTHORIZED|BREAK_GLASS|EMERGENCY)" > break-glass-audit-$(date +%Y%m%d-%H%M%S).log
```

## Break-Glass Time Management

### 1. Time Tracking

```bash
# Start break-glass timer
BREAK_GLASS_START=$(date +%s)
BREAK_GLASS_TTL=7200  # 2 hours in seconds

# Monitor remaining time
while [ $(($(date +%s) - $BREAK_GLASS_START)) -lt $BREAK_GLASS_TTL ]; do
  remaining=$((BREAK_GLASS_TTL - ($(date +%s) - $BREAK_GLASS_START)))
  echo "Break-glass mode active. $((remaining / 60)) minutes remaining."
  
  if [ $remaining -le 300 ]; then  # 5 minutes remaining
    echo "WARNING: Break-glass mode expires in $((remaining / 60)) minutes"
    # Send warning notifications
    curl -X POST $ALERT_WEBHOOK \
      -d '{"text":"Break-glass mode expires in '$((remaining / 60))' minutes"}'
  fi
  
  sleep 60
done
```

### 2. Auto-Expiration

```bash
# Auto-expire break-glass mode
echo "🚨 Break-glass mode expired. Disabling emergency access."

# Disable break-glass mode
./pfctl break-glass disable --ticket-id $BREAK_GLASS_ID

# Re-enable policy enforcement
kubectl patch configmap policy-config -n production \
  --patch '{"data":{"enforcement_mode":"enforce"}}'

# Restart sidecar
kubectl rollout restart deployment/sidecar-watcher -n production
```

## Break-Glass Rollback

### 1. Manual Rollback

```bash
# Disable break-glass mode manually
./pfctl break-glass disable --ticket-id $BREAK_GLASS_ID

# Verify break-glass mode is disabled
./pfctl status --env production | grep "Break-Glass Mode"

# Re-enable normal policy enforcement
kubectl patch configmap policy-config -n production \
  --patch '{"data":{"enforcement_mode":"enforce"}}'
```

### 2. Policy Restoration

```bash
# Restore normal policy configuration
./pfctl config restore --env production --baseline "pre-break-glass"

# Verify policy restoration
./pfctl config show --env production --format json > post-break-glass-config.json

# Compare with baseline
./pfctl config diff --env production --baseline "pre-break-glass"
```

### 3. Security Verification

```bash
# Verify security posture
./pfctl security audit --env production --full

# Check for any unauthorized changes
./pfctl audit review --since "break-glass-start" --output unauthorized-changes.json

# Verify all emergency access has been revoked
./pfctl break-glass verify --ticket-id $BREAK_GLASS_ID
```

## Post-Break-Glass Procedures

### 1. Incident Documentation

```bash
# Complete break-glass ticket
./pfctl break-glass complete \
  --ticket-id $BREAK_GLASS_ID \
  --summary "Emergency operations completed successfully" \
  --actions-taken "Database restoration, emergency access granted" \
  --lessons-learned "Need better monitoring for early detection"

# Generate break-glass report
./pfctl break-glass report \
  --ticket-id $BREAK_GLASS_ID \
  --output break-glass-report-$(date +%Y%m%d-%H%M%S).pdf
```

### 2. Audit Review

```bash
# Review all break-glass activities
./pfctl audit review \
  --since "break-glass-start" \
  --until "break-glass-end" \
  --output break-glass-audit-$(date +%Y%m%d-%H%M%S).json

# Analyze audit logs for any anomalies
./pfctl audit analyze \
  --file break-glass-audit-$(date +%Y%m%d-%H%M%S).json \
  --output anomaly-report-$(date +%Y%m%d-%H%M%S).json
```

### 3. Process Improvements

```bash
# Update break-glass procedures
git add docs/runbooks/break-glass.md
git commit -m "Update break-glass procedures based on incident $BREAK_GLASS_ID"

# Schedule post-incident review
./pfctl meeting schedule \
  --topic "Break-Glass Incident Review" \
  --date "$(date -d '+1 week')" \
  --attendees "security-team,admin-team,business-owners"
```

## Break-Glass Monitoring

### 1. Real-Time Monitoring

```bash
# Monitor break-glass activities in real-time
kubectl logs -n production -l app=sidecar-watcher -f | \
  grep -E "(BREAK_GLASS|EMERGENCY|BYPASS)" | \
  tee break-glass-live-$(date +%Y%m%d-%H%M%S).log

# Monitor system access
./pfctl monitor --env production --watch --filter "break-glass"
```

### 2. Alert Configuration

```bash
# Configure break-glass alerts
./pfctl monitoring add-alert \
  --rule "break_glass_activated" \
  --condition "break_glass_mode == true" \
  --severity "critical" \
  --notification "immediate"

# Configure expiration warnings
./pfctl monitoring add-alert \
  --rule "break_glass_expiring" \
  --condition "break_glass_ttl < 300" \
  --severity "warning" \
  --notification "5min"
```

### 3. Compliance Monitoring

```bash
# Monitor compliance during break-glass
./pfctl compliance monitor \
  --env production \
  --mode "break-glass" \
  --output compliance-report-$(date +%Y%m%d-%H%M%S).json

# Track policy violations during break-glass
./pfctl violations track \
  --env production \
  --since "break-glass-start" \
  --output violations-$(date +%Y%m%d-%H%M%S).json
```

## Success Criteria

- [ ] Break-glass mode activated with proper authorization
- [ ] Emergency operations completed successfully
- [ ] Break-glass mode disabled within TTL
- [ ] Normal policy enforcement restored
- [ ] All emergency access revoked
- [ ] Audit trail complete and reviewed
- [ ] Incident documented and lessons learned captured
- [ ] Process improvements implemented
- [ ] Stakeholders notified of resolution
- [ ] Compliance requirements met

## Emergency Contacts

### Security Team
- **Lead**: security-lead@company.com
- **On-call**: +1-555-0123
- **Escalation**: +1-555-0124

### System Administration
- **Lead**: admin-lead@company.com
- **On-call**: +1-555-0125
- **Escalation**: +1-555-0126

### Business Owners
- **Primary**: business-owner@company.com
- **Backup**: business-backup@company.com
- **Escalation**: +1-555-0127

## Important Notes

1. **Break-glass mode is a last resort** - always attempt normal procedures first
2. **Time limit is strict** - maximum 2 hours, no extensions without C-level approval
3. **All activities are audited** - no exceptions to logging requirements
4. **Immediate rollback required** - normal operations must resume as soon as possible
5. **Post-incident review mandatory** - all break-glass incidents require formal review
6. **Compliance implications** - break-glass usage may affect compliance certifications
7. **Stakeholder notification** - all break-glass incidents must be reported to stakeholders
8. **Process improvement required** - each break-glass incident should lead to process improvements
