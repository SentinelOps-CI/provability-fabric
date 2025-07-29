# Manual Rollback Runbook

This runbook provides step-by-step procedures for manual rollback operations in Provability-Fabric.

## Overview

The automated incident response system can trigger rollbacks automatically, but manual intervention may be required in certain scenarios:

- False positive incidents
- System component failures
- Emergency situations
- Testing and validation

## Prerequisites

- `kubectl` access to the cluster
- Flux CLI installed (`flux` command available)
- Access to the GitOps repository
- Rollback CRD installed (`kubectl get crd rollbacks.ops.prov-fabric.io`)

## Quick Reference

| Component       | Command                                          | Description                  |
| --------------- | ------------------------------------------------ | ---------------------------- |
| Check Rollbacks | `kubectl get rollbacks`                          | List all rollback operations |
| Manual Rollback | `kubectl apply -f rollback.yaml`                 | Create manual rollback       |
| Check Status    | `kubectl describe rollback <name>`               | Get detailed status          |
| View Logs       | `kubectl logs -f deployment/rollback-controller` | Monitor controller           |

## Emergency Rollback Procedure

### Step 1: Assess the Situation

```bash
# Check current system status
kubectl get pods -A
kubectl get helmreleases -A
kubectl get rollbacks

# Check recent incidents
kubectl logs deployment/incident-bot -n monitoring --tail=100
```

### Step 2: Determine Rollback Target

```bash
# Get current Helm release information
kubectl get helmrelease provability-fabric -o yaml

# List available revisions
helm history provability-fabric -n flux-system

# Identify the last stable release
kubectl get helmrelease provability-fabric -o jsonpath='{.status.history[1].revision}'
```

### Step 3: Create Manual Rollback

Create a rollback manifest:

```yaml
apiVersion: ops.prov-fabric.io/v1alpha1
kind: Rollback
metadata:
  name: manual-rollback-$(date +%s)
  namespace: flux-system
spec:
  targetRelease: "v0.1.0" # Replace with actual stable version
  reason: "manual_emergency"
  capsuleHash: "sha256:emergency1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
  tenantId: "emergency-tenant"
```

Apply the rollback:

```bash
kubectl apply -f rollback.yaml
```

### Step 4: Monitor Rollback Progress

```bash
# Watch rollback status
kubectl get rollbacks -w

# Check detailed status
kubectl describe rollback manual-rollback-$(date +%s)

# Monitor controller logs
kubectl logs -f deployment/rollback-controller -n flux-system
```

### Step 5: Verify Rollback Completion

```bash
# Check Helm release status
kubectl get helmrelease provability-fabric -o yaml

# Verify service health
kubectl get pods -A
kubectl get svc -A

# Test critical endpoints
curl -f https://api.provability-fabric.org/health
curl -f https://api.provability-fabric.org/metrics
```

## False Positive Handling

### Scenario: Automated Rollback Triggered Incorrectly

1. **Immediate Actions**

   ```bash
   # Pause incident-bot temporarily
   kubectl scale deployment incident-bot -n monitoring --replicas=0

   # Check what triggered the rollback
   kubectl logs deployment/incident-bot -n monitoring --tail=50
   ```

2. **Investigate the Incident**

   ```bash
   # Check GuardTrip events
   kubectl exec deployment/incident-bot -n monitoring -- curl -s http://localhost:3000/api/v1/events

   # Check metrics
   kubectl exec deployment/incident-bot -n monitoring -- curl -s http://localhost:3000/metrics
   ```

3. **Resume Normal Operation**

   ```bash
   # Restart incident-bot
   kubectl scale deployment incident-bot -n monitoring --replicas=1

   # Verify it's running
   kubectl wait --for=condition=Available deployment/incident-bot -n monitoring
   ```

## System Component Failures

### Rollback Controller Failure

```bash
# Check controller status
kubectl get deployment rollback-controller -n flux-system

# Restart controller
kubectl rollout restart deployment/rollback-controller -n flux-system

# Verify recovery
kubectl wait --for=condition=Available deployment/rollback-controller -n flux-system
```

### Flux Controller Issues

```bash
# Check Flux status
flux get sources
flux get helmreleases

# Reconcile manually
flux reconcile source git flux-system
flux reconcile helmrelease provability-fabric
```

## Testing and Validation

### Create Test Rollback

```yaml
apiVersion: ops.prov-fabric.io/v1alpha1
kind: Rollback
metadata:
  name: test-rollback-$(date +%s)
  namespace: flux-system
spec:
  targetRelease: "v0.1.0"
  reason: "test_validation"
  capsuleHash: "sha256:test1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
  tenantId: "test-tenant"
```

### Validate Rollback Process

```bash
# Apply test rollback
kubectl apply -f test-rollback.yaml

# Monitor process
kubectl get rollbacks -w

# Verify completion
kubectl get rollbacks -o jsonpath='{.items[0].status.phase}'
```

## Troubleshooting

### Common Issues

1. **Rollback Stuck in Pending**

   ```bash
   # Check controller logs
   kubectl logs deployment/rollback-controller -n flux-system

   # Check CRD status
   kubectl get crd rollbacks.ops.prov-fabric.io
   ```

2. **Helm Release Not Found**

   ```bash
   # Verify Helm release exists
   kubectl get helmreleases -A

   # Check Flux source
   flux get sources git
   ```

3. **Permission Denied**

   ```bash
   # Check RBAC
   kubectl auth can-i create rollbacks
   kubectl auth can-i update helmreleases

   # Verify service account
   kubectl get serviceaccount rollback-controller -n flux-system
   ```

### Debug Commands

```bash
# Get detailed rollback information
kubectl get rollbacks -o yaml

# Check events
kubectl get events --sort-by=.metadata.creationTimestamp

# Verify CRD schema
kubectl explain rollback.spec

# Check controller metrics
kubectl port-forward deployment/rollback-controller 8080:8080 -n flux-system
curl http://localhost:8080/metrics
```

## Related Documentation

- [Rollback CRD Specification](ops/crd/rollback.yaml)
- [Flux Integration](ops/flux/rollback-controller.yaml)
- [Incident Response Architecture](../architecture/incident-response.md)
- [Automated Rollback Guide](../guides/automated-rollback.md)

## Emergency Contacts

- **On-Call Engineer**: [Contact Information]
- **SRE Team**: [Contact Information]
- **Security Team**: [Contact Information]

## Post-Incident Actions

1. **Document the Incident**

   - Record what triggered the rollback
   - Note any manual interventions
   - Document lessons learned

2. **Update Procedures**

   - Revise this runbook if needed
   - Update automation thresholds
   - Improve monitoring and alerting

3. **Follow-up**
   - Schedule incident review meeting
   - Update runbooks and procedures
   - Implement preventive measures
