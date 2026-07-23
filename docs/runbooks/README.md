# Operational Runbooks

This directory contains operational procedures and runbooks for managing Provability-Fabric deployments in production environments.

## Available Runbooks

### Core Operations
- **[Deployment](deployment.md)** - Standard deployment procedures and best practices
- **[Incident Response](incident-response.md)** - Incident management and resolution procedures
- **[Break Glass](break-glass.md)** - Emergency access procedures for critical situations
- **[Operations](operations.md)** - General operations, triage, and escalation

### Specialized
- **[Surge](surge.md)** - Surge and backpressure handling
- **[Approvals](approvals.md)** - Human approval workflows
- **[Live ops secrets](live-ops-secrets.md)** - Secret-gated DR / publish / revocation / edge-load dispatch

Historical rollback / GuardTrip-bot procedures (removed in-tree controller and ops CRDs): [runbook-rollback.md](../internal/archive/runbook-rollback.md), [runbook-guardtrip-triage.md](../internal/archive/runbook-guardtrip-triage.md).

## Runbook Structure

Each runbook follows a consistent structure:

1. **Overview** - Brief description of the procedure
2. **Prerequisites** - Required access, tools, and conditions
3. **Procedure** - Step-by-step execution instructions
4. **Verification** - How to confirm successful execution
5. **Troubleshooting** - Common issues and solutions
6. **References** - Related documentation and resources

## Usage Guidelines

### Before Executing Runbooks

- Ensure you have the necessary permissions and access
- Verify the current system state and context
- Review any recent changes or incidents
- Have a backup plan ready

### During Execution

- Follow steps exactly as documented
- Document any deviations or unexpected behavior
- Keep stakeholders informed of progress
- Maintain detailed logs of all actions

### After Execution

- Verify all expected outcomes
- Update relevant documentation
- Conduct post-mortem if issues occurred
- Update monitoring and alerting as needed

## Emergency Procedures

For critical incidents requiring immediate response:

1. **Assess Impact** - Determine scope and severity
2. **Engage Team** - Notify appropriate personnel
3. **Execute Runbook** - Follow documented procedures
4. **Monitor Progress** - Track resolution status
5. **Communicate Status** - Keep stakeholders updated

## Maintenance

Runbooks are living documents that should be:

- **Regularly Reviewed** - Updated based on lessons learned
- **Tested Periodically** - Validated through drills and exercises
- **Version Controlled** - Tracked with clear change history
- **Accessible** - Available to all operational personnel

## Contributing

When updating runbooks:

- Test procedures in non-production environments
- Include clear success criteria and verification steps
- Document any assumptions or dependencies
- Review with relevant team members
- Update related documentation and procedures
