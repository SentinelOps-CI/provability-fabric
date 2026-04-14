# Human Approval Workflows

## Overview

The Provability Fabric implements a comprehensive human approval system for high-risk operations. This system ensures that potentially dangerous tool calls are reviewed by authorized personnel before execution.

## Risk Thresholds

### Risk Score Categories

| Risk Score | Category | Action Required |
|------------|----------|-----------------|
| 0.0 - 0.3 | Low Risk | Auto-approved (if configured) |
| 0.3 - 0.7 | Medium Risk | Single approver required |
| 0.7 - 0.9 | High Risk | Multiple approvers required |
| 0.9 - 1.0 | Critical Risk | Security admin approval required |

### Risk Factors

The risk score is calculated based on multiple factors:

1. **Tool Type**: Some tools are inherently riskier than others
2. **Resource Access**: Access to sensitive data increases risk
3. **User Context**: User's role and permissions affect risk
4. **Session History**: Previous violations increase risk
5. **Time of Day**: Unusual hours may increase risk
6. **Geographic Location**: Unusual locations may increase risk

## Approval Workflow

### 1. Request Creation

When a tool call exceeds the risk threshold:

1. **Request Generation**: System creates an approval request
2. **Notification**: Relevant approvers are notified
3. **Documentation**: Request details are logged for audit

### 2. Approval Process

#### Single Approver (Medium Risk)
- Any authorized approver can approve
- 30-minute timeout
- Email/Slack notification

#### Multiple Approvers (High Risk)
- Requires approval from 2+ approvers
- 60-minute timeout
- Escalation to security team if not approved

#### Security Admin (Critical Risk)
- Requires security admin approval
- 120-minute timeout
- Immediate escalation

### 3. Approval Decision

#### Approved Requests
- Tool call proceeds with execution
- Approval details logged
- Audit trail maintained

#### Denied Requests
- Tool call blocked
- Reason for denial logged
- User notified of denial

#### Expired Requests
- Automatically denied after timeout
- System logs expiration
- User must create new request

## Approver Roles and Permissions

### Security Admin
- **Permissions**: All risk levels, all tools, all tenants
- **Responsibilities**: Critical risk approvals, security policy enforcement
- **Contact**: security-admin@company.com

### System Admin
- **Permissions**: High risk and below, system tools, all tenants
- **Responsibilities**: System maintenance approvals
- **Contact**: sysadmin@company.com

### Risk Manager
- **Permissions**: Medium risk and below, business tools, specific tenants
- **Responsibilities**: Business risk assessment
- **Contact**: risk-manager@company.com

### Compliance Officer
- **Permissions**: Medium risk and below, compliance tools, specific tenants
- **Responsibilities**: Regulatory compliance approvals
- **Contact**: compliance@company.com

### Team Lead
- **Permissions**: Low risk, team-specific tools, team tenants
- **Responsibilities**: Team operation approvals
- **Contact**: team-lead@company.com

### Developer
- **Permissions**: Low risk, development tools, development tenants
- **Responsibilities**: Development workflow approvals
- **Contact**: dev-team@company.com

## Notification Channels

### Email Notifications
- **Recipients**: Authorized approvers
- **Content**: Request details, risk assessment, approval link
- **Frequency**: Immediate upon request creation

### Slack Notifications
- **Channels**: #security-approvals, #team-approvals
- **Content**: Request summary with approval buttons
- **Frequency**: Immediate upon request creation

### Webhook Notifications
- **Recipients**: External systems (Jira, ServiceNow)
- **Content**: Structured JSON payload
- **Frequency**: Immediate upon request creation

## Emergency Procedures

### Emergency Approvals
- **Trigger**: Critical system failure or security incident
- **Process**: Security admin can override normal workflow
- **Documentation**: Emergency approval must be documented with reason

### Escalation Procedures
1. **Level 1**: Team lead notification (5 minutes)
2. **Level 2**: Security team notification (15 minutes)
3. **Level 3**: CISO notification (30 minutes)

## Audit and Compliance

### Approval Logging
All approval activities are logged with:
- Request ID and details
- Approver ID and timestamp
- Approval decision and reasoning
- Risk score and factors

### Compliance Reporting
Monthly reports include:
- Approval volume by risk level
- Average approval time
- Denial rate and reasons
- Escalation frequency

### Retention Policy
- **Approval Records**: 7 years
- **Denial Records**: 7 years
- **Audit Logs**: 10 years
- **Compliance Reports**: 10 years

## Configuration

### Risk Thresholds
```yaml
approval_config:
  low_risk_threshold: 0.3
  medium_risk_threshold: 0.7
  high_risk_threshold: 0.9
  critical_risk_threshold: 1.0
```

### Timeout Settings
```yaml
timeout_config:
  low_risk_timeout_minutes: 30
  medium_risk_timeout_minutes: 30
  high_risk_timeout_minutes: 60
  critical_risk_timeout_minutes: 120
```

### Notification Settings
```yaml
notification_config:
  channels:
    - email
    - slack
    - webhook
  escalation_enabled: true
  auto_approve_low_risk: false
```

## Troubleshooting

### Common Issues

#### Request Not Appearing
1. Check notification settings
2. Verify approver permissions
3. Check system logs for errors

#### Approval Not Processing
1. Verify approver authentication
2. Check request status
3. Validate approval permissions

#### Timeout Issues
1. Check system time synchronization
2. Verify timeout configuration
3. Review system performance

### Debug Commands

```bash
# Check approval status
curl -X GET "http://localhost:8083/api/approval-requests/{request_id}"

# List pending requests
curl -X GET "http://localhost:8083/api/approval-requests"

# Check approver permissions
curl -X GET "http://localhost:8083/api/approvers/{approver_id}"

# View approval history
curl -X GET "http://localhost:8083/api/approval-history?limit=100"
```

## Best Practices

### For Approvers
1. **Review Thoroughly**: Always review request details before approving
2. **Document Decisions**: Provide clear reasoning for approvals/denials
3. **Escalate When Uncertain**: When in doubt, escalate to security team
4. **Respond Promptly**: Approve or deny within timeout period

### For Requesters
1. **Provide Context**: Include clear business justification
2. **Plan Ahead**: Submit requests well before needed
3. **Follow Up**: Check status if approval is delayed
4. **Respect Decisions**: Accept denials and adjust approach

### For Administrators
1. **Monitor Volume**: Track approval request patterns
2. **Adjust Thresholds**: Fine-tune risk thresholds based on patterns
3. **Train Approvers**: Regular training on approval procedures
4. **Review Policies**: Periodic review of approval policies

## Integration Points

### External Systems
- **Jira**: Issue creation for approvals
- **ServiceNow**: Ticket management
- **Slack**: Real-time notifications
- **Email**: Formal notifications

### Internal Systems
- **Kernel**: Risk assessment integration
- **Sidecar**: Enforcement integration
- **Ledger**: Audit trail integration
- **Evidence**: Compliance documentation 