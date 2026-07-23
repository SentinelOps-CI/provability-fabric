# Cross-Region Disaster Recovery

This document describes the cross-region disaster recovery (DR) implementation for Provability-Fabric, which provides zero-downtime failover capabilities and automated testing.

## Architecture Overview

The DR implementation consists of three main components:

1. **Primary RDS Instance** (us-west-2) - Main database serving production traffic
2. **Secondary RDS Instance** (us-east-1) - Read replica for failover
3. **Route 53 Failover DNS** - Automatic traffic routing based on health checks
4. **S3 Cross-Region Replication** - Backup data replication

```mermaid
graph TD
    A[Client] --> B[Route 53 DNS]
    B --> C{Health Check}
    C -->|Primary Healthy| D[Primary RDS<br/>us-west-2]
    C -->|Primary Unhealthy| E[Secondary RDS<br/>us-east-1]
    F[S3 Primary Bucket<br/>us-west-2] --> G[S3 Secondary Bucket<br/>us-east-1]
    H[Blue-Green Migration<br/>Script] --> I[Zero-Downtime<br/>Deployments]
```

## Infrastructure Components

In-repo Terraform under `ops/terraform/` was removed. CI-local DR proof is
`scripts/dr/` plus [`.github/workflows/dr-cross.yaml`](../../.github/workflows/dr-cross.yaml)
(moto by default; live AWS only via `workflow_dispatch`). Production multi-region
layout remains an operator concern outside this repository.

### Key Features

- **CI-local proof**: moto/boto3 smoke for cross-region S3 / Route 53 shapes
- **Blue-green migrations**: `scripts/db/blue_green_migrate.sh`
- **Zero-downtime upgrades**: `scripts/zero-downtime-upgrade.sh` (when wired to real ALBs)

## Blue-Green Migration Script

The `scripts/db/blue_green_migrate.sh` script enables zero-downtime database migrations:

### Usage

```bash
# Dry run to see the plan
./scripts/db/blue_green_migrate.sh \
  --dry-run \
  --blue-db-url postgresql://user:pass@blue-db:5432/db \
  --green-db-url postgresql://user:pass@green-db:5432/db \
  --dns-zone Z1234567890ABC \
  --dns-record db.provability-fabric.org

# Execute migration (requires --confirm; applies green schema + Route53 UPSERT)
./scripts/db/blue_green_migrate.sh \
  --confirm \
  --blue-db-url postgresql://user:pass@blue-db:5432/db \
  --green-db-url postgresql://user:pass@green-db:5432/db \
  --dns-zone Z1234567890ABC \
  --dns-record db.provability-fabric.org \
  --smoke-test-url https://api.provability-fabric.org/health

# Live DR CI uses --verify-only (connectivity + Route53 read; no mutations)
```

### Migration Process

1. **Connectivity Check**: Verify both blue and green databases are accessible
2. **Migration Application**: Apply Prisma migrations to green database
3. **Health Verification**: Verify green database has expected schema and data
4. **Smoke Tests**: Run health checks against the application
5. **DNS Flip**: Update Route 53 to point to green database
6. **Final Verification**: Confirm application is working with green database

## Automated Testing

The `.github/workflows/dr-cross.yaml` workflow provides DR testing with a hard split between CI-local and live AWS:

| Path | Trigger | Behavior |
|------|---------|----------|
| **Moto gate** | push / PR / Monday schedule / `workflow_dispatch` `mode=moto` | Local moto S3 + Route53 + `blue_green_migrate.sh --dry-run`. Report sets `live_aws: false`. Inventory-safe. |
| **Live AWS** | `workflow_dispatch` `mode=live` only | Real RDS/Route53/S3. Fail-closed without secrets. Report sets `live_aws: true`. |

Adding AWS secrets must **not** convert the Monday schedule into live DR.

### Live test scenarios (`mode=live`)

1. **Normal Operation**: Verify primary database and sidecar are healthy
2. **Failover**: Disable primary health check and verify DNS flips to secondary
3. **Recovery**: Re-enable health check and verify DNS returns to primary
4. **Replication Verification**: Put object in primary dumps bucket; assert secondary replica
5. **Blue-green verify**: `blue_green_migrate.sh --verify-only` against live endpoints (connectivity + Route53 read; no DNS flip)

### Test Metrics

- **Maximum Service Disruption**: < 90 seconds
- **DNS Failover Time**: < 60 seconds
- **S3 Replication Latency**: < 60 seconds

### Schedule vs dispatch

- **Schedule (Monday 09:00 UTC):** moto gate only.
- **Live:** `gh workflow run dr-cross.yaml -f mode=live` (see [live-ops-secrets.md](../runbooks/live-ops-secrets.md)).

## Monitoring and Alerts

### Health Checks

- **Database Connectivity**: PostgreSQL connection health
- **Sidecar Heartbeat**: Application health endpoint
- **DNS Resolution**: Route 53 record availability
- **S3 Replication**: Cross-region backup verification

### Alerting

- Failed health checks trigger immediate notifications
- Weekly test failures generate detailed reports
- Service disruption exceeding 90 seconds triggers alerts

## Configuration

### Required Secrets (live `mode=live` only)

These are **not** required for the moto gate. Live dispatch hard-fails if any are missing:

- `AWS_ACCESS_KEY_ID`: AWS access key for infrastructure management
- `AWS_SECRET_ACCESS_KEY`: AWS secret key for infrastructure management
- `DNS_ZONE_ID`: Route 53 hosted zone ID
- `HEALTH_CHECK_ID`: Route 53 health check ID

RDS endpoints are discovered at runtime (`provability-fabric-primary` in `PRIMARY_REGION`, `provability-fabric-secondary` in `SECONDARY_REGION`).

### Environment Variables

- `PRIMARY_REGION`: us-west-2
- `SECONDARY_REGION`: us-east-1
- `DNS_RECORD`: db.provability-fabric.org

## Disaster Recovery Procedures

### Automatic Failover

1. Route 53 health check detects primary database failure
2. DNS automatically switches to secondary database
3. Application continues serving traffic from secondary
4. Monitoring alerts notify operations team

### Manual Failover

```bash
# Disable primary health check
aws route53 update-health-check \
  --health-check-id $HEALTH_CHECK_ID \
  --disabled

# Verify DNS failover
dig db.provability-fabric.org

# Re-enable primary health check when ready
aws route53 update-health-check \
  --health-check-id $HEALTH_CHECK_ID \
  --no-disabled
```

### Recovery Procedures

1. **Primary Database Recovery**: Restore primary database from backup
2. **Data Synchronization**: Ensure secondary has latest data
3. **Health Check Restoration**: Re-enable primary health check
4. **DNS Verification**: Confirm traffic routes back to primary
5. **Application Verification**: Run smoke tests to confirm functionality

## Performance Considerations

### Latency

- **Primary Region**: ~5ms latency for us-west-2 clients
- **Secondary Region**: ~50ms latency for us-west-2 clients
- **Failover Time**: < 90 seconds total disruption

### Costs

- **RDS Instances**: Primary + read replica
- **S3 Storage**: Cross-region replication storage
- **Route 53**: Health checks and DNS queries
- **Data Transfer**: Cross-region replication bandwidth

## Security

### Network Security

- **VPC Isolation**: Separate VPCs in each region
- **Security Groups**: Database access controls
- **SSL/TLS**: Encrypted database connections
- **IAM Roles**: Least privilege access

### Data Protection

- **Encryption at Rest**: RDS and S3 encryption
- **Encryption in Transit**: SSL/TLS for all connections
- **Backup Encryption**: S3 bucket encryption
- **Access Controls**: IAM policies and security groups

## Troubleshooting

### Common Issues

1. **DNS Failover Not Working**

   - Check Route 53 health check configuration
   - Verify database connectivity
   - Review security group rules

2. **Replication Lag**

   - Monitor RDS replication lag metrics
   - Check network connectivity between regions
   - Review database load and performance

3. **Migration Script Failures**
   - Verify database credentials
   - Check Prisma migration files
   - Review DNS zone permissions

### Debugging Commands

```bash
# Check database connectivity
pg_isready -h $DB_HOST -p 5432

# Verify DNS resolution
dig db.provability-fabric.org

# Test sidecar health
curl -f https://sidecar.provability-fabric.org/health

# Check S3 replication
aws s3 ls s3://bucket-name/ --region us-east-1
```

## Compliance and Auditing

### Audit Trail

- **Terraform State**: Infrastructure changes tracked in state files
- **Route 53 Logs**: DNS change history
- **RDS Logs**: Database access and performance logs
- **S3 Access Logs**: Backup access tracking

### Compliance Features

- **Data Residency**: Primary data in us-west-2
- **Backup Retention**: 7-day backup retention
- **Encryption**: All data encrypted at rest and in transit
- **Access Logging**: Comprehensive audit trails

## Future Enhancements

### Planned Improvements

1. **Multi-Region Application Deployment**: Deploy application in both regions
2. **Global Load Balancing**: Use CloudFront for global distribution
3. **Automated Recovery**: Self-healing infrastructure components
4. **Enhanced Monitoring**: Real-time DR metrics dashboard

### Scalability Considerations

- **Read Replicas**: Add additional read replicas for scaling
- **Sharding**: Database sharding for horizontal scaling
- **Caching**: Redis cluster for improved performance
- **CDN**: Global content delivery network

## Support and Maintenance

### Regular Maintenance

- **Weekly DR Tests**: Automated failover testing
- **Monthly Backup Verification**: Restore testing procedures
- **Quarterly Security Reviews**: Access control audits
- **Annual DR Drills**: Full disaster recovery simulation
