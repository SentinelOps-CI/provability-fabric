# Multi-Tenant Ledger & RBAC

This document describes the multi-tenant implementation of Provability-Fabric's ledger service, including tenant isolation, RBAC (Role-Based Access Control), and authentication.

## Architecture Overview

The multi-tenant system provides:

- **Tenant Isolation**: Each tenant's data is completely isolated from other tenants
- **JWT Authentication**: Auth0-based authentication with tenant claims
- **Row-Level Security**: PostgreSQL RLS policies enforce data isolation
- **RBAC**: Kubernetes namespaces and role bindings for tenant resources

## Components

### 1. Database Schema

The ledger database includes a `Tenant` model with foreign key relationships:

```sql
model Tenant {
  id          String   @id @default(cuid())
  name        String   @unique
  auth0Id     String   @unique
  createdAt   DateTime @default(now())
  updatedAt   DateTime @updatedAt
  capsules    Capsule[]
  premiumQuotes PremiumQuote[]
}
```

### 2. Row-Level Security (RLS)

PostgreSQL RLS policies ensure tenant isolation:

```sql
-- Enable RLS on all tables
ALTER TABLE "Tenant" ENABLE ROW LEVEL SECURITY;
ALTER TABLE "Capsule" ENABLE ROW LEVEL SECURITY;
ALTER TABLE "PremiumQuote" ENABLE ROW LEVEL SECURITY;

-- Tenant isolation policies
CREATE POLICY "tenant_isolation_capsule_select" ON "Capsule"
    FOR SELECT USING (tenant_id = current_setting('app.current_tenant_id', true));
```

### 3. Authentication Middleware

JWT validation and tenant context setting:

```typescript
// Auth0 JWT validation
export const authMiddleware = jwt({
  secret: jwksRsa.expressJwtSecret({
    jwksUri: `https://${process.env.AUTH0_DOMAIN}/.well-known/jwks.json`,
  }),
  audience: process.env.AUTH0_AUDIENCE,
  issuer: `https://${process.env.AUTH0_DOMAIN}/`,
  algorithms: ["RS256"],
});

// Tenant validation and context setting
export const tenantMiddleware = async (req, res, next) => {
  const tenant = await prisma.tenant.findUnique({
    where: { auth0Id: req.user.tid },
  });

  // Set PostgreSQL tenant context for RLS
  await prisma.$executeRaw`SELECT set_tenant_context(${tenant.id})`;
};
```

## Setup Instructions

### 1. Create a New Tenant

Use the CLI to create a new tenant with onboarding bundle:

```bash
pf tenant create my-tenant \
  --auth0-domain my-tenant.auth0.com \
  --client-id abc123def456 \
  --client-secret xyz789secret
```

This generates:

- Tenant configuration in `tenants/my-tenant/tenant.json`
- Kubernetes manifests in `tenants/my-tenant/k8s-*.yaml`
- Signed tenant configuration with Cosign

### 2. Apply Kubernetes Resources

```bash
kubectl apply -f tenants/my-tenant/k8s-*.yaml
```

### 3. Configure Auth0 Application

1. Create a new Auth0 application
2. Configure callbacks and logout URLs
3. Add custom claims for tenant ID (`tid`)

### 4. Import Tenant to Database

```sql
INSERT INTO "Tenant" (id, name, auth0_id, created_at, updated_at)
VALUES ('tenant-id', 'my-tenant', 'auth0-tenant-id', NOW(), NOW());
```

## API Usage

### GraphQL Endpoints

All GraphQL endpoints require authentication and tenant context:

```graphql
# Query tenant's capsules
query {
  capsules {
    id
    hash
    tenantId
    riskScore
  }
}

# Create capsule (tenant-scoped)
mutation {
  createCapsule(hash: "abc123", specSig: "sig", riskScore: 0.5) {
    id
    hash
    tenantId
  }
}
```

### REST Endpoints

Tenant-scoped REST endpoints:

```bash
# Get tenant's capsules
GET /tenant/{tid}/capsules
Authorization: Bearer <jwt-token>

# Get premium quote for capsule
GET /tenant/{tid}/quote/{hash}
Authorization: Bearer <jwt-token>
```

## Security Features

### 1. Tenant Isolation

- Each tenant can only access their own data
- RLS policies enforce isolation at the database level
- JWT claims must include valid tenant ID

### 2. SQL Injection Prevention

- JWT claims are validated before database access
- Malicious tenant IDs in JWT are rejected
- Parameterized queries prevent injection

### 3. RBAC Enforcement

- Kubernetes namespaces isolate tenant resources
- Role bindings control access to tenant namespaces
- Admission controller validates tenant permissions

## Testing

### Manual Testing

Run the tenant isolation test:

```bash
python tests/rbac/test_tenant_isolation.py
```

### Automated Testing

The RBAC test workflow runs on every PR:

```yaml
# .github/workflows/rbac-test.yaml
- Tests tenant isolation between Tenant A and B
- Verifies SQL injection prevention
- Ensures RLS policies are enforced
```

## Troubleshooting

### Common Issues

1. **401 Unauthorized**: Check JWT token and Auth0 configuration
2. **403 Forbidden**: Verify tenant exists and JWT claims are correct
3. **Database errors**: Ensure RLS policies are applied correctly

### Debug Commands

```bash
# List configured tenants
pf tenant list

# Check tenant configuration
cat tenants/my-tenant/tenant.json

# Verify RLS policies
psql -d provability_fabric -c "SELECT * FROM pg_policies WHERE tablename = 'Capsule';"
```

## Monitoring

### Metrics

- Tenant API usage per tenant
- Authentication failures
- RLS policy violations

### Alerts

- Failed tenant authentication
- Cross-tenant access attempts
- SQL injection attempts

## Compliance

The multi-tenant implementation supports:

- **SOC 2**: Tenant data isolation
- **GDPR**: Data residency and access controls
- **HIPAA**: PHI isolation between tenants
- **FedRAMP**: Multi-tenant security controls
