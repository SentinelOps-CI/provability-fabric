# SentinelOps Platform

A complete, modular platform that converts natural-language policies into formal specifications, compiles them to provable monitors, enforces them at runtime with deterministic egress, and emits machine-verifiable evidence with deterministic replay.

## Quick Start

### Option 1: One-Command Demo

```bash
make demo-up
```

This starts the complete platform with the Verifiable MCP Fraud demo.

### Option 2: Quick Demo Script

```bash
./scripts/quick-demo.sh
```

Runs a guided demo showcasing all platform capabilities.

### Option 3: Manual Setup

```bash
# Start platform services
./scripts/start-platform.sh

# Setup demo data
make demo-setup

# Run demo
cd demos/verifiable-mcp-fraud && npm run dev:agent
```

## Platform Architecture

### Core Services

1. **Spec Service** (port 8001) - English → ActionDSL conversion, schema validation, policy versioning
2. **Proof Service** (port 8002) - Lean obligations, proof artifacts caching, Morph integration
3. **Build Orchestrator** (port 8003) - ActionDSL → DFA compilation, signed policy builds
4. **Evidence Service** (port 8004) - CERT-V1 storage, validation, search, packet builder
5. **Replay Service** (port 8005) - TRACE-REPLAY-KIT integration, deterministic replay
6. **Runtime Sidecar** (port 8006) - Permissions, IFC labels, deterministic egress, CERT-V1 emission
7. **API Gateway** (port 8000) - Unified API routing and load balancing

### User Interfaces

- **Console UI** (port 3000) - Comprehensive web interface with tabs for Policies, Runtime, Evidence, Replay, Compliance, Settings
- **Grafana** (port 3002) - Observability dashboards for latency, cert health, replay coverage, RLS isolation
- **Demo App** (port 3001) - Verifiable MCP Fraud detection demo

## Target User Workflows

### Developer / Agent Owner

```bash
# Write policy in English
echo "Only FraudService may call /score endpoint" > policy.md

# Compile → Build → Prove → Deploy
so policy compile --in policy.md --out build/
so policy prove --build build/
so policy build --build build/
so deploy --build build/ --epoch rotate

# During incidents
so cert verify evidence/certs/*.json
so replay run <decision-id> --open
so packet make <decision-id> --out artifacts/
```

### Security / Compliance (CISO, Risk, Auditor)

1. Browse certificates in Console UI → Evidence tab
2. Filter by policy/tenant/time range
3. Export compliance packets
4. Run trace-replay on sampled decisions
5. Archive evidence in GRC systems

### SRE / Platform Engineer

1. Monitor SLOs in Console UI → Runtime tab
2. Set up alerts for cert validation failures, replay match rates
3. Automate CI gates with SDK
4. Roll back policy epochs in seconds
5. Fetch precise artifacts for postmortems

## API Reference

### Policy Lifecycle

```bash
POST /api/v1/policy/compile     # English → ActionDSL
POST /api/v1/proofs/run         # Generate Lean proofs
POST /api/v1/policy/build       # ActionDSL → DFA
POST /api/v1/runtime/deploy     # Deploy to runtime
POST /api/v1/runtime/epoch/rotate # Rotate epochs
```

### Evidence & Replay

```bash
GET /api/v1/evidence/cert/:id   # Get CERT-V1
POST /api/v1/evidence/search    # Search certificates
POST /api/v1/replay             # Start replay
GET /api/v1/replay/:jobId       # Get replay status
GET /api/v1/compliance/packet/:id # Download compliance packet
```

### Runtime & Monitoring

```bash
GET /api/v1/runtime/slo         # Get SLO metrics
GET /health                     # Platform health
GET /metrics                    # Prometheus metrics
```

## SDK Usage

### TypeScript

```typescript
import { SentinelOpsClient } from '@sentinelops/platform-sdk';

const client = new SentinelOpsClient('http://localhost:8000');

// Full policy workflow
const result = await client.fullPolicyWorkflow(
  'Only FraudService may call /score endpoint',
  'fraud-policy-v1'
);

// Verify certificates
const valid = await client.verifyCert(certificate);

// Start replay
const replay = await client.startReplay({ decision_id: 'txn_123' });
const status = await client.waitForReplay(replay.job_id);
```

### Python

```python
from sentinelops import SentinelOpsClient

client = SentinelOpsClient('http://localhost:8000')

# Full policy workflow
result = client.full_policy_workflow(
    'Only FraudService may call /score endpoint',
    'fraud-policy-v1'
)

# CI helpers
assert client.assert_certs_valid(certificates)
assert client.assert_low_view(replay_id, threshold=0.999)
```

### Go

```go
import "github.com/sentinelops/platform-sdk-go"

client := sentinelops.NewClient("http://localhost:8000", "")

// Full workflow
result, err := client.FullPolicyWorkflow(ctx, englishPolicy, "fraud-policy-v1")

// CI helpers
err = client.AssertCertsValid(ctx, certificates)
err = client.AssertLowView(ctx, replayID, 0.999)
```

## Performance SLOs

- **Sidecar decision latency**: P95 < 2ms (prod), < 1ms (local loopback)
- **Evidence write**: Amortized < 1ms per emission (batched)
- **Certificate validation**: 0 failures (deny-wins on any error)
- **Replay low-view match**: ≥99.9% (alert if below)

## Security & Privacy

- **RLS enforced** for all database reads (multi-tenant isolation)
- **PII redacted** at source and UI
- **All certificates signed** with deny-wins on validation errors
- **TLS everywhere** with JWT auth and RBAC
- **CERT-V1 schema validation** synchronous on every emission

## Verifiable MCP Fraud Demo

The demo showcases a complete vertical built entirely on platform APIs:

### Components

- **MCP Server**: TypeScript fraud scoring service
- **MCP Client Agent**: Policy-enforced transaction processor  
- **Transaction Simulator**: Multi-tenant synthetic data
- **Fraud Scorer**: ML-based risk assessment

### Demo Policy (English)

```
Only FraudService may call /score endpoint.
Alerts emitted only after L_txn → L_ops via Δ_Risk.
Rate limit alerts ≤ 5 per 10s/tenant.
Block score ≥ 0.93.
```

### Demo Flow

1. Author English policy in Policies tab → compile/build/prove/deploy
2. Watch Live Runtime metrics
3. Click decision → Evidence → view CERT-V1
4. Run Replay → get 99.9%+ low-view equality
5. Rotate Epoch and lower threshold to 0.90 for tenant ACME
6. Download Compliance Packet and export PDF

## Development

### Prerequisites

- Docker & Docker Compose
- Go 1.21+
- Node.js 18+
- Python 3.8+
- Lean 4 (optional, for local proofs)

### Local Development

```bash
# Start databases only
docker-compose up -d postgres redis

# Run services locally for development
cd services/api-gateway && go run main.go &
cd services/spec-service && go run main.go &
cd services/proof-service && go run main.go &
# ... etc

# Start console UI
cd console && npm start

# Start demo
cd demos/verifiable-mcp-fraud && npm run dev
```

### Testing

```bash
make test-all          # Complete test suite
make validate-certs    # CERT-V1 validation
make security          # Security tests
make bench             # Performance benchmarks
```

## Production Deployment

### Helm Charts

```bash
helm install sentinelops-platform charts/pf-enforce/ \
  --set global.environment=production \
  --set global.domain=platform.company.com \
  --set database.host=postgres.company.com \
  --set redis.host=redis.company.com \
  --set storage.s3.bucket=company-evidence-bucket
```

### Environment Variables

```bash
# Database
DATABASE_URL=postgres://user:pass@host:5432/sentinelops
REDIS_URL=redis://host:6379

# Storage
EVIDENCE_STORAGE_PATH=/data/evidence
PROOF_CACHE_PATH=/data/proof-cache

# Security
JWT_SECRET=your-jwt-secret
TLS_CERT_PATH=/etc/ssl/certs
TLS_KEY_PATH=/etc/ssl/private

# Morph Integration (optional)
MORPH_ENABLED=true
MORPH_API_URL=https://morph.company.com
```

## Observability

### Key Metrics

- `sidecar_decision_seconds_bucket` - Sidecar decision latency histogram
- `egress_write_seconds_bucket` - Evidence write latency histogram  
- `transactions_tps` - Transactions per second
- `cert_validation_failures_total` - Certificate validation failures (ALERT if > 0)
- `replay_lowview_match_ratio` - Replay low-view match ratio (ALERT if < 0.999)
- `rls_cross_tenant_blocks_total` - Cross-tenant access blocks

### Grafana Dashboards

- **Latency Dashboard**: P50/P95/P99 latencies across all services
- **Certificate Health**: Validation rates, emission patterns, failure analysis
- **Replay Coverage**: Low-view match rates, drift detection, execution times
- **RLS Isolation**: Cross-tenant blocks, policy effectiveness
- **Audit Integrity**: Hash chain verification, signature validation

## Standards Integration

- **CERT-V1**: `external/CERT-V1/` - Canonical certificate schema (submodule)
- **TRACE-REPLAY-KIT**: `external/TRACE-REPLAY-KIT/` - Deterministic replay runner (submodule)
- **Morph Integration**: Optional distributed proving and replay
- **ActionDSL**: Formal policy specification language with Lean proofs

## License

Apache License 2.0 - see [LICENSE](LICENSE) file for details.

## Links

- **CERT Schema**: https://github.com/verifiable-ai-ci/CERT-V1
- **Replay Kit**: https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT
- **Morph Lean CI**: https://github.com/SentinelOps-CI/morph-lean-ci
- **Morph Replay Runner**: https://github.com/SentinelOps-CI/morph-replay-runner

---

**SentinelOps Platform** - Usable, modular platform for developing, operating, auditing, and approving AI agents with provable behavioral guarantees.