# Provability Fabric Core SDKs

Official SDKs for Provability Fabric core surfaces: ledger HTTP, local trace verification, and Express middleware.

Local ports for compose / `make ledger-up`: ledger `http://localhost:4000`, sidecar `http://localhost:8006`. See [docs/dev/local-workflows.md](../../docs/dev/local-workflows.md).

## Quick Start

### TypeScript/Node.js

```bash
cd core/sdk/typescript
npm install
npm test
```

```typescript
import {
  ProvabilityFabricSDK,
  pfMiddleware,
  retryMiddleware,
} from '@provability-fabric/core-sdk-typescript';
import express from 'express';

const app = express();
app.use(express.json());

const sdk = new ProvabilityFabricSDK({
  endpoint: 'http://localhost:4000', // ledger GraphQL /health
  timeout: 30000,
  retries: 3,
});

await sdk.connect(); // probes GET /health

app.use(
  pfMiddleware({
    sdk,
    addHeaders: true,
    verifyTrace: true,
    timeout: 5000,
  })
);

app.use(
  retryMiddleware({
    maxRetries: 3,
    baseDelay: 1000,
    maxDelay: 10000,
  })
);

app.get('/status', async (_req, res) => {
  const health = await sdk.getClient().getHealth();
  res.json(health);
});

app.post('/verify', async (req, res) => {
  try {
    const result = await sdk.verifyTrace(req.body.trace);
    res.json(result);
  } catch (error) {
    res.status(400).json({ error: (error as Error).message });
  }
});

app.listen(3000);
```

Transport is **HTTP only** today. Passing `transport: 'grpc'` throws; gRPC is deferred until generated protos are consumed by this package. Unused `@grpc/grpc-js` dependencies were removed.

### Go

```bash
go get github.com/provability-fabric/core/sdk/go
```

See `core/sdk/go` for HTTP client and Gin middleware wiring. Point `Endpoint` at the ledger (`http://localhost:4000`) or API gateway (`http://localhost:8000`) as appropriate.

### Rust

```toml
# Cargo.toml
[dependencies]
provability-fabric-core-sdk-rust = "1.0.0"
```

Point the client builder at the ledger HTTP endpoint (`http://localhost:4000`) unless you are talking to another documented surface.

## Features

- **Trace verification**: local DSSE / policy-oriented `verifyTrace`
- **HTTP client**: `connect()` → `/health`, then ledger/API paths
- **Express middleware**: `pfMiddleware`, `retryMiddleware`, `circuitBreakerMiddleware`
- **Resilience**: idempotent retries with backoff (see `retry.ts`)

## Configuration

```typescript
const sdk = new ProvabilityFabricSDK({
  endpoint: 'http://localhost:4000',
  timeout: 30000,
  retries: 3,
  apiKey: process.env.PF_API_KEY,
});
```

Environment variable names for local stacks are documented in [schemas/pf-env.schema.json](../../schemas/pf-env.schema.json).

## Testing

```bash
# TypeScript
cd core/sdk/typescript && npm test

# Go
cd core/sdk/go && go test ./...

# Rust
cd core/sdk/rust && cargo test
```

## Contributing

See [Contributing Guide](../../CONTRIBUTING.md).

## License

Apache License 2.0 — see [LICENSE](../../LICENSE).
