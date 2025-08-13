# Provability Fabric Core SDKs

This directory contains the official SDKs for the Provability Fabric Core, providing easy integration with the core services including Policy Kernel, Access Receipt, Egress Firewall, and Safety Case services.

## Quick Start

### TypeScript/Node.js

```bash
npm install @provability-fabric/core-sdk-typescript
```

```typescript
import { ProvabilityFabricSDK, pfMiddleware } from '@provability-fabric/core-sdk-typescript';
import express from 'express';

const app = express();
const sdk = new ProvabilityFabricSDK({
  endpoint: 'http://localhost:8080',
  timeout: 30000,
  retries: 3
});

// Add PF middleware with trace verification
app.use(pfMiddleware({
  sdk,
  addHeaders: true,
  verifyTrace: true,
  timeout: 5000
}));

// Add circuit breaker and retry middleware
app.use(circuitBreakerMiddleware({
  failureThreshold: 5,
  resetTimeout: 60000
}));

app.use(retryMiddleware({
  maxRetries: 3,
  baseDelay: 1000,
  maxDelay: 10000
}));

app.post('/verify', async (req, res) => {
  try {
    const result = await sdk.verifyTrace(req.body.trace);
    res.json(result);
  } catch (error) {
    res.status(400).json({ error: error.message });
  }
});

app.listen(3000, () => {
  console.log('Server running on port 3000');
});
```

### Go

```bash
go get github.com/provability-fabric/core/sdk/go
```

```go
package main

import (
    "github.com/gin-gonic/gin"
    "github.com/provability-fabric/core/sdk/go/sdk"
    "github.com/provability-fabric/core/sdk/go/middleware"
)

func main() {
    r := gin.Default()
    
    // Initialize SDK
    config := sdk.Config{
        Endpoint: "http://localhost:8080",
        Timeout:  30 * time.Second,
        Retries:  3,
    }
    
    pfSDK := sdk.NewSDK(config, nil) // TODO: Implement actual client
    
    // Add PF middleware
    r.Use(middleware.PFMiddleware(middleware.PFMiddlewareOptions{
        SDK:         pfSDK,
        AddHeaders:  true,
        VerifyTrace: true,
        Timeout:     5 * time.Second,
    }))
    
    // Add circuit breaker and retry middleware
    r.Use(middleware.CircuitBreakerMiddleware(middleware.CircuitBreakerOptions{
        FailureThreshold: 5,
        ResetTimeout:     60 * time.Second,
    }))
    
    r.Use(middleware.RetryMiddleware(middleware.RetryOptions{
        MaxRetries: 3,
        BaseDelay:  1 * time.Second,
        MaxDelay:   10 * time.Second,
    }))
    
    r.POST("/verify", func(c *gin.Context) {
        // Trace verification is handled by middleware
        c.JSON(200, gin.H{"status": "verified"})
    })
    
    r.Run(":3000")
}
```

### Rust

```toml
# Cargo.toml
[dependencies]
provability-fabric-core-sdk-rust = "1.0.0"
```

```rust
use provability_fabric_core_sdk_rust::{
    client::ClientBuilder,
    types::{Trace, Subject, SubjectType},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create client
    let client = ClientBuilder::new()
        .endpoint("http://localhost:8080")
        .timeout(std::time::Duration::from_secs(30))
        .build()?;
    
    // Create trace
    let trace = Trace {
        id: "trace_123".to_string(),
        subject: Subject {
            id: "user_456".to_string(),
            subject_type: SubjectType::User,
            capabilities: vec!["read".to_string(), "write".to_string()],
            labels: std::collections::HashMap::new(),
        },
        steps: vec![],
        metadata: std::collections::HashMap::new(),
    };
    
    // Verify trace
    let result = client.verify_trace(&trace).await?;
    println!("Trace verification result: {:?}", result);
    
    Ok(())
}
```

## Architecture

The SDKs provide a unified interface to the Provability Fabric Core services:

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Application   │    │      SDK        │    │  Core Services  │
│                 │◄──►│                 │◄──►│                 │
│ - Express/Gin   │    │ - Client        │    │ - Policy Kernel │
│ - Middleware    │    │ - Middleware    │    │ - Access Receipt│
│ - Error Handling│    │ - Types         │    │ - Egress Firewall│
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

## Features

### Core Functionality
- **Trace Verification**: Verify execution traces against policy rules
- **Access Control**: Enforce capability-based access control
- **Label Flow**: Track and enforce data labeling policies
- **Receipt Management**: Create and verify access receipts

### Middleware Support
- **PF-Sig Headers**: Automatic addition of Provability Fabric signature headers
- **Circuit Breaker**: Automatic failure detection and service isolation
- **Retry Logic**: Exponential backoff with configurable limits
- **Timeout Handling**: Configurable timeouts for all operations

### Resilience Features
- **Connection Pooling**: Efficient connection management
- **Load Balancing**: Automatic load distribution
- **Health Checks**: Service health monitoring
- **Metrics**: Built-in observability and monitoring

## Configuration

### SDK Configuration

```typescript
const config = {
  endpoint: 'https://pf-core.example.com:8080',
  timeout: 30000,           // 30 seconds
  retries: 3,               // 3 retry attempts
  circuitBreaker: {
    failureThreshold: 5,     // Open circuit after 5 failures
    resetTimeout: 60000,     // Wait 60 seconds before retry
    monitoringWindow: 300000 // 5 minute monitoring window
  },
  authentication: {
    type: 'jwt',             // JWT authentication
    credentials: {
      token: 'your-jwt-token'
    },
    tokenRefreshInterval: 3600000 // 1 hour refresh
  }
};
```

### Middleware Configuration

```typescript
const middlewareOptions = {
  sdk: pfSDK,
  addHeaders: true,          // Add PF-Sig headers
  verifyTrace: true,         // Verify traces automatically
  timeout: 5000,             // 5 second verification timeout
  circuitBreaker: true,      // Enable circuit breaker
  retries: true              // Enable retry logic
};
```

## Testing

### Unit Tests
```bash
# TypeScript
npm test

# Go
go test ./...

# Rust
cargo test
```

### Integration Tests
```bash
# Start mock server
npm run test:integration

# Run tests against mock server
npm run test:e2e
```

### Performance Tests
```bash
# TypeScript
npm run test:perf

# Go
go test -bench=. -benchmem ./...

# Rust
cargo bench
```

## Publishing

### TypeScript SDK
```bash
cd core/sdk/typescript
chmod +x scripts/publish.sh
./scripts/publish.sh
```

### Go SDK
```bash
cd core/sdk/go
chmod +x scripts/publish.sh
./scripts/publish.sh
```

### Rust SDK
```bash
cd core/sdk/rust
cargo publish
```

## Security

- **Authentication**: JWT, API Key, and OAuth support
- **Encryption**: TLS 1.3 for all communications
- **Attestation**: Enclave attestation verification
- **Audit Logging**: Comprehensive audit trail
- **Rate Limiting**: Built-in rate limiting and throttling

## Monitoring

The SDKs provide built-in metrics and observability:

- **Request Counters**: Total requests, successes, failures
- **Latency Histograms**: Response time distributions
- **Error Rates**: Failure rates by error type
- **Circuit Breaker Status**: Open/closed state monitoring
- **Retry Statistics**: Retry attempts and success rates

## Error Handling

The SDKs provide structured error handling with:

- **Error Types**: Categorized error types (validation, auth, timeout, etc.)
- **Error Codes**: Machine-readable error codes
- **Error Details**: Additional context and debugging information
- **Error Recovery**: Automatic retry and circuit breaker logic

## Contributing

We welcome contributions! Please see our [Contributing Guide](../../CONTRIBUTING.md) for details.

## License

This project is licensed under the Apache License 2.0 - see the [LICENSE](../../LICENSE) file for details.
