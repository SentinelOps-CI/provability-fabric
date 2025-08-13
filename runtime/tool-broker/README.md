# Tool Broker

The Tool Broker is a critical security component in the Provability Fabric that enforces policy decisions from the Policy Kernel and implements rate limiting to prevent abuse.

## Overview

The Tool Broker serves as the enforcement layer between the Policy Kernel and actual tool execution. It ensures that:

1. **No tool runs without Kernel approval** - Every tool execution must have a valid decision token from the Policy Kernel
2. **Rate limits are enforced** - Prevents abuse through configurable rate limiting at multiple levels
3. **Human approval is required for high-risk operations** - Automatically escalates operations that exceed approval thresholds
4. **All violations are logged and monitored** - Provides comprehensive audit trail and metrics

## Architecture

```
┌─────────────────┐    ┌─────────────────┐     ┌─────────────────┐
│   Policy Kernel │───▶│   Tool Broker   │───▶│  Tool Execution │
│                 │    │                 │     │                 │
│ • Validates     │    │ • Rate Limiting │     │ • Actual Tool   │
│ • Approves      │    │ • Approvals     │     │   Execution     │
│ • Signs         │    │ • Enforcement   │     │ • Results       │
└─────────────────┘    └─────────────────┘     └─────────────────┘
```

## Core Components

### 1. Rate Limiter (`ratelimit.rs`)

Implements multi-level rate limiting with the following features:

- **Tool-specific limits**: Different rate limits for different tool types
- **Tenant isolation**: Per-tenant rate limiting and budget controls
- **Global limits**: System-wide rate limiting to prevent overload
- **Burst allowance**: Configurable burst capacity for legitimate traffic spikes
- **Approval thresholds**: Automatic escalation when usage exceeds thresholds

#### Rate Limit Configuration

```rust
pub struct RateLimitConfig {
    pub tool_limits: HashMap<String, ToolRateLimit>,
    pub tenant_limits: HashMap<String, TenantRateLimit>,
    pub global_limits: GlobalRateLimit,
    pub burst_allowance: f64,
    pub sliding_window_ms: u64,
}
```

#### Default Limits

| Tool Type | Per Minute | Per Hour | Per Day | Burst Multiplier | Approval Threshold |
|-----------|------------|----------|---------|------------------|-------------------|
| `data_query` | 100 | 5,000 | 100,000 | 2.0x | 50 |
| `retrieval` | 200 | 10,000 | 200,000 | 1.5x | 100 |

### 2. Approval Manager (`approvals.rs`)

Handles human approval workflows for high-risk operations:

- **Risk-based escalation**: Automatically escalates operations based on risk scores
- **Multi-approver support**: Configurable approval chains for critical operations
- **Timeout handling**: Automatic escalation if approvals are not received
- **Audit trail**: Complete record of approval decisions and reasoning

### 3. Main Broker (`main.rs`)

Orchestrates all components and provides the main API:

- **Plan validation**: Ensures plans are approved by the Policy Kernel
- **Tool execution**: Manages the complete tool execution lifecycle
- **Violation logging**: Records all policy violations and rate limit breaches
- **Metrics collection**: Exposes Prometheus metrics for monitoring

## Rate Limiting Implementation

### Multi-Level Rate Limiting

The rate limiter implements a hierarchical approach:

1. **Global Limits**: System-wide protection against overload
2. **Tenant Limits**: Per-tenant isolation and budget controls
3. **Tool Limits**: Tool-specific rate limiting and burst controls

### Sliding Window Algorithm

Uses a sliding window approach for accurate rate limiting:

```rust
fn get_requests_in_window(&self, timestamps: &VecDeque<Instant>, window: Duration) -> u32 {
    let now = Instant::now();
    let cutoff = now - window;
    
    timestamps.iter()
        .filter(|&ts| *ts > cutoff)
        .count() as u32
}
```

### Burst Handling

Supports configurable burst allowances for legitimate traffic spikes:

```rust
let burst_limit = (tool_limit.requests_per_minute as f64 * tool_limit.burst_multiplier) as u32;
if usage.requests_last_minute > burst_limit {
    return Ok(RateLimitDecision::Deny(format!("Burst limit exceeded")));
}
```

## Usage Examples

### Basic Rate Limiting

```rust
use runtime::tool_broker::ToolBroker;

let broker = ToolBroker::new("http://localhost:8080".to_string());

// Check rate limits before tool execution
let decision = broker.rate_limiter.check_rate_limit(
    "tenant1",
    "data_query",
    "session1"
).await?;

match decision {
    RateLimitDecision::Allow => {
        // Execute tool
    }
    RateLimitDecision::Deny(reason) => {
        // Handle rate limit violation
    }
    RateLimitDecision::RequireApproval(reason) => {
        // Create approval request
    }
    RateLimitDecision::Throttle(delay_ms) => {
        // Implement throttling
    }
}
```

### Configuration Updates

```rust
let mut new_config = RateLimitConfig::default();
new_config.tool_limits.insert("custom_tool".to_string(), ToolRateLimit {
    tool_name: "custom_tool".to_string(),
    requests_per_minute: 50,
    requests_per_hour: 1000,
    requests_per_day: 10000,
    burst_multiplier: 1.5,
    requires_approval_above: 25,
});

broker.update_rate_limit_config(new_config).await?;
```

### Monitoring and Metrics

```rust
// Get violation statistics
let stats = broker.get_rate_limit_stats().await?;
println!("Rate limit violations: {:?}", stats);

// Get general violations
let violations = broker.get_violations().await;
println!("Policy violations: {:?}", violations);
```

## Metrics

The Tool Broker exposes the following Prometheus metrics:

- `pf_broker_tool_executions_total{tool}` - Total tool executions by tool type
- `pf_broker_denies_total{reason}` - Total denials by reason (rate_limit, capability_missing, etc.)
- `pf_broker_approvals_required_total{tool}` - Total approval requests by tool type
- `pf_broker_tool_execution_duration_ms` - Tool execution duration histogram
- `http_connection_pool_size` - HTTP connection pool size gauge

## Testing

### Unit Tests

```bash
cd runtime/tool-broker
cargo test
```

### Integration Tests

```bash
cargo test --test integration_test
```

### Rate Limiting Tests

```bash
cargo test --test ratelimit_test
```

## Configuration

### Environment Variables

- `KERNEL_URL`: URL of the Policy Kernel service (default: http://localhost:8080)

### Rate Limiting Configuration

Rate limits can be configured through the `RateLimitConfig` structure:

```rust
let config = RateLimitConfig {
    tool_limits: HashMap::new(),
    tenant_limits: HashMap::new(),
    global_limits: GlobalRateLimit {
        max_requests_per_minute: 10000,
        max_requests_per_hour: 500000,
        max_requests_per_day: 10000000,
        max_concurrent_sessions: 1000,
        emergency_threshold: 0.9,
    },
    burst_allowance: 1.5,
    sliding_window_ms: 60000,
};
```

## Security Features

### 1. Policy Enforcement

- **Capability checking**: Ensures tools only run with appropriate capabilities
- **Receipt validation**: Verifies access receipts for data retrieval operations
- **Plan validation**: Only executes tools from approved plans

### 2. Rate Limiting

- **Multi-level protection**: Global, tenant, and tool-specific limits
- **Burst protection**: Configurable burst allowances with automatic throttling
- **Approval escalation**: Automatic escalation for high-usage operations

### 3. Audit and Monitoring

- **Violation logging**: Complete record of all policy violations
- **Rate limit tracking**: Detailed usage statistics and violation records
- **Metrics exposure**: Prometheus metrics for operational monitoring

## Performance Considerations

### Optimizations

- **Connection pooling**: HTTP/2 connection reuse for kernel communication
- **Sliding window**: Efficient time-window tracking with automatic cleanup
- **Async operations**: Non-blocking rate limit checks and tool execution

### Scalability

- **Per-tenant isolation**: Independent rate limiting per tenant
- **Configurable limits**: Adjustable limits based on system capacity
- **Horizontal scaling**: Stateless design supports multiple broker instances

## Troubleshooting

### Common Issues

1. **Rate limit violations**: Check current usage and adjust limits
2. **Approval delays**: Verify approval workflow configuration
3. **Connection errors**: Check kernel URL and network connectivity

### Debug Information

Enable debug logging to see detailed rate limiting decisions:

```bash
RUST_LOG=debug cargo run
```

### Monitoring

Use the exposed metrics to monitor broker performance:

- Track denial rates by reason
- Monitor tool execution durations
- Watch connection pool utilization

## Contributing

When contributing to the Tool Broker:

1. **Add tests**: All new functionality must include unit and integration tests
2. **Update metrics**: New features should expose relevant Prometheus metrics
3. **Document changes**: Update this README for any configuration or API changes
4. **Follow patterns**: Maintain consistency with existing code structure

## License

Apache 2.0 License - see LICENSE file for details.
