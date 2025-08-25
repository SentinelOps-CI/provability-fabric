# API Reference

This document provides comprehensive API reference information for the Provability-Fabric framework, including REST APIs, gRPC services, and client SDKs.

## Overview

Provability-Fabric provides multiple API interfaces for different use cases:

- **REST API** - HTTP-based API for web applications
- **gRPC API** - High-performance RPC for service-to-service communication
- **GraphQL API** - Flexible query interface for complex data retrieval
- **Client SDKs** - Language-specific libraries for easy integration

## REST API

### Base URL

```
https://api.provability-fabric.org/v1
```

### Authentication

All API requests require authentication using API keys or OAuth 2.0:

```bash
# API Key Authentication
Authorization: Bearer YOUR_API_KEY

# OAuth 2.0
Authorization: Bearer YOUR_ACCESS_TOKEN
```

### Common Headers

```http
Content-Type: application/json
Accept: application/json
User-Agent: ProvabilityFabric-Client/1.0
```

### Error Handling

All errors follow a consistent format:

```json
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Invalid specification format",
    "details": {
      "field": "specification",
      "issue": "Missing required field 'name'"
    }
  }
}
```

### HTTP Status Codes

- `200` - Success
- `201` - Created
- `400` - Bad Request
- `401` - Unauthorized
- `403` - Forbidden
- `404` - Not Found
- `422` - Validation Error
- `500` - Internal Server Error

## Core API Endpoints

### Agent Management

#### List Agents

```http
GET /agents
```

**Query Parameters:**
- `page` - Page number (default: 1)
- `limit` - Items per page (default: 20)
- `status` - Filter by status (active, inactive, failed)
- `capability` - Filter by capability

**Response:**
```json
{
  "agents": [
    {
      "id": "agent-123",
      "name": "text-generator",
      "version": "1.0.0",
      "status": "active",
      "capabilities": ["text_generation"],
      "created_at": "2024-01-01T00:00:00Z",
      "updated_at": "2024-01-01T00:00:00Z"
    }
  ],
  "pagination": {
    "page": 1,
    "limit": 20,
    "total": 100,
    "pages": 5
  }
}
```

#### Get Agent

```http
GET /agents/{agent_id}
```

**Response:**
```json
{
  "id": "agent-123",
  "name": "text-generator",
  "version": "1.0.0",
  "status": "active",
  "specification": {
    "capabilities": [
      {
        "name": "text_generation",
        "constraints": {
          "max_length": 1000,
          "content_filter": true
        }
      }
    ]
  },
  "proofs": [
    {
      "id": "proof-456",
      "type": "lean",
      "status": "verified",
      "verified_at": "2024-01-01T00:00:00Z"
    }
  ],
  "created_at": "2024-01-01T00:00:00Z",
  "updated_at": "2024-01-01T00:00:00Z"
}
```

#### Create Agent

```http
POST /agents
```

**Request Body:**
```json
{
  "name": "new-agent",
  "version": "1.0.0",
  "description": "A new AI agent",
  "specification": {
    "capabilities": [
      {
        "name": "text_generation",
        "constraints": {
          "max_length": 1000
        }
      }
    ]
  }
}
```

**Response:**
```json
{
  "id": "agent-789",
  "name": "new-agent",
  "version": "1.0.0",
  "status": "pending",
  "created_at": "2024-01-01T00:00:00Z"
}
```

#### Update Agent

```http
PUT /agents/{agent_id}
```

**Request Body:**
```json
{
  "version": "1.1.0",
  "specification": {
    "capabilities": [
      {
        "name": "text_generation",
        "constraints": {
          "max_length": 2000
        }
      }
    ]
  }
}
```

#### Delete Agent

```http
DELETE /agents/{agent_id}
```

**Response:**
```json
{
  "message": "Agent deleted successfully",
  "deleted_at": "2024-01-01T00:00:00Z"
}
```

### Proof Management

#### List Proofs

```http
GET /proofs
```

**Query Parameters:**
- `agent_id` - Filter by agent
- `type` - Filter by proof type (lean, marabou, dryvr)
- `status` - Filter by status (pending, verified, failed)

#### Get Proof

```http
GET /proofs/{proof_id}
```

**Response:**
```json
{
  "id": "proof-456",
  "agent_id": "agent-123",
  "type": "lean",
  "status": "verified",
  "content": "theorem example...",
  "verification_result": {
    "verified_at": "2024-01-01T00:00:00Z",
    "verifier": "lean-4.0.0",
    "verification_time": 15.5
  },
  "created_at": "2024-01-01T00:00:00Z"
}
```

#### Verify Proof

```http
POST /proofs/{proof_id}/verify
```

**Response:**
```json
{
  "status": "verified",
  "verified_at": "2024-01-01T00:00:00Z",
  "verification_time": 15.5
}
```

### Deployment Management

#### List Deployments

```http
GET /deployments
```

#### Get Deployment

```http
GET /deployments/{deployment_id}
```

#### Create Deployment

```http
POST /deployments
```

**Request Body:**
```json
{
  "agent_id": "agent-123",
  "environment": "production",
  "replicas": 3,
  "resources": {
    "cpu": "1000m",
    "memory": "2Gi"
  }
}
```

#### Update Deployment

```http
PUT /deployments/{deployment_id}
```

#### Delete Deployment

```http
DELETE /deployments/{deployment_id}
```

### Monitoring and Metrics

#### Get Agent Metrics

```http
GET /agents/{agent_id}/metrics
```

**Query Parameters:**
- `start_time` - Start of time range
- `end_time` - End of time range
- `interval` - Time interval (1m, 5m, 1h, 1d)

**Response:**
```json
{
  "metrics": [
    {
      "timestamp": "2024-01-01T00:00:00Z",
      "requests_per_second": 150.5,
      "latency_p95": 45.2,
      "error_rate": 0.01,
      "resource_usage": {
        "cpu": 0.75,
        "memory": 0.60
      }
    }
  ]
}
```

#### Get System Health

```http
GET /health
```

**Response:**
```json
{
  "status": "healthy",
  "timestamp": "2024-01-01T00:00:00Z",
  "components": {
    "api": "healthy",
    "database": "healthy",
    "verification_engine": "healthy"
  },
  "version": "1.0.0"
}
```

## gRPC API

### Service Definitions

The gRPC API is defined using Protocol Buffers and provides high-performance RPC communication.

#### Agent Service

```protobuf
service AgentService {
  rpc ListAgents(ListAgentsRequest) returns (ListAgentsResponse);
  rpc GetAgent(GetAgentRequest) returns (Agent);
  rpc CreateAgent(CreateAgentRequest) returns (Agent);
  rpc UpdateAgent(UpdateAgentRequest) returns (Agent);
  rpc DeleteAgent(DeleteAgentRequest) returns (DeleteAgentResponse);
}
```

#### Proof Service

```protobuf
service ProofService {
  rpc ListProofs(ListProofsRequest) returns (ListProofsResponse);
  rpc GetProof(GetProofRequest) returns (Proof);
  rpc VerifyProof(VerifyProofRequest) returns (VerifyProofResponse);
}
```

#### Deployment Service

```protobuf
service DeploymentService {
  rpc ListDeployments(ListDeploymentsRequest) returns (ListDeploymentsResponse);
  rpc GetDeployment(GetDeploymentRequest) returns (Deployment);
  rpc CreateDeployment(CreateDeploymentRequest) returns (Deployment);
  rpc UpdateDeployment(UpdateDeploymentRequest) returns (Deployment);
  rpc DeleteDeployment(DeleteDeploymentRequest) returns (DeleteDeploymentResponse);
}
```

### gRPC Client Example

```go
package main

import (
    "context"
    "log"
    "google.golang.org/grpc"
    pb "github.com/provability-fabric/provability-fabric/api/v1"
)

func main() {
    conn, err := grpc.Dial("localhost:50051", grpc.WithInsecure())
    if err != nil {
        log.Fatalf("Failed to connect: %v", err)
    }
    defer conn.Close()

    client := pb.NewAgentServiceClient(conn)
    
    resp, err := client.ListAgents(context.Background(), &pb.ListAgentsRequest{})
    if err != nil {
        log.Fatalf("Failed to list agents: %v", err)
    }
    
    for _, agent := range resp.Agents {
        log.Printf("Agent: %s", agent.Name)
    }
}
```

## GraphQL API

### Schema

The GraphQL API provides a flexible interface for querying complex data relationships.

```graphql
type Agent {
  id: ID!
  name: String!
  version: String!
  status: AgentStatus!
  capabilities: [Capability!]!
  proofs: [Proof!]!
  deployments: [Deployment!]!
  metrics: Metrics
  createdAt: DateTime!
  updatedAt: DateTime!
}

type Capability {
  name: String!
  constraints: JSON!
}

type Proof {
  id: ID!
  type: ProofType!
  status: ProofStatus!
  content: String!
  verificationResult: VerificationResult
}

type Deployment {
  id: ID!
  environment: String!
  replicas: Int!
  status: DeploymentStatus!
  metrics: Metrics
}

type Metrics {
  requestsPerSecond: Float
  latencyP95: Float
  errorRate: Float
  resourceUsage: ResourceUsage
}

enum AgentStatus {
  ACTIVE
  INACTIVE
  FAILED
  PENDING
}

enum ProofStatus {
  PENDING
  VERIFIED
  FAILED
}

enum ProofType {
  LEAN
  MARABOU
  DRYVR
}

enum DeploymentStatus {
  RUNNING
  SCALING
  FAILED
  STOPPED
}

type Query {
  agents(
    first: Int
    after: String
    status: AgentStatus
    capability: String
  ): AgentConnection!
  
  agent(id: ID!): Agent
  
  proofs(
    first: Int
    after: String
    agentId: ID
    type: ProofType
    status: ProofStatus
  ): ProofConnection!
  
  deployments(
    first: Int
    after: String
    agentId: ID
    environment: String
  ): DeploymentConnection!
}

type Mutation {
  createAgent(input: CreateAgentInput!): CreateAgentPayload!
  updateAgent(input: UpdateAgentInput!): UpdateAgentPayload!
  deleteAgent(input: DeleteAgentInput!): DeleteAgentPayload!
  
  verifyProof(input: VerifyProofInput!): VerifyProofPayload!
  
  createDeployment(input: CreateDeploymentInput!): CreateDeploymentPayload!
  updateDeployment(input: UpdateDeploymentInput!): UpdateDeploymentPayload!
  deleteDeployment(input: DeleteDeploymentInput!): DeleteDeploymentPayload!
}
```

### GraphQL Query Example

```graphql
query GetAgentWithDetails($agentId: ID!) {
  agent(id: $agentId) {
    id
    name
    version
    status
    capabilities {
      name
      constraints
    }
    proofs {
      id
      type
      status
      verificationResult {
        verifiedAt
        verifier
        verificationTime
      }
    }
    deployments {
      id
      environment
      replicas
      status
      metrics {
        requestsPerSecond
        latencyP95
        errorRate
      }
    }
    metrics {
      requestsPerSecond
      latencyP95
      errorRate
      resourceUsage {
        cpu
        memory
      }
    }
  }
}
```

## Client SDKs

### TypeScript/Node.js SDK

```bash
npm install @provability-fabric/core-sdk-typescript
```

**Usage:**
```typescript
import { ProvabilityFabricClient } from '@provability-fabric/core-sdk-typescript';

const client = new ProvabilityFabricClient({
  apiKey: 'your-api-key',
  baseUrl: 'https://api.provability-fabric.org/v1'
});

// List agents
const agents = await client.agents.list({
  page: 1,
  limit: 20
});

// Create agent
const agent = await client.agents.create({
  name: 'my-agent',
  version: '1.0.0',
  specification: {
    capabilities: [
      {
        name: 'text_generation',
        constraints: { max_length: 1000 }
      }
    ]
  }
});

// Get agent metrics
const metrics = await client.agents.getMetrics(agent.id, {
  startTime: new Date('2024-01-01'),
  endTime: new Date('2024-01-02'),
  interval: '1h'
});
```

### Go SDK

```bash
go get github.com/provability-fabric/core/sdk/go
```

**Usage:**
```go
package main

import (
    "context"
    "log"
    "github.com/provability-fabric/core/sdk/go"
)

func main() {
    client := provabilityfabric.NewClient(&provabilityfabric.Config{
        APIKey:  "your-api-key",
        BaseURL: "https://api.provability-fabric.org/v1",
    })

    // List agents
    agents, err := client.Agents.List(context.Background(), &provabilityfabric.ListAgentsRequest{
        Page:  1,
        Limit: 20,
    })
    if err != nil {
        log.Fatalf("Failed to list agents: %v", err)
    }

    // Create agent
    agent, err := client.Agents.Create(context.Background(), &provabilityfabric.CreateAgentRequest{
        Name:    "my-agent",
        Version: "1.0.0",
        Specification: &provabilityfabric.AgentSpecification{
            Capabilities: []*provabilityfabric.Capability{
                {
                    Name: "text_generation",
                    Constraints: map[string]interface{}{
                        "max_length": 1000,
                    },
                },
            },
        },
    })
    if err != nil {
        log.Fatalf("Failed to create agent: %v", err)
    }

    log.Printf("Created agent: %s", agent.ID)
}
```

### Rust SDK

```toml
[dependencies]
provability-fabric-core-sdk-rust = "1.0.0"
```

**Usage:**
```rust
use provability_fabric_core_sdk_rust::{Client, Config};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new(Config {
        api_key: "your-api-key".to_string(),
        base_url: "https://api.provability-fabric.org/v1".to_string(),
    });

    // List agents
    let agents = client.agents().list(&ListAgentsRequest {
        page: Some(1),
        limit: Some(20),
        ..Default::default()
    }).await?;

    // Create agent
    let agent = client.agents().create(&CreateAgentRequest {
        name: "my-agent".to_string(),
        version: "1.0.0".to_string(),
        specification: Some(AgentSpecification {
            capabilities: vec![Capability {
                name: "text_generation".to_string(),
                constraints: serde_json::json!({
                    "max_length": 1000
                }),
            }],
        }),
    }).await?;

    println!("Created agent: {}", agent.id);
    Ok(())
}
```

## Rate Limiting

The API implements rate limiting to ensure fair usage:

- **Free Tier**: 100 requests per hour
- **Pro Tier**: 1,000 requests per hour
- **Enterprise**: Custom limits

Rate limit headers are included in responses:

```http
X-RateLimit-Limit: 1000
X-RateLimit-Remaining: 999
X-RateLimit-Reset: 1640995200
```

## Pagination

List endpoints support pagination using cursor-based pagination:

```json
{
  "data": [...],
  "pagination": {
    "next_cursor": "eyJpZCI6ImFnZW50LTEyMyJ9",
    "has_more": true
  }
}
```

**Usage:**
```bash
# First page
GET /agents?limit=20

# Next page using cursor
GET /agents?limit=20&cursor=eyJpZCI6ImFnZW50LTEyMyJ9
```

## Webhooks

Webhooks allow you to receive real-time notifications about events:

### Supported Events

- `agent.created` - Agent created
- `agent.updated` - Agent updated
- `agent.deleted` - Agent deleted
- `proof.verified` - Proof verification completed
- `deployment.created` - Deployment created
- `deployment.updated` - Deployment updated
- `deployment.failed` - Deployment failed

### Webhook Configuration

```json
{
  "url": "https://your-app.com/webhooks",
  "events": ["agent.created", "proof.verified"],
  "secret": "webhook-secret"
}
```

### Webhook Payload

```json
{
  "event": "agent.created",
  "timestamp": "2024-01-01T00:00:00Z",
  "data": {
    "agent": {
      "id": "agent-123",
      "name": "my-agent"
    }
  }
}
```

## SDK Examples

### Complete Agent Lifecycle

```typescript
import { ProvabilityFabricClient } from '@provability-fabric/core-sdk-typescript';

const client = new ProvabilityFabricClient({
  apiKey: process.env.PF_API_KEY
});

async function createAndDeployAgent() {
  try {
    // 1. Create agent specification
    const agent = await client.agents.create({
      name: 'production-agent',
      version: '1.0.0',
      specification: {
        capabilities: [
          {
            name: 'text_generation',
            constraints: { max_length: 1000, content_filter: true }
          }
        ]
      }
    });

    // 2. Upload and verify proofs
    const proof = await client.proofs.upload(agent.id, {
      type: 'lean',
      content: 'theorem behavior_verification...'
    });

    await client.proofs.verify(proof.id);

    // 3. Create deployment
    const deployment = await client.deployments.create({
      agentId: agent.id,
      environment: 'production',
      replicas: 3,
      resources: { cpu: '1000m', memory: '2Gi' }
    });

    // 4. Monitor deployment
    const metrics = await client.deployments.getMetrics(deployment.id);
    console.log('Deployment metrics:', metrics);

  } catch (error) {
    console.error('Error:', error);
  }
}
```

## Error Codes

Common error codes and their meanings:

| Code | Description | HTTP Status |
|------|-------------|-------------|
| `VALIDATION_ERROR` | Request validation failed | 400 |
| `AUTHENTICATION_FAILED` | Invalid or missing authentication | 401 |
| `AUTHORIZATION_FAILED` | Insufficient permissions | 403 |
| `RESOURCE_NOT_FOUND` | Requested resource not found | 404 |
| `RATE_LIMIT_EXCEEDED` | Rate limit exceeded | 429 |
| `INTERNAL_ERROR` | Internal server error | 500 |
| `SERVICE_UNAVAILABLE` | Service temporarily unavailable | 503 |

## Support

For API support and questions:

- **Documentation**: This API reference
- **GitHub Issues**: Bug reports and feature requests
- **Discord**: Community discussions
- **Email**: api-support@provability-fabric.org

## SDK Downloads

Download the latest SDK versions:

- **TypeScript/Node.js**: [npm package](https://www.npmjs.com/package/@provability-fabric/core-sdk-typescript)
- **Go**: [Go module](https://pkg.go.dev/github.com/provability-fabric/core/sdk/go)
- **Rust**: [Crates.io](https://crates.io/crates/provability-fabric-core-sdk-rust)
