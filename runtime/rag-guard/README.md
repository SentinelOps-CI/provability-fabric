# @pf/guard-rag

A comprehensive Node.js content filter for RAG (Retrieval-Augmented Generation) responses that detects and blocks PII (Personally Identifiable Information) and secrets using regex patterns and entropy analysis.

## Features

- **PII Detection**: Detects SSNs, credit cards, emails, phone numbers, IP addresses, and more
- **Secret Detection**: Identifies API keys, tokens, passwords, and private keys
- **Entropy Analysis**: Uses Shannon entropy to detect high-entropy secrets
- **Incident Logging**: Reports blocked content to Provability Fabric ledger
- **TypeScript Support**: Full TypeScript types and definitions
- **Configurable**: Customizable patterns and detection rules
- **Secure by Default**: Fails securely when errors occur

## Installation

```bash
npm install @pf/guard-rag
```

## Quick Start

```typescript
import { RAGGuard, GuardConfig } from '@pf/guard-rag';

const config: GuardConfig = {
  ledgerUrl: 'http://localhost:3000',
  tenantId: 'your-tenant-id',
  sessionId: 'session-123',
  enablePII: true,
  enableSecrets: true,
  timeout: 5000,
  retries: 3
};

const guard = new RAGGuard(config);

// Filter content
const result = await guard.filter('User email: admin@example.com has API key: sk_fake_example_key_not_real');

if (result.allowed) {
  console.log('Content is safe:', result.safeContent);
} else {
  console.log('Content blocked:', result.safeContent);
  console.log('Detections:', result.blockedDetections);
  console.log('Incident ID:', result.incidentId);
}
```

## API Reference

### GuardConfig

```typescript
interface GuardConfig {
  ledgerUrl: string;        // PF ledger endpoint
  tenantId: string;         // Tenant identifier
  sessionId: string;        // Session identifier
  enablePII: boolean;       // Enable PII detection
  enableSecrets: boolean;   // Enable secret detection
  customPatterns?: {        // Custom detection patterns
    pii?: PIIPattern[];
    secrets?: SecretPattern[];
  };
  timeout: number;          // Request timeout (ms)
  retries: number;          // Retry attempts
}
```

### GuardResponse

```typescript
interface GuardResponse {
  allowed: boolean;                    // Whether content is allowed
  safeContent?: string;                // Content with redactions
  blockedDetections?: DetectionResult[]; // What was detected
  incidentId?: string;                 // Ledger incident ID
}
```

### DetectionResult

```typescript
interface DetectionResult {
  type: 'pii' | 'secret';             // Detection type
  name: string;                       // Pattern name
  severity: 'low' | 'medium' | 'high' | 'critical';
  match: string;                      // Matched text
  position: { start: number; end: number; };
  description: string;                // Human-readable description
}
```

## Built-in Detection Patterns

### PII Patterns

- **SSN**: Social Security Numbers (with/without dashes)
- **Credit Cards**: Visa, MasterCard, Amex, Discover
- **Email**: Email addresses (RFC-compliant)
- **Phone**: US phone numbers (various formats)
- **IP Address**: IPv4 addresses
- **Passport**: Passport numbers
- **Driver License**: Driver license numbers

### Secret Patterns

- **AWS Keys**: Access keys and secret keys (with entropy check)
- **GitHub Tokens**: Personal access tokens and app tokens
- **Slack Tokens**: Bot tokens and user tokens
- **Stripe Keys**: Live secret keys
- **JWT Tokens**: JSON Web Tokens
- **Private Keys**: RSA, EC, and other private keys
- **Generic API Keys**: High-entropy strings labeled as keys/tokens

## Custom Patterns

Add custom detection patterns:

```typescript
const customConfig: GuardConfig = {
  // ... base config
  customPatterns: {
    pii: [
      {
        name: 'employee_id',
        pattern: /EMP\d{6}/g,
        severity: 'medium',
        description: 'Employee ID'
      }
    ],
    secrets: [
      {
        name: 'custom_token',
        pattern: /CTK_[A-Za-z0-9]{32}/g,
        entropyThreshold: 4.5,
        severity: 'high',
        description: 'Custom Token'
      }
    ]
  }
};
```

## Content Redaction

Detected patterns are replaced with descriptive redaction markers:

```
Original: "Contact admin@example.com with API key sk_fake_example_key_not_real"
Redacted: "Contact [EMAIL-REDACTED] with API key [STRIPE-KEY-REDACTED]"
```

## Error Handling

The guard fails securely - if an error occurs during processing, content is blocked:

```typescript
try {
  const result = await guard.filter(content);
  // Handle result
} catch (error) {
  // Guard already handles errors internally
  // Result will have allowed: false with error message
}
```

## Testing

Run the test suite:

```bash
npm test
```

Run with coverage:

```bash
npm run test -- --coverage
```

## Demo

Try the interactive demo:

```bash
npm run demo
```

## Performance

- **Regex Efficiency**: Optimized patterns with minimal backtracking
- **Entropy Calculation**: Efficient Shannon entropy for secret detection
- **Memory Usage**: Streaming-friendly processing for large content
- **Async Operations**: Non-blocking ledger reporting

## Security Considerations

- **Fail Secure**: Blocks content on processing errors
- **No Data Leakage**: Original content never stored in logs
- **Entropy Thresholds**: Prevents false positives on low-entropy data
- **Redaction Markers**: Clear indication of what was blocked

## License

Apache-2.0 - See LICENSE file for details.

## Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

## Support

For issues and questions:
- GitHub Issues: [provability-fabric/issues](https://github.com/SentinelOps-CI/provability-fabric/issues)
- Documentation: [Provability Fabric Docs](https://docs.provability-fabric.com)
