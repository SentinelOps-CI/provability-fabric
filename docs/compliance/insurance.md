# Insurance-Grade Risk API & Premium Simulation

Provability-Fabric provides insurance-grade risk assessment and premium calculation capabilities for AI agent deployments, enabling compliance with regulatory requirements and supporting insurance industry standards.

## Overview

The insurance features provide:

- **Risk-to-Premium API**: Real-time premium calculation based on risk scores
- **Premium Simulation**: Historical analysis and trend prediction
- **Compliance Reporting**: EU AI Act and insurance industry standards
- **Weekly Insights**: Automated reporting and visualization

## API Endpoints

### Premium Quote API

Get a premium quote for a specific capsule:

```bash
GET /quote/{hash}
```

**Response:**

```json
{
  "risk": 0.75,
  "premium": 750.0,
  "quote_id": "quote_123",
  "created_at": "2024-01-01T00:00:00Z"
}
```

### GraphQL API

Query premium quotes and risk data:

```graphql
query {
  capsule(hash: "abc123...") {
    hash
    riskScore
    premiumQuotes {
      annualUsd
      createdAt
    }
  }
}
```

## Premium Calculation

Premiums are calculated using a linear formula:

```
Annual Premium = Risk Score × Base Rate
```

Where:

- **Risk Score**: 0.0 to 1.0 (from formal verification and runtime monitoring)
- **Base Rate**: Configurable base annual premium (default: $1,000)

### Risk Categories

- **Low Risk (0.0-0.3)**: $0-$300 annual premium
- **Medium Risk (0.3-0.7)**: $300-$700 annual premium
- **High Risk (0.7-1.0)**: $700-$1,000+ annual premium

## Weekly Simulation

The insurance simulator runs weekly to generate insights:

```bash
# Run simulation manually
python tools/insure/simulator.py --ledger-url http://localhost:4000 --days 30

# Output files:
# - docs/insights/risk_premium_chart.png
# - docs/insights/premium_distribution.png
# - docs/insights/insurance_report.md
```

### Generated Reports

1. **Risk vs Premium Chart**: Scatter plot showing correlation
2. **Premium Distribution**: Histogram of premium ranges
3. **Statistical Analysis**: Mean, median, standard deviation
4. **Top Risk Capsules**: Highest risk deployments
5. **Compliance Summary**: Regulatory alignment

## Configuration

### Environment Variables

```bash
# Ledger service
BASE_RATE=1000.0          # Base annual premium rate
LEDGER_URL=http://localhost:4000

# Simulation
SIMULATION_DAYS=30         # Days to analyze
OUTPUT_DIR=docs/insights   # Report output directory
```

### Database Schema

```sql
-- Premium quotes table
CREATE TABLE "PremiumQuote" (
  "id" TEXT NOT NULL,
  "capsuleHash" TEXT NOT NULL,
  "riskScore" REAL NOT NULL,
  "annualUsd" REAL NOT NULL,
  "createdAt" DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY ("id")
);

-- Foreign key to capsules
ALTER TABLE "PremiumQuote" ADD CONSTRAINT "PremiumQuote_capsuleHash_fkey"
  FOREIGN KEY ("capsuleHash") REFERENCES "Capsule"("hash") ON DELETE RESTRICT ON UPDATE CASCADE;
```

## Compliance Features

### EU AI Act Annex VIII

The insurance API supports EU AI Act requirements:

- **Risk Assessment**: Formal verification-based risk scoring
- **Transparency**: Public premium calculation methodology
- **Documentation**: Automated compliance reporting
- **Monitoring**: Continuous risk assessment

### Insurance Industry Standards

- **Actuarial Methods**: Statistical risk modeling
- **Premium Calculation**: Industry-standard linear formulas
- **Risk Categories**: Standardized risk classification
- **Reporting**: Automated regulatory reporting

## Integration Examples

### Kubernetes Admission Controller

```yaml
apiVersion: admission.k8s.io/v1
kind: ValidatingWebhookConfiguration
metadata:
  name: provability-fabric-webhook
webhooks:
  - name: provability-fabric.io
    rules:
      - apiGroups: [""]
        apiVersions: ["v1"]
        operations: ["CREATE"]
        resources: ["pods"]
    clientConfig:
      service:
        name: admission-controller
        port: 443
    sideEffects: None
    admissionReviewVersions: ["v1"]
```

### CI/CD Pipeline

```yaml
# .github/workflows/insurance-weekly.yaml
name: Weekly Insurance Analysis
on:
  schedule:
    - cron: "0 9 * * 1" # Every Monday at 9 AM

jobs:
  insurance-analysis:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run insurance simulation
        run: |
          python tools/insure/simulator.py --days 30
      - name: Commit insights
        run: |
          git add docs/insights/
          git commit -m "Weekly insurance insights"
          git push
```

## Monitoring & Alerts

### Risk Thresholds

- **High Risk Alert**: Risk score > 0.8
- **Premium Spike Alert**: 50% increase in 24h
- **Compliance Warning**: Missing risk assessment

### Metrics

- `insurance_premium_total`: Total annual premiums
- `insurance_risk_average`: Average risk score
- `insurance_quotes_generated`: Number of quotes
- `insurance_compliance_score`: Regulatory compliance

## Troubleshooting

### Common Issues

1. **No Data Available**: Ensure ledger service is running
2. **Invalid Risk Scores**: Check formal verification results
3. **Premium Calculation Errors**: Verify BASE_RATE configuration
4. **Graph Generation Fails**: Install matplotlib and numpy

### Debug Commands

```bash
# Test premium API
curl http://localhost:4000/quote/test-hash

# Check GraphQL
curl -X POST http://localhost:4000/graphql \
  -H "Content-Type: application/json" \
  -d '{"query":"query { capsules { hash riskScore } }"}'

# Run simulation with debug
python tools/insure/simulator.py --ledger-url http://localhost:4000 --days 7
```

## Future Enhancements

- **Machine Learning**: Predictive risk modeling
- **Multi-Factor Premiums**: Complex risk calculations
- **Insurance Integration**: Direct insurer APIs
- **Regulatory Updates**: Automated compliance checking
