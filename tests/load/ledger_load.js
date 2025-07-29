import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate } from 'k6/metrics';

// Custom metrics
const errorRate = new Rate('errors');

// Test configuration
export const options = {
  stages: [
    { duration: '30s', target: 50 },   // Ramp up to 50 users
    { duration: '60s', target: 100 },  // Ramp up to 100 users
    { duration: '60s', target: 100 },  // Stay at 100 users
    { duration: '30s', target: 0 },    // Ramp down to 0 users
  ],
  thresholds: {
    http_req_duration: ['p(95)<120'],  // 95th percentile must be < 120ms
    http_req_failed: ['rate<0.001'],   // Error rate must be < 0.1%
    http_req_rate: ['rate>95'],        // Must maintain > 95 req/s
  },
};

// Test data generator
function generateCapsuleData() {
  const hash = Math.random().toString(36).substring(2, 15) + Math.random().toString(36).substring(2, 15);
  const specSig = `sigstore:sha256:${Math.random().toString(36).substring(2, 15)}`;
  const risk = Math.random() * 1.0; // Random risk score between 0 and 1
  const reasons = ['normal_operation', 'budget_violation', 'spam_violation', 'assumption_drift'];
  const reason = reasons[Math.floor(Math.random() * reasons.length)];
  
  return {
    hash: hash,
    specSig: specSig,
    risk: risk,
    reason: reason
  };
}

// GraphQL mutation for publishing capsules
const publishMutation = `
  mutation Publish($hash: ID!, $specSig: String!, $risk: Float!, $reason: String!) {
    publish(hash: $hash, specSig: $specSig, risk: $risk, reason: $reason) {
      hash
      specSig
      riskScore
      reason
      createdAt
      updatedAt
    }
  }
`;

// GraphQL query for retrieving capsules
const capsuleQuery = `
  query Capsule($hash: ID!) {
    capsule(hash: $hash) {
      hash
      specSig
      riskScore
      reason
      createdAt
      updatedAt
    }
  }
`;

export default function () {
  const baseURL = __ENV.LEDGER_URL || 'http://localhost:4000';
  const headers = {
    'Content-Type': 'application/json',
  };

  // Generate test data
  const capsuleData = generateCapsuleData();
  
  // Test 1: Publish capsule
  const publishPayload = {
    query: publishMutation,
    variables: {
      hash: capsuleData.hash,
      specSig: capsuleData.specSig,
      risk: capsuleData.risk,
      reason: capsuleData.reason
    }
  };

  const publishResponse = http.post(`${baseURL}/graphql`, JSON.stringify(publishPayload), {
    headers: headers,
  });

  const publishCheck = check(publishResponse, {
    'publish status is 200': (r) => r.status === 200,
    'publish response has data': (r) => r.json('data.publish') !== undefined,
    'publish response has correct hash': (r) => r.json('data.publish.hash') === capsuleData.hash,
    'publish response has correct risk score': (r) => r.json('data.publish.riskScore') === capsuleData.risk,
  });

  errorRate.add(!publishCheck);

  // Test 2: Query capsule
  const queryPayload = {
    query: capsuleQuery,
    variables: {
      hash: capsuleData.hash
    }
  };

  const queryResponse = http.post(`${baseURL}/graphql`, JSON.stringify(queryPayload), {
    headers: headers,
  });

  const queryCheck = check(queryResponse, {
    'query status is 200': (r) => r.status === 200,
    'query response has data': (r) => r.json('data.capsule') !== undefined,
    'query response has correct hash': (r) => r.json('data.capsule.hash') === capsuleData.hash,
  });

  errorRate.add(!queryCheck);

  // Test 3: Query all capsules (less frequent)
  if (Math.random() < 0.1) { // 10% of requests
    const allCapsulesQuery = `
      query {
        capsules {
          hash
          specSig
          riskScore
          reason
          createdAt
          updatedAt
        }
      }
    `;

    const allCapsulesPayload = {
      query: allCapsulesQuery
    };

    const allCapsulesResponse = http.post(`${baseURL}/graphql`, JSON.stringify(allCapsulesPayload), {
      headers: headers,
    });

    const allCapsulesCheck = check(allCapsulesResponse, {
      'all capsules query status is 200': (r) => r.status === 200,
      'all capsules response has data': (r) => r.json('data.capsules') !== undefined,
    });

    errorRate.add(!allCapsulesCheck);
  }

  // Small sleep to prevent overwhelming the service
  sleep(0.1);
}

// Setup function to verify service is available
export function setup() {
  const baseURL = __ENV.LEDGER_URL || 'http://localhost:4000';
  
  // Health check
  const healthResponse = http.get(`${baseURL}/health`);
  
  if (healthResponse.status !== 200) {
    throw new Error(`Ledger service not available at ${baseURL}`);
  }
  
  console.log(`✅ Ledger service is available at ${baseURL}`);
  return { baseURL };
}

// Teardown function
export function teardown(data) {
  console.log('🏁 Load test completed');
}