import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend } from 'k6/metrics';

// Custom metrics
const planLatency = new Trend('plan_latency_ms');
const retrievalLatency = new Trend('retrieval_latency_ms');
const kernelLatency = new Trend('kernel_latency_ms');
const egressLatency = new Trend('egress_latency_ms');
const totalLatency = new Trend('total_latency_ms');
const errorRate = new Rate('errors');

// Test configuration
export const options = {
  stages: [
    { duration: '30s', target: 100 }, // Ramp up
    { duration: '60s', target: 1000 }, // Ramp to target
    { duration: '60s', target: 1000 }, // Stay at target
    { duration: '30s', target: 0 }, // Ramp down
  ],
  thresholds: {
    // SLO thresholds
    'p(95)': ['total_latency_ms < 2000'], // p95 < 2.0s
    'p(99)': ['total_latency_ms < 4000'], // p99 < 4.0s
    'errors': ['rate < 0.001'], // Error rate < 0.1%
    
    // Component budget thresholds
    'p(95)': ['plan_latency_ms < 150'], // Plan budget
    'p(95)': ['retrieval_latency_ms < 600'], // Retrieval budget
    'p(95)': ['kernel_latency_ms < 120'], // Kernel budget
    'p(95)': ['egress_latency_ms < 400'], // Egress budget
  },
};

// Test data
const testPlans = [
  {
    plan_id: 'test_plan_1',
    tenant: 'test-tenant',
    subject: {
      id: 'test-subject',
      caps: ['read_docs', 'send_email']
    },
    input_channels: {
      system: {
        hash: 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456',
        policy_hash: 'policy_hash_1'
      },
      user: {
        content_hash: 'user_input_hash_1',
        quoted: true
      },
      retrieved: [
        {
          receipt_id: 'receipt_1',
          content_hash: 'retrieved_content_hash_1',
          quoted: true,
          labels: ['public']
        }
      ],
      file: []
    },
    steps: [
      {
        tool: 'retrieval',
        args: { query: 'test query' },
        caps_required: ['read_docs'],
        labels_in: ['public'],
        labels_out: ['documents']
      }
    ],
    constraints: {
      budget: 1.0,
      pii: false,
      dp_epsilon: 0.1,
      dp_delta: 1e-6,
      latency_max: 30.0
    },
    system_prompt_hash: 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456',
    created_at: Math.floor(Date.now() / 1000),
    expires_at: Math.floor(Date.now() / 1000) + 3600
  }
];

// Helper function to extract timing headers
function extractTimings(response) {
  const headers = response.headers;
  return {
    plan: parseInt(headers['X-PF-Plan-ms']) || 0,
    retrieval: parseInt(headers['X-PF-Retrieval-ms']) || 0,
    kernel: parseInt(headers['X-PF-Kernel-ms']) || 0,
    egress: parseInt(headers['X-PF-Egress-ms']) || 0,
    total: parseInt(headers['X-PF-Total-ms']) || 0
  };
}

// Main test function
export default function() {
  const baseUrl = __ENV.BASE_URL || 'http://localhost:8080';
  const plan = testPlans[Math.floor(Math.random() * testPlans.length)];
  
  // Test plan validation
  const planStart = Date.now();
  const planResponse = http.post(`${baseUrl}/validate`, JSON.stringify(plan), {
    headers: {
      'Content-Type': 'application/json',
      'X-Test-ID': `test_${Date.now()}_${Math.random()}`
    }
  });
  
  const planTimings = extractTimings(planResponse);
  const planDuration = Date.now() - planStart;
  
  // Record component latencies
  planLatency.add(planTimings.plan);
  retrievalLatency.add(planTimings.retrieval);
  kernelLatency.add(planTimings.kernel);
  egressLatency.add(planTimings.egress);
  totalLatency.add(planTimings.total);
  
  // Check response
  const success = check(planResponse, {
    'status is 200': (r) => r.status === 200,
    'response time < 2s': (r) => r.timings.duration < 2000,
    'has timing headers': (r) => r.headers['X-PF-Total-ms'] !== undefined,
    'plan budget respected': () => planTimings.plan <= 150,
    'retrieval budget respected': () => planTimings.retrieval <= 600,
    'kernel budget respected': () => planTimings.kernel <= 120,
    'egress budget respected': () => planTimings.egress <= 400,
  });
  
  if (!success) {
    errorRate.add(1);
    console.log(`Test failed: ${planResponse.status} - ${planResponse.body}`);
  } else {
    errorRate.add(0);
  }
  
  // Test plan execution
  if (planResponse.status === 200) {
    const executeResponse = http.post(`${baseUrl}/execute`, JSON.stringify({
      plan_id: plan.plan_id,
      tenant: plan.tenant
    }), {
      headers: {
        'Content-Type': 'application/json',
        'X-Test-ID': `execute_${Date.now()}_${Math.random()}`
      }
    });
    
    const executeTimings = extractTimings(executeResponse);
    
    check(executeResponse, {
      'execution status is 200': (r) => r.status === 200,
      'execution time < 2s': (r) => r.timings.duration < 2000,
      'execution has timing headers': (r) => r.headers['X-PF-Total-ms'] !== undefined,
    });
  }
  
  // Random sleep to simulate real usage
  sleep(Math.random() * 0.1);
}

// Setup function for test initialization
export function setup() {
  console.log('Starting SLO performance test');
  console.log(`Base URL: ${__ENV.BASE_URL || 'http://localhost:8080'}`);
  console.log('SLO Targets:');
  console.log('  - p95 < 2.0s');
  console.log('  - p99 < 4.0s');
  console.log('  - Error rate < 0.1%');
  console.log('Component Budgets:');
  console.log('  - Plan: ≤ 150ms');
  console.log('  - Retrieval: ≤ 600ms');
  console.log('  - Kernel: ≤ 120ms');
  console.log('  - Egress: ≤ 400ms');
}

// Teardown function for cleanup
export function teardown(data) {
  console.log('SLO performance test completed');
} 