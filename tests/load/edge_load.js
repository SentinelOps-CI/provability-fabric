// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend } from 'k6/metrics';

// Custom metrics
const errorRate = new Rate('errors');
const p95Latency = new Trend('p95_latency');

// Test configuration
export const options = {
  stages: [
    // Ramp up to 1000 RPS over 2 minutes
    { duration: '2m', target: 1000 },
    // Maintain 1000 RPS for 5 minutes
    { duration: '5m', target: 1000 },
    // Ramp down over 1 minute
    { duration: '1m', target: 0 },
  ],
  thresholds: {
    // Fail if error rate exceeds 1%
    'errors': ['rate<0.01'],
    // Fail if p95 latency exceeds 80ms
    'http_req_duration{status:200}': ['p(95)<80'],
    // Fail if any request takes longer than 150ms
    'http_req_duration': ['max<150'],
  },
};

// Test data
const regions = [
  'https://api.us-west.provability-fabric.org',
  'https://api.us-east.provability-fabric.org',
  'https://api.eu-west.provability-fabric.org'
];

const testCapsules = [
  'sha256:abc123def4567890123456789012345678901234567890abcdef1234567890abcd',
  'sha256:def456abc1237890123456789012345678901234567890abcdef1234567890efgh',
  'sha256:ghi789def4561230123456789012345678901234567890abcdef1234567890ijkl'
];

const testQuotes = [
  { capsule_hash: testCapsules[0], risk_score: 0.15 },
  { capsule_hash: testCapsules[1], risk_score: 0.85 },
  { capsule_hash: testCapsules[2], risk_score: 0.45 }
];

// Main test function
export default function() {
  const region = regions[Math.floor(Math.random() * regions.length)];
  const testType = Math.random() < 0.7 ? 'quote' : 'capsule'; // 70% quotes, 30% capsules
  
  let response;
  let url;
  
  if (testType === 'quote') {
    const quote = testQuotes[Math.floor(Math.random() * testQuotes.length)];
    url = `${region}/quote?capsule_hash=${quote.capsule_hash}&risk_score=${quote.risk_score}`;
    response = http.get(url);
  } else {
    const capsule = testCapsules[Math.floor(Math.random() * testCapsules.length)];
    url = `${region}/capsule/${capsule}`;
    response = http.get(url);
  }
  
  // Record metrics
  const success = check(response, {
    'status is 200': (r) => r.status === 200,
    'response time < 80ms': (r) => r.timings.duration < 80,
    'has cache header': (r) => r.headers['X-Cache'] !== undefined,
    'has region header': (r) => r.headers['X-Cache-Region'] !== undefined,
    'content type is json': (r) => r.headers['Content-Type']?.includes('application/json'),
  });
  
  // Record error rate
  errorRate.add(!success);
  
  // Record latency for successful requests
  if (response.status === 200) {
    p95Latency.add(response.timings.duration);
  }
  
  // Log cache hit/miss ratio
  if (response.headers['X-Cache']) {
    console.log(`Cache ${response.headers['X-Cache']} for ${url}`);
  }
  
  // Small sleep to prevent overwhelming
  sleep(0.1);
}

// Setup function to verify endpoints are available
export function setup() {
  console.log('Starting edge API load test...');
  
  // Test each region's health endpoint
  for (const region of regions) {
    const healthUrl = `${region}/health`;
    const response = http.get(healthUrl);
    
    check(response, {
      [`${region} health check`]: (r) => r.status === 200,
    });
    
    if (response.status !== 200) {
      throw new Error(`Health check failed for ${region}: ${response.status}`);
    }
    
    console.log(`${region} is healthy`);
  }
  
  return { regions, testCapsules, testQuotes };
}

// Teardown function
export function teardown(data) {
  console.log('Edge API load test completed');
  
  // Log final metrics
  console.log(`Final error rate: ${errorRate.value}`);
  console.log(`Final p95 latency: ${p95Latency.value}`);
}

// Handle test results
export function handleSummary(data) {
  const { metrics } = data;
  
  // Check if thresholds were met
  const p95LatencyValue = metrics['http_req_duration{status:200}'].values.p95;
  const errorRateValue = metrics.errors.values.rate;
  
  console.log(`\n=== Edge API Load Test Results ===`);
  console.log(`P95 Latency: ${p95LatencyValue}ms (target: <80ms)`);
  console.log(`Error Rate: ${(errorRateValue * 100).toFixed(2)}% (target: <1%)`);
  console.log(`Total Requests: ${metrics.http_reqs.values.count}`);
  console.log(`Average RPS: ${metrics.http_reqs.values.rate.toFixed(2)}`);
  
  // Determine if test passed
  const passed = p95LatencyValue < 80 && errorRateValue < 0.01;
  
  if (passed) {
    console.log(`✅ Test PASSED - All thresholds met`);
  } else {
    console.log(`❌ Test FAILED - Thresholds exceeded`);
    
    if (p95LatencyValue >= 80) {
      console.log(`  - P95 latency ${p95LatencyValue}ms exceeds 80ms threshold`);
    }
    
    if (errorRateValue >= 0.01) {
      console.log(`  - Error rate ${(errorRateValue * 100).toFixed(2)}% exceeds 1% threshold`);
    }
  }
  
  return {
    'edge-load-test-results.json': JSON.stringify(data, null, 2),
    stdout: `Edge API load test ${passed ? 'PASSED' : 'FAILED'}\n`
  };
}