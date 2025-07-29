// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend, Counter } from 'k6/metrics';

// Custom metrics for TRUST-FIRE validation
const errorRate = new Rate('errors');
const p95Latency = new Trend('p95_latency');
const cacheHitRatio = new Trend('cache_hit_ratio');
const cachePurgeCount = new Counter('cache_purge_requests');

// Test configuration for TRUST-FIRE Phase 1
export const options = {
  stages: [
    // Ramp up to 2500 RPS over 5 minutes
    { duration: '5m', target: 2500 },
    // Maintain 2500 RPS for 30 minutes (TRUST-FIRE requirement)
    { duration: '30m', target: 2500 },
    // Ramp down over 2 minutes
    { duration: '2m', target: 0 },
  ],
  thresholds: {
    // TRUST-FIRE Phase 1 Gates
    'errors': ['rate<0.005'],           // Error rate < 0.5%
    'http_req_duration{status:200}': ['p(95)<90'], // P95 latency < 90ms
    'http_req_duration': ['max<150'],   // Max latency < 150ms
    'cache_hit_ratio': ['value>0.20'],  // Cache hit ratio > 20%
  },
};

// Test data for edge API endpoints
const regions = [
  'https://api.us-west.provability-fabric.org',
  'https://api.us-east.provability-fabric.org',
  'https://api.eu-west.provability-fabric.org'
];

const testCapsules = [
  'sha256:abc123def4567890123456789012345678901234567890abcdef1234567890abcd',
  'sha256:def456abc1237890123456789012345678901234567890abcdef1234567890efgh',
  'sha256:ghi789def4561230123456789012345678901234567890abcdef1234567890ijkl',
  'sha256:jkl012ghi789456123456789012345678901234567890abcdef1234567890mnop',
  'sha256:mno345jkl012789123456789012345678901234567890abcdef1234567890qrst'
];

const testQuotes = [
  { capsule_hash: testCapsules[0], risk_score: 0.15 },
  { capsule_hash: testCapsules[1], risk_score: 0.85 },
  { capsule_hash: testCapsules[2], risk_score: 0.45 },
  { capsule_hash: testCapsules[3], risk_score: 0.75 },
  { capsule_hash: testCapsules[4], risk_score: 0.25 }
];

// Cache purge test capsules (10 random hashes as per TRUST-FIRE spec)
const purgeCapsules = [
  'sha256:purge1def4567890123456789012345678901234567890abcdef1234567890abcd',
  'sha256:purge2abc1237890123456789012345678901234567890abcdef1234567890efgh',
  'sha256:purge3ghi7894561230123456789012345678901234567890abcdef1234567890ijkl',
  'sha256:purge4jkl012789456123456789012345678901234567890abcdef1234567890mnop',
  'sha256:purge5mno345012789123456789012345678901234567890abcdef1234567890qrst',
  'sha256:purge6pqr678345012123456789012345678901234567890abcdef1234567890uvwx',
  'sha256:purge7stu901678345123456789012345678901234567890abcdef1234567890yzab',
  'sha256:purge8vwx234901678123456789012345678901234567890abcdef1234567890cdef',
  'sha256:purge9yza567234901123456789012345678901234567890abcdef1234567890fghi',
  'sha256:purge0bcd890567234123456789012345678901234567890abcdef1234567890ijkl'
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
  
  // Record metrics for TRUST-FIRE validation
  const success = check(response, {
    'status is 200': (r) => r.status === 200,
    'response time < 90ms': (r) => r.timings.duration < 90,
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
  
  // Record cache hit/miss ratio
  if (response.headers['X-Cache']) {
    const isHit = response.headers['X-Cache'] === 'HIT';
    cacheHitRatio.add(isHit ? 1 : 0);
  }
  
  // Small sleep to prevent overwhelming
  sleep(0.1);
}

// Setup function to verify endpoints are available
export function setup() {
  console.log('Starting TRUST-FIRE Phase 1: Edge Traffic Surge...');
  
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
  
  return { regions, testCapsules, testQuotes, purgeCapsules };
}

// Teardown function
export function teardown(data) {
  console.log('TRUST-FIRE Phase 1: Edge Traffic Surge completed');
  
  // Log final metrics for TRUST-FIRE validation
  console.log(`Final error rate: ${errorRate.value}`);
  console.log(`Final p95 latency: ${p95Latency.value}`);
  console.log(`Cache hit ratio trend: ${cacheHitRatio.value}`);
}

// Handle test results for TRUST-FIRE validation
export function handleSummary(data) {
  const { metrics } = data;
  
  // Check TRUST-FIRE Phase 1 Gates
  const p95LatencyValue = metrics['http_req_duration{status:200}'].values.p95;
  const errorRateValue = metrics.errors.values.rate;
  const cacheHitRatioValue = metrics.cache_hit_ratio.values.avg;
  
  console.log(`\n=== TRUST-FIRE Phase 1 Results ===`);
  console.log(`P95 Latency: ${p95LatencyValue}ms (target: <90ms)`);
  console.log(`Error Rate: ${(errorRateValue * 100).toFixed(2)}% (target: <0.5%)`);
  console.log(`Cache Hit Ratio: ${(cacheHitRatioValue * 100).toFixed(2)}% (target: >20%)`);
  console.log(`Total Requests: ${metrics.http_reqs.values.count}`);
  console.log(`Average RPS: ${metrics.http_reqs.values.rate.toFixed(2)}`);
  
  // TRUST-FIRE Phase 1 Gate validation
  const latencyPass = p95LatencyValue < 90;
  const errorPass = errorRateValue < 0.005;
  const cachePass = cacheHitRatioValue > 0.20;
  
  const allGatesPass = latencyPass && errorPass && cachePass;
  
  if (allGatesPass) {
    console.log(`✅ TRUST-FIRE Phase 1 PASSED - All gates satisfied`);
  } else {
    console.log(`❌ TRUST-FIRE Phase 1 FAILED - Gates not satisfied`);
    
    if (!latencyPass) {
      console.log(`  - P95 latency ${p95LatencyValue}ms exceeds 90ms threshold`);
    }
    
    if (!errorPass) {
      console.log(`  - Error rate ${(errorRateValue * 100).toFixed(2)}% exceeds 0.5% threshold`);
    }
    
    if (!cachePass) {
      console.log(`  - Cache hit ratio ${(cacheHitRatioValue * 100).toFixed(2)}% below 20% threshold`);
    }
  }
  
  return {
    'trust-fire-phase1-results.json': JSON.stringify(data, null, 2),
    stdout: `TRUST-FIRE Phase 1 ${allGatesPass ? 'PASSED' : 'FAILED'}\n`
  };
}

// Cache purge test function (called at t+15min as per TRUST-FIRE spec)
export function cachePurgeTest() {
  console.log('Executing cache purge test at t+15min...');
  
  const region = regions[0]; // Use primary region for purge test
  
  // Test cache purge with 10 random capsule hashes
  for (const capsuleHash of purgeCapsules) {
    const purgeUrl = `${region}/admin/purge`;
    const purgePayload = JSON.stringify({ capsule_hash: capsuleHash });
    
    const response = http.post(purgeUrl, purgePayload, {
      headers: { 'Content-Type': 'application/json' }
    });
    
    check(response, {
      'purge status is 200': (r) => r.status === 200,
      'purge response is json': (r) => r.headers['Content-Type']?.includes('application/json'),
    });
    
    cachePurgeCount.add(1);
    
    if (response.status === 200) {
      console.log(`Cache purge successful for ${capsuleHash}`);
    } else {
      console.log(`Cache purge failed for ${capsuleHash}: ${response.status}`);
    }
  }
  
  console.log(`Cache purge test completed. Purged ${cachePurgeCount.value} capsules.`);
}