// SPDX-License-Identifier: Apache-2.0
// CI-sized multi-region edge smoke against local mock stack (no live SaaS).
import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate } from 'k6/metrics';

const errorRate = new Rate('region_errors');

export const options = {
  vus: 3,
  duration: '12s',
  thresholds: {
    http_req_failed: ['rate<0.01'],
    http_req_duration: ['p(95)<400'],
    region_errors: ['rate<0.01'],
    checks: ['rate>0.99'],
  },
};

const REGIONS = (
  __ENV.REGION_URLS ||
  'http://127.0.0.1:8081,http://127.0.0.1:8082,http://127.0.0.1:8083'
).split(',');

export default function () {
  for (const base of REGIONS) {
    const health = http.get(`${base}/health`);
    const okHealth = check(health, {
      [`${base} health 200`]: (r) => r.status === 200,
    });
    errorRate.add(!okHealth);

    const quote = http.get(`${base}/quote?capsule_hash=sha256:ci`);
    const okQuote = check(quote, {
      [`${base} quote 200`]: (r) => r.status === 200,
    });
    errorRate.add(!okQuote);

    const proof = http.post(`${base}/proof`, JSON.stringify({ n: 1 }), {
      headers: { 'Content-Type': 'application/json' },
    });
    const okProof = check(proof, {
      [`${base} proof 200`]: (r) => r.status === 200,
    });
    errorRate.add(!okProof);
  }
  sleep(0.15);
}
