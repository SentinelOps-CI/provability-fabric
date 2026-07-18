// SPDX-License-Identifier: Apache-2.0
// CI-sized k6 smoke against a local mock (no external SaaS).
import http from 'k6/http';
import { check, sleep } from 'k6';

export const options = {
  vus: 2,
  duration: '15s',
  thresholds: {
    http_req_failed: ['rate<0.01'],
    http_req_duration: ['p(95)<500'],
  },
};

const BASE = __ENV.BASE_URL || 'http://127.0.0.1:8080';

export default function () {
  const health = http.get(`${BASE}/health`);
  check(health, { 'health 200': (r) => r.status === 200 });
  const proof = http.post(`${BASE}/proof`, JSON.stringify({ n: 1 }), {
    headers: { 'Content-Type': 'application/json' },
  });
  check(proof, { 'proof 200': (r) => r.status === 200 });
  sleep(0.2);
}
