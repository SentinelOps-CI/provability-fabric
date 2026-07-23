// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import fs from 'fs';
import path from 'path';
import {
  ACCESS_RECEIPT_TYPE,
  DsseEnvelope,
  ENV_ENFORCE_DSSE,
  ENV_TRUST_ROOT_PEM,
  enforceDsse,
  resolveFixtureDir,
  verifyAccessReceipt,
  verifyEnvelope,
} from '../verify.js';

describe('dsse verify', () => {
  const fixtureDir = resolveFixtureDir();
  const originalEnforce = process.env[ENV_ENFORCE_DSSE];
  const originalTrust = process.env[ENV_TRUST_ROOT_PEM];

  afterEach(() => {
    if (originalEnforce === undefined) {
      delete process.env[ENV_ENFORCE_DSSE];
    } else {
      process.env[ENV_ENFORCE_DSSE] = originalEnforce;
    }
    if (originalTrust === undefined) {
      delete process.env[ENV_TRUST_ROOT_PEM];
    } else {
      process.env[ENV_TRUST_ROOT_PEM] = originalTrust;
    }
  });

  beforeEach(() => {
    process.env[ENV_TRUST_ROOT_PEM] = path.join(fixtureDir, 'ed25519_public.pem');
    process.env[ENV_ENFORCE_DSSE] = '1';
  });

  it('accepts valid fixture envelope', () => {
    const env = JSON.parse(
      fs.readFileSync(path.join(fixtureDir, 'dsse_sample_envelope.json'), 'utf8'),
    ) as DsseEnvelope;
    const result = verifyEnvelope(env, ACCESS_RECEIPT_TYPE);
    expect(result.valid).toBe(true);
  });

  it('rejects tampered signature', () => {
    const env = JSON.parse(
      fs.readFileSync(path.join(fixtureDir, 'dsse_sample_envelope.json'), 'utf8'),
    ) as DsseEnvelope;
    env.signatures[0].sig = env.signatures[0].sig.slice(0, -4) + 'AAAA';
    const result = verifyEnvelope(env, ACCESS_RECEIPT_TYPE);
    expect(result.valid).toBe(false);
  });

  it('enforceDsse: unset and 1 enforce; 0/false opt out', () => {
    delete process.env[ENV_ENFORCE_DSSE];
    expect(enforceDsse()).toBe(true);
    process.env[ENV_ENFORCE_DSSE] = '1';
    expect(enforceDsse()).toBe(true);
    process.env[ENV_ENFORCE_DSSE] = '0';
    expect(enforceDsse()).toBe(false);
    process.env[ENV_ENFORCE_DSSE] = 'false';
    expect(enforceDsse()).toBe(false);
  });

  it('rejects receipt without trust root when unset', () => {
    delete process.env[ENV_ENFORCE_DSSE];
    delete process.env[ENV_TRUST_ROOT_PEM];
    const result = verifyAccessReceipt(
      {
        receipt_id: 'rcpt-1',
        tenant: 'tenant-a',
        subject_id: 'user-1',
        query_hash: 'abc',
        index_shard: 'shard-0',
        timestamp: 1,
        result_hash: 'deadbeef',
      },
      'ed25519',
      'deadbeef',
    );
    expect(result.ok).toBe(false);
    expect(result.reason).toMatch(/trust root/i);
  });

  it('structural pass when PF_ENFORCE_DSSE=0', () => {
    process.env[ENV_ENFORCE_DSSE] = '0';
    delete process.env[ENV_TRUST_ROOT_PEM];
    const result = verifyAccessReceipt(
      {
        receipt_id: 'rcpt-1',
        tenant: 'tenant-a',
        subject_id: 'user-1',
        query_hash: 'abc',
        index_shard: 'shard-0',
        timestamp: 1,
        result_hash: 'deadbeef',
      },
      'ed25519',
      'deadbeef',
    );
    expect(result.ok).toBe(true);
  });
});
