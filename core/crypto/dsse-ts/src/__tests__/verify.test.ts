// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import fs from 'fs';
import path from 'path';
import {
  ACCESS_RECEIPT_TYPE,
  DsseEnvelope,
  ENV_ENFORCE_DSSE,
  ENV_TRUST_ROOT_PEM,
  resolveFixtureDir,
  verifyEnvelope,
} from '../verify.js';

describe('dsse verify', () => {
  const fixtureDir = resolveFixtureDir();

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
});
