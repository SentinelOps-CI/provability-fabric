// SPDX-License-Identifier: Apache-2.0
import { verifyTracePayload } from '../verifyTrace.js';

describe('verifyTracePayload', () => {
  const originalEnforce = process.env.PF_ENFORCE_DSSE;
  const originalTrustRoot = process.env.PF_TRUST_ROOT_PEM;

  afterEach(() => {
    if (originalEnforce === undefined) {
      delete process.env.PF_ENFORCE_DSSE;
    } else {
      process.env.PF_ENFORCE_DSSE = originalEnforce;
    }
    if (originalTrustRoot === undefined) {
      delete process.env.PF_TRUST_ROOT_PEM;
    } else {
      process.env.PF_TRUST_ROOT_PEM = originalTrustRoot;
    }
  });

  it('passes structurally when enforcement is opted out', () => {
    process.env.PF_ENFORCE_DSSE = '0';
    delete process.env.PF_TRUST_ROOT_PEM;
    const result = verifyTracePayload({
      receipt_id: 'rcpt-1',
      tenant: 'tenant-a',
      subject_id: 'user-1',
      query_hash: 'abc',
      index_shard: 'shard-0',
      timestamp: 1,
      result_hash: 'deadbeef',
      sign_alg: 'ed25519',
      sig: 'a'.repeat(64),
    });
    expect(result.valid).toBe(true);
  });

  it('rejects when unset (fail-closed default) without trust root', () => {
    delete process.env.PF_ENFORCE_DSSE;
    delete process.env.PF_TRUST_ROOT_PEM;
    const result = verifyTracePayload({
      receipt_id: 'rcpt-1',
      tenant: 'tenant-a',
      subject_id: 'user-1',
      query_hash: 'abc',
      index_shard: 'shard-0',
      timestamp: 1,
      result_hash: 'deadbeef',
      sign_alg: 'ed25519',
      sig: 'a'.repeat(64),
    });
    expect(result.valid).toBe(false);
    expect(result.reason).toMatch(/trust root/i);
  });

  it('rejects unknown trace format when enforcement is on', () => {
    process.env.PF_ENFORCE_DSSE = '1';
    const result = verifyTracePayload({ foo: 'bar' });
    expect(result.valid).toBe(false);
    expect(result.reason).toBe('unsupported trace format');
  });

  it('rejects unknown trace format when unset (default enforce)', () => {
    delete process.env.PF_ENFORCE_DSSE;
    const result = verifyTracePayload({ foo: 'bar' });
    expect(result.valid).toBe(false);
    expect(result.reason).toBe('unsupported trace format');
  });

  it('rejects receipts missing required fields when enforcement is on', () => {
    process.env.PF_ENFORCE_DSSE = '1';
    const result = verifyTracePayload({
      receipt_id: 'rcpt-1',
      sig: 'abc',
      sign_alg: 'ed25519',
    });
    expect(result.valid).toBe(false);
  });

  it('allows unknown format only when PF_ENFORCE_DSSE=0', () => {
    process.env.PF_ENFORCE_DSSE = '0';
    const result = verifyTracePayload({ foo: 'bar' });
    expect(result.valid).toBe(true);
  });
});
