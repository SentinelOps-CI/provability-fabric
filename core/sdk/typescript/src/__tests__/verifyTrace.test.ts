// SPDX-License-Identifier: Apache-2.0
import { verifyTracePayload } from '../verifyTrace.js';

describe('verifyTracePayload', () => {
  const originalEnforce = process.env.PF_ENFORCE_DSSE;

  afterEach(() => {
    if (originalEnforce === undefined) {
      delete process.env.PF_ENFORCE_DSSE;
    } else {
      process.env.PF_ENFORCE_DSSE = originalEnforce;
    }
  });

  it('passes structurally when enforcement is off', () => {
    delete process.env.PF_ENFORCE_DSSE;
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

  it('rejects unknown trace format when enforcement is on', () => {
    process.env.PF_ENFORCE_DSSE = '1';
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
});
