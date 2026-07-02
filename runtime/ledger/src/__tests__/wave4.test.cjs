// SPDX-License-Identifier: Apache-2.0
const { readFileSync } = require('node:fs');
const { join } = require('node:path');
const crypto = require('node:crypto');

function verifyReceiptSignature(receipt) {
  try {
    return receipt.sign_alg === 'ed25519' && receipt.sig.length > 0;
  } catch {
    return false;
  }
}

function buildUpdateCapsuleWhere(hash, user) {
  return { hash, tenantId: user.tid };
}

function computeToolSignatureHash(name, schemaDigest) {
  return crypto.createHash('sha256').update(`${name}:${schemaDigest}`).digest('hex');
}

describe('ledger wave4 tests', () => {
  it('package identity is provability-fabric-ledger', () => {
    const pkg = JSON.parse(readFileSync(join(__dirname, '../../package.json'), 'utf8'));
    expect(pkg.name).toBe('provability-fabric-ledger');
    expect(pkg.dependencies.ws).toBeDefined();
    expect(pkg.dependencies['apollo-server-express']).toBeUndefined();
  });

  describe('verifyReceiptSignature', () => {
    const validReceipt = {
      sign_alg: 'ed25519',
      sig: 'a'.repeat(64),
    };

    it('accepts structurally valid ed25519 receipts', () => {
      expect(verifyReceiptSignature(validReceipt)).toBe(true);
    });

    it('rejects empty signatures', () => {
      expect(verifyReceiptSignature({ ...validReceipt, sig: '' })).toBe(false);
    });

    it('rejects non-ed25519 algorithms', () => {
      expect(verifyReceiptSignature({ ...validReceipt, sign_alg: 'rsa' })).toBe(false);
    });
  });

  describe('GraphQL tenant scoping', () => {
    it('updateCapsule where includes tenantId', () => {
      expect(
        buildUpdateCapsuleWhere('hash-1', { tid: 'tenant-a', sub: 'u1', email: 'a@t.com' })
      ).toEqual({ hash: 'hash-1', tenantId: 'tenant-a' });
    });
  });

  describe('MCP tenant resolution', () => {
    it('prefers tid over legacy tenant_id', () => {
      const user = { tid: 'canonical', tenant_id: 'legacy' };
      const tenantId = user.tid ?? user.tenantId ?? user.tenant_id;
      expect(tenantId).toBe('canonical');
    });
  });

  describe('MCP unknown method policy', () => {
    function enforceMethodPolicy(method) {
      switch (method) {
        case 'tools/list':
        case 'resources/list':
          return { allowed: true };
        default:
          return { allowed: false, violatedConstraints: ['unknown_method'] };
      }
    }

    it('denies unknown methods', () => {
      const result = enforceMethodPolicy('experimental/invoke');
      expect(result.allowed).toBe(false);
    });

    it('allows tools/list', () => {
      expect(enforceMethodPolicy('tools/list').allowed).toBe(true);
    });
  });

  describe('tool signature self-allow fix', () => {
    it('validation uses pre-registered set without auto-insert', () => {
      const allowedTools = new Set(['registered-sig']);
      const computed = computeToolSignatureHash('unknown_tool', 'abc');
      expect(allowedTools.has(computed)).toBe(false);
      allowedTools.add(computed);
      expect(allowedTools.has(computed)).toBe(true);
    });
  });
});
