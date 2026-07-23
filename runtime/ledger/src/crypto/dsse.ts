// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import crypto from 'crypto';
import fs from 'fs';

export const ENV_TRUST_ROOT_PEM = 'PF_TRUST_ROOT_PEM';
export const ENV_ENFORCE_DSSE = 'PF_ENFORCE_DSSE';
export const ACCESS_RECEIPT_TYPE = 'application/vnd.provability-fabric.access-receipt';

export interface DsseEnvelope {
  payloadType: string;
  payload: string;
  signatures: Array<{ keyid: string; sig: string; alg?: string }>;
}

/** Fail-closed by default; opt out only with PF_ENFORCE_DSSE=0 or false. */
export function enforceDsse(): boolean {
  const v = (process.env[ENV_ENFORCE_DSSE] ?? '').trim();
  if (v === '0' || v.toLowerCase() === 'false') return false;
  return true;
}

function loadTrustRootPem(): Buffer {
  const raw = (process.env[ENV_TRUST_ROOT_PEM] ?? '').trim();
  if (!raw) {
    throw new Error(`${ENV_TRUST_ROOT_PEM} unset`);
  }
  if (fs.existsSync(raw)) {
    return fs.readFileSync(raw);
  }
  return Buffer.from(raw, 'utf8');
}

export function verifyEnvelope(envelope: DsseEnvelope, expected = ACCESS_RECEIPT_TYPE): boolean {
  if (envelope.payloadType !== expected) {
    return false;
  }
  if (!envelope.signatures?.length) {
    return false;
  }
  const payload = Buffer.from(envelope.payload, 'base64');
  const pem = loadTrustRootPem();
  const key = crypto.createPublicKey({ key: pem, format: 'pem' });
  for (const sig of envelope.signatures) {
    if (sig.alg && sig.alg.toLowerCase() !== 'ed25519') {
      continue;
    }
    try {
      const sigBytes = Buffer.from(sig.sig, 'base64');
      if (crypto.verify(null, payload, key, sigBytes)) {
        return true;
      }
    } catch {
      // try next signature
    }
  }
  return false;
}

export interface ReceiptFields {
  receipt_id: string;
  tenant: string;
  subject_id: string;
  query_hash: string;
  index_shard: string;
  timestamp: number;
  result_hash: string;
  result_count?: number;
  query_time_ms?: number;
}

export function canonicalReceiptPayload(receipt: ReceiptFields): string {
  const obj: Record<string, unknown> = {
    index_shard: receipt.index_shard,
    query_hash: receipt.query_hash,
    receipt_id: receipt.receipt_id,
    result_hash: receipt.result_hash,
    signature: '',
    subject_id: receipt.subject_id,
    tenant: receipt.tenant,
    timestamp: receipt.timestamp,
  };
  if (receipt.result_count) obj.result_count = receipt.result_count;
  if (receipt.query_time_ms) obj.query_time_ms = receipt.query_time_ms;
  const keys = Object.keys(obj).sort();
  const sorted: Record<string, unknown> = {};
  for (const k of keys) sorted[k] = obj[k];
  return JSON.stringify(sorted);
}

export function verifyReceiptSignature(
  receipt: ReceiptFields,
  signAlg: string,
  sig: string,
): boolean {
  if (!receipt.receipt_id || !receipt.tenant || !receipt.index_shard) {
    return false;
  }
  if (signAlg !== 'ed25519' || !sig) {
    return false;
  }
  if (!enforceDsse()) {
    return true;
  }
  try {
    const payload = Buffer.from(canonicalReceiptPayload(receipt), 'utf8');
    const pem = loadTrustRootPem();
    const key = crypto.createPublicKey({ key: pem, format: 'pem' });
    return crypto.verify(null, payload, key, Buffer.from(sig, 'base64'));
  } catch {
    return false;
  }
}
