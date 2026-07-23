// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import crypto from 'crypto';
import fs from 'fs';
import path from 'path';

export const ENV_TRUST_ROOT_PEM = 'PF_TRUST_ROOT_PEM';
export const ENV_JWKS_URL = 'PF_JWKS_URL';
export const ENV_ENFORCE_DSSE = 'PF_ENFORCE_DSSE';
export const ACCESS_RECEIPT_TYPE = 'application/vnd.provability-fabric.access-receipt';

export interface DsseSignature {
  keyid: string;
  sig: string;
  alg?: string;
}

export interface DsseEnvelope {
  payloadType: string;
  payload: string;
  signatures: DsseSignature[];
}

export interface VerifyResult {
  valid: boolean;
  reason?: string;
}

export interface AccessReceiptPayload {
  receipt_id: string;
  tenant: string;
  subject_id: string;
  query_hash: string;
  index_shard: string;
  timestamp: number;
  result_hash: string;
  result_count?: number;
  query_time_ms?: number;
  signature?: string;
}

/** Fail-closed by default; opt out only with PF_ENFORCE_DSSE=0 or false. */
export function enforceDsse(): boolean {
  const v = (process.env[ENV_ENFORCE_DSSE] ?? '').trim();
  if (v === '0' || v.toLowerCase() === 'false') return false;
  return true;
}

export function loadTrustRootPem(): Buffer {
  const raw = (process.env[ENV_TRUST_ROOT_PEM] ?? '').trim();
  if (!raw) {
    throw new Error(`${ENV_TRUST_ROOT_PEM} unset`);
  }
  if (fs.existsSync(raw)) {
    return fs.readFileSync(raw);
  }
  return Buffer.from(raw, 'utf8');
}

export function trustRootConfigured(): boolean {
  try {
    loadTrustRootPem();
    return true;
  } catch {
    return false;
  }
}

function loadEd25519PublicKey(pemData: Buffer): crypto.KeyObject {
  return crypto.createPublicKey({ key: pemData, format: 'pem' });
}

function decodeSig(sigB64: string): Buffer {
  try {
    return Buffer.from(sigB64, 'base64');
  } catch {
    throw new Error('sig_decode_error');
  }
}

export function verifySignature(message: Buffer, sigB64: string, pemPub: Buffer): boolean {
  try {
    const sig = decodeSig(sigB64);
    const key = loadEd25519PublicKey(pemPub);
    return crypto.verify(null, message, key, sig);
  } catch {
    return false;
  }
}

export function verifyEnvelope(
  envelope: DsseEnvelope,
  expectedPayloadType: string = ACCESS_RECEIPT_TYPE,
): VerifyResult {
  if (expectedPayloadType && envelope.payloadType !== expectedPayloadType) {
    return { valid: false, reason: 'payload_type_mismatch' };
  }
  if (!envelope.signatures?.length) {
    return { valid: false, reason: 'no_signatures' };
  }
  let payload: Buffer;
  try {
    payload = Buffer.from(envelope.payload, 'base64');
  } catch {
    return { valid: false, reason: 'payload_decode_error' };
  }
  let pemPub: Buffer;
  try {
    pemPub = loadTrustRootPem();
  } catch {
    return { valid: false, reason: 'trust_root_not_configured' };
  }
  for (const sig of envelope.signatures) {
    if (sig.alg && sig.alg.toLowerCase() !== 'ed25519') {
      continue;
    }
    if (verifySignature(payload, sig.sig, pemPub)) {
      return { valid: true };
    }
  }
  return { valid: false, reason: 'signature_mismatch' };
}

export function canonicalReceiptPayload(receipt: AccessReceiptPayload): string {
  const obj: Record<string, unknown> = {
    index_shard: receipt.index_shard,
    query_hash: receipt.query_hash,
    receipt_id: receipt.receipt_id,
    result_hash: receipt.result_hash,
    signature: receipt.signature ?? '',
    subject_id: receipt.subject_id,
    tenant: receipt.tenant,
    timestamp: receipt.timestamp,
  };
  if (receipt.result_count) {
    obj.result_count = receipt.result_count;
  }
  if (receipt.query_time_ms) {
    obj.query_time_ms = receipt.query_time_ms;
  }
  const keys = Object.keys(obj).sort();
  const sorted: Record<string, unknown> = {};
  for (const k of keys) {
    sorted[k] = obj[k];
  }
  return JSON.stringify(sorted);
}

export function verifyAccessReceipt(
  receipt: AccessReceiptPayload,
  signAlg: string,
  sig: string,
): { ok: boolean; reason?: string } {
  if (!receipt.receipt_id) return { ok: false, reason: 'receipt ID is required' };
  if (!receipt.tenant) return { ok: false, reason: 'receipt tenant is required' };
  if (!receipt.index_shard) return { ok: false, reason: 'receipt index shard is required' };
  if (signAlg !== 'ed25519') return { ok: false, reason: `unsupported signature algorithm: ${signAlg}` };
  if (!sig) return { ok: false, reason: 'receipt signature is required' };
  if (!enforceDsse()) return { ok: true };
  if (!trustRootConfigured()) return { ok: false, reason: 'trust root not configured' };
  const payload = Buffer.from(canonicalReceiptPayload(receipt), 'utf8');
  const pemPub = loadTrustRootPem();
  if (!verifySignature(payload, sig, pemPub)) {
    return { ok: false, reason: 'signature_mismatch' };
  }
  return { ok: true };
}

export function resolveFixtureDir(): string {
  const candidates = [
    path.join(process.cwd(), 'tests', 'fixtures', 'crypto'),
    path.join(process.cwd(), '..', '..', 'tests', 'fixtures', 'crypto'),
    path.join(process.cwd(), '..', '..', '..', 'tests', 'fixtures', 'crypto'),
  ];
  for (const c of candidates) {
    if (fs.existsSync(path.join(c, 'ed25519_public.pem'))) {
      return c;
    }
  }
  throw new Error('crypto fixtures not found');
}
