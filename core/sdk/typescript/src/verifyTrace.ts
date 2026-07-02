// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import crypto from 'crypto';
import fs from 'fs';

const ENV_TRUST_ROOT_PEM = 'PF_TRUST_ROOT_PEM';
const ENV_ENFORCE_DSSE = 'PF_ENFORCE_DSSE';
const ACCESS_RECEIPT_TYPE = 'application/vnd.provability-fabric.access-receipt';

interface DsseEnvelope {
  payloadType: string;
  payload: string;
  signatures: Array<{ keyid: string; sig: string; alg?: string }>;
}

interface AccessReceiptPayload {
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

export interface TraceVerificationResult {
  valid: boolean;
  reason?: string;
  trace?: unknown;
}

function enforceDsse(): boolean {
  const v = (process.env[ENV_ENFORCE_DSSE] ?? '').trim();
  return v === '1' || v.toLowerCase() === 'true';
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

function verifyEnvelope(envelope: DsseEnvelope): { valid: boolean; reason?: string } {
  if (envelope.payloadType !== ACCESS_RECEIPT_TYPE) {
    return { valid: false, reason: 'payload_type_mismatch' };
  }
  if (!envelope.signatures?.length) {
    return { valid: false, reason: 'no_signatures' };
  }
  const payload = Buffer.from(envelope.payload, 'base64');
  const pem = loadTrustRootPem();
  const key = crypto.createPublicKey({ key: pem, format: 'pem' });
  for (const sig of envelope.signatures) {
    if (sig.alg && sig.alg.toLowerCase() !== 'ed25519') continue;
    try {
      if (crypto.verify(null, payload, key, Buffer.from(sig.sig, 'base64'))) {
        return { valid: true };
      }
    } catch {
      // try next
    }
  }
  return { valid: false, reason: 'signature_mismatch' };
}

function canonicalReceiptPayload(receipt: AccessReceiptPayload): string {
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
  if (receipt.result_count) obj.result_count = receipt.result_count;
  if (receipt.query_time_ms) obj.query_time_ms = receipt.query_time_ms;
  const keys = Object.keys(obj).sort();
  const sorted: Record<string, unknown> = {};
  for (const k of keys) sorted[k] = obj[k];
  return JSON.stringify(sorted);
}

function verifyAccessReceipt(
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
  try {
    const payload = Buffer.from(canonicalReceiptPayload(receipt), 'utf8');
    const pem = loadTrustRootPem();
    const key = crypto.createPublicKey({ key: pem, format: 'pem' });
    if (!crypto.verify(null, payload, key, Buffer.from(sig, 'base64'))) {
      return { ok: false, reason: 'signature_mismatch' };
    }
    return { ok: true };
  } catch {
    return { ok: false, reason: 'trust root not configured' };
  }
}

function asEnvelope(trace: unknown): DsseEnvelope | null {
  if (!trace || typeof trace !== 'object') return null;
  const candidate = trace as Record<string, unknown>;
  if (
    typeof candidate.payloadType === 'string' &&
    typeof candidate.payload === 'string' &&
    Array.isArray(candidate.signatures)
  ) {
    return candidate as unknown as DsseEnvelope;
  }
  if (candidate.envelope && typeof candidate.envelope === 'object') {
    return candidate.envelope as DsseEnvelope;
  }
  return null;
}

function asReceipt(trace: unknown): { receipt: AccessReceiptPayload; signAlg: string; sig: string } | null {
  if (!trace || typeof trace !== 'object') return null;
  const t = trace as Record<string, unknown>;
  if (typeof t.receipt_id !== 'string' || typeof t.sig !== 'string') return null;
  return {
    receipt: {
      receipt_id: String(t.receipt_id),
      tenant: String(t.tenant ?? ''),
      subject_id: String(t.subject_id ?? ''),
      query_hash: String(t.query_hash ?? ''),
      index_shard: String(t.index_shard ?? ''),
      timestamp: Number(t.timestamp ?? 0),
      result_hash: String(t.result_hash ?? ''),
      result_count: t.result_count ? Number(t.result_count) : undefined,
      query_time_ms: t.query_time_ms ? Number(t.query_time_ms) : undefined,
    },
    signAlg: String(t.sign_alg ?? 'ed25519'),
    sig: String(t.sig),
  };
}

export function verifyTracePayload(trace: unknown): TraceVerificationResult {
  const envelope = asEnvelope(trace);
  if (envelope) {
    if (!enforceDsse()) return { valid: true, trace };
    const result = verifyEnvelope(envelope);
    return { valid: result.valid, reason: result.reason, trace };
  }

  const receipt = asReceipt(trace);
  if (receipt) {
    const result = verifyAccessReceipt(receipt.receipt, receipt.signAlg, receipt.sig);
    return { valid: result.ok, reason: result.reason, trace };
  }

  if (enforceDsse()) {
    return { valid: false, reason: 'unsupported trace format', trace };
  }

  return { valid: true, trace };
}
