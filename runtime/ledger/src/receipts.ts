import { PrismaClient } from '@prisma/client';
import { Request, Response } from 'express';
import crypto from 'crypto';

const prisma = new PrismaClient();

// Receipt interface matching the schema
interface AccessReceipt {
  receipt_id: string;
  tenant: string;
  subject_id: string;
  query_hash: string;
  index_shard: string;
  timestamp: number;
  result_hash: string;
  sign_alg: string;
  sig: string;
  result_count?: number;
  query_time_ms?: number;
  labels_accessed?: string[];
  abac_decision?: {
    allowed: boolean;
    policy_version: string;
    rules_applied: string[];
  };
  privacy_budget?: {
    epsilon_consumed: number;
    delta_consumed: number;
    budget_remaining: number;
  };
  audit_trail?: {
    request_id: string;
    client_ip?: string;
    user_agent?: string;
  };
}

// Store a receipt in the ledger
export async function storeReceipt(receipt: AccessReceipt): Promise<void> {
  try {
    await prisma.accessReceipt.create({
      data: {
        receiptId: receipt.receipt_id,
        tenant: receipt.tenant,
        subjectId: receipt.subject_id,
        queryHash: receipt.query_hash,
        indexShard: receipt.index_shard,
        timestamp: new Date(receipt.timestamp * 1000),
        resultHash: receipt.result_hash,
        signAlg: receipt.sign_alg,
        signature: receipt.sig,
        resultCount: receipt.result_count || 0,
        queryTimeMs: receipt.query_time_ms || 0,
        labelsAccessed: receipt.labels_accessed || [],
        abacDecision: receipt.abac_decision ? JSON.stringify(receipt.abac_decision) : null,
        privacyBudget: receipt.privacy_budget ? JSON.stringify(receipt.privacy_budget) : null,
        auditTrail: receipt.audit_trail ? JSON.stringify(receipt.audit_trail) : null,
      },
    });
  } catch (error) {
    console.error('Failed to store receipt:', error);
    throw new Error(`Failed to store receipt: ${error}`);
  }
}

// Retrieve a receipt by ID
export async function getReceipt(receiptId: string): Promise<AccessReceipt | null> {
  try {
    const receipt = await prisma.accessReceipt.findUnique({
      where: { receiptId },
    });

    if (!receipt) {
      return null;
    }

    return {
      receipt_id: receipt.receiptId,
      tenant: receipt.tenant,
      subject_id: receipt.subjectId,
      query_hash: receipt.queryHash,
      index_shard: receipt.indexShard,
      timestamp: Math.floor(receipt.timestamp.getTime() / 1000),
      result_hash: receipt.resultHash,
      sign_alg: receipt.signAlg,
      sig: receipt.signature,
      result_count: receipt.resultCount,
      query_time_ms: receipt.queryTimeMs,
      labels_accessed: receipt.labelsAccessed,
      abac_decision: receipt.abacDecision ? JSON.parse(receipt.abacDecision) : undefined,
      privacy_budget: receipt.privacyBudget ? JSON.parse(receipt.privacyBudget) : undefined,
      audit_trail: receipt.auditTrail ? JSON.parse(receipt.auditTrail) : undefined,
    };
  } catch (error) {
    console.error('Failed to retrieve receipt:', error);
    throw new Error(`Failed to retrieve receipt: ${error}`);
  }
}

// Get receipts by tenant
export async function getReceiptsByTenant(tenant: string, limit: number = 100): Promise<AccessReceipt[]> {
  try {
    const receipts = await prisma.accessReceipt.findMany({
      where: { tenant },
      orderBy: { timestamp: 'desc' },
      take: limit,
    });

    return receipts.map(receipt => ({
      receipt_id: receipt.receiptId,
      tenant: receipt.tenant,
      subject_id: receipt.subjectId,
      query_hash: receipt.queryHash,
      index_shard: receipt.indexShard,
      timestamp: Math.floor(receipt.timestamp.getTime() / 1000),
      result_hash: receipt.resultHash,
      sign_alg: receipt.signAlg,
      sig: receipt.signature,
      result_count: receipt.resultCount,
      query_time_ms: receipt.queryTimeMs,
      labels_accessed: receipt.labelsAccessed,
      abac_decision: receipt.abacDecision ? JSON.parse(receipt.abacDecision) : undefined,
      privacy_budget: receipt.privacyBudget ? JSON.parse(receipt.privacyBudget) : undefined,
      audit_trail: receipt.auditTrail ? JSON.parse(receipt.auditTrail) : undefined,
    }));
  } catch (error) {
    console.error('Failed to retrieve receipts by tenant:', error);
    throw new Error(`Failed to retrieve receipts by tenant: ${error}`);
  }
}

// Get receipts by subject
export async function getReceiptsBySubject(subjectId: string, limit: number = 100): Promise<AccessReceipt[]> {
  try {
    const receipts = await prisma.accessReceipt.findMany({
      where: { subjectId },
      orderBy: { timestamp: 'desc' },
      take: limit,
    });

    return receipts.map(receipt => ({
      receipt_id: receipt.receiptId,
      tenant: receipt.tenant,
      subject_id: receipt.subjectId,
      query_hash: receipt.queryHash,
      index_shard: receipt.indexShard,
      timestamp: Math.floor(receipt.timestamp.getTime() / 1000),
      result_hash: receipt.resultHash,
      sign_alg: receipt.signAlg,
      sig: receipt.signature,
      result_count: receipt.resultCount,
      query_time_ms: receipt.queryTimeMs,
      labels_accessed: receipt.labelsAccessed,
      abac_decision: receipt.abacDecision ? JSON.parse(receipt.abacDecision) : undefined,
      privacy_budget: receipt.privacyBudget ? JSON.parse(receipt.privacyBudget) : undefined,
      audit_trail: receipt.auditTrail ? JSON.parse(receipt.auditTrail) : undefined,
    }));
  } catch (error) {
    console.error('Failed to retrieve receipts by subject:', error);
    throw new Error(`Failed to retrieve receipts by subject: ${error}`);
  }
}

// Express route handlers
export async function getReceiptHandler(req: Request, res: Response): Promise<void> {
  try {
    const { id } = req.params;
    
    if (!id) {
      res.status(400).json({ error: 'Receipt ID is required' });
      return;
    }

    const receipt = await getReceipt(id);
    
    if (!receipt) {
      res.status(404).json({ error: 'Receipt not found' });
      return;
    }

    res.json(receipt);
  } catch (error) {
    console.error('Error in getReceiptHandler:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}

export async function getReceiptsByTenantHandler(req: Request, res: Response): Promise<void> {
  try {
    const { tenant } = req.params;
    const limit = parseInt(req.query.limit as string) || 100;
    
    if (!tenant) {
      res.status(400).json({ error: 'Tenant is required' });
      return;
    }

    const receipts = await getReceiptsByTenant(tenant, limit);
    res.json(receipts);
  } catch (error) {
    console.error('Error in getReceiptsByTenantHandler:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}

export async function getReceiptsBySubjectHandler(req: Request, res: Response): Promise<void> {
  try {
    const { subjectId } = req.params;
    const limit = parseInt(req.query.limit as string) || 100;
    
    if (!subjectId) {
      res.status(400).json({ error: 'Subject ID is required' });
      return;
    }

    const receipts = await getReceiptsBySubject(subjectId, limit);
    res.json(receipts);
  } catch (error) {
    console.error('Error in getReceiptsBySubjectHandler:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}

// Verify receipt signature
export function verifyReceiptSignature(receipt: AccessReceipt): boolean {
  try {
    // Create receipt data for verification
    const receiptData = {
      receipt_id: receipt.receipt_id,
      tenant: receipt.tenant,
      subject_id: receipt.subject_id,
      query_hash: receipt.query_hash,
      index_shard: receipt.index_shard,
      timestamp: receipt.timestamp,
      result_hash: receipt.result_hash,
    };

    const receiptBytes = JSON.stringify(receiptData);
    const receiptHash = crypto.createHash('sha256').update(receiptBytes).digest();
    
    // TODO: Implement actual Ed25519 signature verification
    // This would require the public key for the specific shard
    // For now, we'll do basic structural validation
    
    return receipt.sign_alg === 'ed25519' && receipt.sig.length > 0;
  } catch (error) {
    console.error('Error verifying receipt signature:', error);
    return false;
  }
} 