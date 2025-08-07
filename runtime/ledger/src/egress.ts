import { PrismaClient } from '@prisma/client';
import { Request, Response } from 'express';
import crypto from 'crypto';

const prisma = new PrismaClient();

// Egress certificate interface
interface EgressCertificate {
  cert_id: string;
  plan_id?: string;
  tenant: string;
  detector_flags: {
    pii_detected: boolean;
    secrets_detected: boolean;
    near_dupe_detected: boolean;
    policy_violations: boolean;
  };
  near_dupe_score: number;
  policy_hash: string;
  text_hash: string;
  timestamp: number;
  signer?: string;
  // Non-interference verdict fields
  non_interference: 'passed' | 'failed';
  influencing_labels: string[];
  attestation_ref?: string;
}

// Store an egress certificate in the ledger
export async function storeEgressCertificate(certificate: EgressCertificate): Promise<void> {
  try {
    await prisma.egressCertificate.create({
      data: {
        certId: certificate.cert_id,
        planId: certificate.plan_id,
        tenant: certificate.tenant,
        piiDetected: certificate.detector_flags.pii_detected,
        secretsDetected: certificate.detector_flags.secrets_detected,
        nearDupeDetected: certificate.detector_flags.near_dupe_detected,
        policyViolations: certificate.detector_flags.policy_violations,
        nearDupeScore: certificate.near_dupe_score,
        policyHash: certificate.policy_hash,
        textHash: certificate.text_hash,
        timestamp: new Date(certificate.timestamp * 1000),
        signer: certificate.signer,
        // Non-interference fields
        nonInterference: certificate.non_interference,
        influencingLabels: certificate.influencing_labels,
        attestationRef: certificate.attestation_ref,
      },
    });
  } catch (error) {
    console.error('Failed to store egress certificate:', error);
    throw new Error(`Failed to store egress certificate: ${error}`);
  }
}

// Retrieve an egress certificate by ID
export async function getEgressCertificate(certId: string): Promise<EgressCertificate | null> {
  try {
    const certificate = await prisma.egressCertificate.findUnique({
      where: { certId },
    });

    if (!certificate) {
      return null;
    }

    return {
      cert_id: certificate.certId,
      plan_id: certificate.planId,
      tenant: certificate.tenant,
      detector_flags: {
        pii_detected: certificate.piiDetected,
        secrets_detected: certificate.secretsDetected,
        near_dupe_detected: certificate.nearDupeDetected,
        policy_violations: certificate.policyViolations,
      },
      near_dupe_score: certificate.nearDupeScore,
      policy_hash: certificate.policyHash,
      text_hash: certificate.textHash,
      timestamp: Math.floor(certificate.timestamp.getTime() / 1000),
      signer: certificate.signer,
      // Non-interference fields
      non_interference: certificate.nonInterference as 'passed' | 'failed',
      influencing_labels: certificate.influencingLabels || [],
      attestation_ref: certificate.attestationRef,
    };
  } catch (error) {
    console.error('Failed to retrieve egress certificate:', error);
    throw new Error(`Failed to retrieve egress certificate: ${error}`);
  }
}

// Get egress certificates by tenant
export async function getEgressCertificatesByTenant(tenant: string, limit: number = 100): Promise<EgressCertificate[]> {
  try {
    const certificates = await prisma.egressCertificate.findMany({
      where: { tenant },
      orderBy: { timestamp: 'desc' },
      take: limit,
    });

    return certificates.map(cert => ({
      cert_id: cert.certId,
      plan_id: cert.planId,
      tenant: cert.tenant,
      detector_flags: {
        pii_detected: cert.piiDetected,
        secrets_detected: cert.secretsDetected,
        near_dupe_detected: cert.nearDupeDetected,
        policy_violations: cert.policyViolations,
      },
      near_dupe_score: cert.nearDupeScore,
      policy_hash: cert.policyHash,
      text_hash: cert.textHash,
      timestamp: Math.floor(cert.timestamp.getTime() / 1000),
      signer: cert.signer,
      // Non-interference fields
      non_interference: cert.nonInterference as 'passed' | 'failed',
      influencing_labels: cert.influencingLabels || [],
      attestation_ref: cert.attestationRef,
    }));
  } catch (error) {
    console.error('Failed to retrieve egress certificates by tenant:', error);
    throw new Error(`Failed to retrieve egress certificates by tenant: ${error}`);
  }
}

// Get egress certificates by plan ID
export async function getEgressCertificatesByPlan(planId: string): Promise<EgressCertificate[]> {
  try {
    const certificates = await prisma.egressCertificate.findMany({
      where: { planId },
      orderBy: { timestamp: 'desc' },
    });

    return certificates.map(cert => ({
      cert_id: cert.certId,
      plan_id: cert.planId,
      tenant: cert.tenant,
      detector_flags: {
        pii_detected: cert.piiDetected,
        secrets_detected: cert.secretsDetected,
        near_dupe_detected: cert.nearDupeDetected,
        policy_violations: cert.policyViolations,
      },
      near_dupe_score: cert.nearDupeScore,
      policy_hash: cert.policyHash,
      text_hash: cert.textHash,
      timestamp: Math.floor(cert.timestamp.getTime() / 1000),
      signer: cert.signer,
      // Non-interference fields
      non_interference: cert.nonInterference as 'passed' | 'failed',
      influencing_labels: cert.influencingLabels || [],
      attestation_ref: cert.attestationRef,
    }));
  } catch (error) {
    console.error('Failed to retrieve egress certificates by plan:', error);
    throw new Error(`Failed to retrieve egress certificates by plan: ${error}`);
  }
}

// Get certificates with violations
export async function getCertificatesWithViolations(limit: number = 100): Promise<EgressCertificate[]> {
  try {
    const certificates = await prisma.egressCertificate.findMany({
      where: {
        OR: [
          { piiDetected: true },
          { secretsDetected: true },
          { policyViolations: true },
          { nonInterference: 'failed' },
        ],
      },
      orderBy: { timestamp: 'desc' },
      take: limit,
    });

    return certificates.map(cert => ({
      cert_id: cert.certId,
      plan_id: cert.planId,
      tenant: cert.tenant,
      detector_flags: {
        pii_detected: cert.piiDetected,
        secrets_detected: cert.secretsDetected,
        near_dupe_detected: cert.nearDupeDetected,
        policy_violations: cert.policyViolations,
      },
      near_dupe_score: cert.nearDupeScore,
      policy_hash: cert.policyHash,
      text_hash: cert.textHash,
      timestamp: Math.floor(cert.timestamp.getTime() / 1000),
      signer: cert.signer,
      // Non-interference fields
      non_interference: cert.nonInterference as 'passed' | 'failed',
      influencing_labels: cert.influencingLabels || [],
      attestation_ref: cert.attestationRef,
    }));
  } catch (error) {
    console.error('Failed to retrieve certificates with violations:', error);
    throw new Error(`Failed to retrieve certificates with violations: ${error}`);
  }
}

// Get certificates with non-interference failures
export async function getCertificatesWithNIFailures(limit: number = 100): Promise<EgressCertificate[]> {
  try {
    const certificates = await prisma.egressCertificate.findMany({
      where: {
        nonInterference: 'failed',
      },
      orderBy: { timestamp: 'desc' },
      take: limit,
    });

    return certificates.map(cert => ({
      cert_id: cert.certId,
      plan_id: cert.planId,
      tenant: cert.tenant,
      detector_flags: {
        pii_detected: cert.piiDetected,
        secrets_detected: cert.secretsDetected,
        near_dupe_detected: cert.nearDupeDetected,
        policy_violations: cert.policyViolations,
      },
      near_dupe_score: cert.nearDupeScore,
      policy_hash: cert.policyHash,
      text_hash: cert.textHash,
      timestamp: Math.floor(cert.timestamp.getTime() / 1000),
      signer: cert.signer,
      // Non-interference fields
      non_interference: cert.nonInterference as 'passed' | 'failed',
      influencing_labels: cert.influencingLabels || [],
      attestation_ref: cert.attestationRef,
    }));
  } catch (error) {
    console.error('Failed to retrieve certificates with NI failures:', error);
    throw new Error(`Failed to retrieve certificates with NI failures: ${error}`);
  }
}

// Express route handlers
export async function getEgressCertificateHandler(req: Request, res: Response): Promise<void> {
  try {
    const { id } = req.params;
    
    if (!id) {
      res.status(400).json({ error: 'Certificate ID is required' });
      return;
    }

    const certificate = await getEgressCertificate(id);
    
    if (!certificate) {
      res.status(404).json({ error: 'Certificate not found' });
      return;
    }

    res.json(certificate);
  } catch (error) {
    console.error('Error in getEgressCertificateHandler:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}

export async function getEgressCertificatesByTenantHandler(req: Request, res: Response): Promise<void> {
  try {
    const { tenant } = req.params;
    const limit = parseInt(req.query.limit as string) || 100;
    
    if (!tenant) {
      res.status(400).json({ error: 'Tenant is required' });
      return;
    }

    const certificates = await getEgressCertificatesByTenant(tenant, limit);
    res.json(certificates);
  } catch (error) {
    console.error('Error in getEgressCertificatesByTenantHandler:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}

export async function getEgressCertificatesByPlanHandler(req: Request, res: Response): Promise<void> {
  try {
    const { planId } = req.params;
    
    if (!planId) {
      res.status(400).json({ error: 'Plan ID is required' });
      return;
    }

    const certificates = await getEgressCertificatesByPlan(planId);
    res.json(certificates);
  } catch (error) {
    console.error('Error in getEgressCertificatesByPlanHandler:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}

export async function getCertificatesWithViolationsHandler(req: Request, res: Response): Promise<void> {
  try {
    const limit = parseInt(req.query.limit as string) || 100;
    const certificates = await getCertificatesWithViolations(limit);
    res.json(certificates);
  } catch (error) {
    console.error('Error in getCertificatesWithViolationsHandler:', error);
    res.status(500).json({ error: 'Internal server error' });
  }
}

// Verify certificate signature
export function verifyCertificateSignature(certificate: EgressCertificate): boolean {
  try {
    // Create certificate data for verification
    const certData = {
      cert_id: certificate.cert_id,
      plan_id: certificate.plan_id,
      tenant: certificate.tenant,
      detector_flags: certificate.detector_flags,
      near_dupe_score: certificate.near_dupe_score,
      policy_hash: certificate.policy_hash,
      text_hash: certificate.text_hash,
      timestamp: certificate.timestamp,
    };

    const certBytes = JSON.stringify(certData);
    const certHash = crypto.createHash('sha256').update(certBytes).digest();
    
    // TODO: Implement actual signature verification
    // This would require the public key for the signer
    // For now, we'll do basic structural validation
    
    return certificate.text_hash.length === 64 && certificate.policy_hash.length === 64;
  } catch (error) {
    console.error('Error verifying certificate signature:', error);
    return false;
  }
}

// Generate certificate statistics
export async function getCertificateStats(): Promise<{
  total: number;
  with_violations: number;
  pii_violations: number;
  secrets_violations: number;
  policy_violations: number;
  avg_near_dupe_score: number;
}> {
  try {
    const total = await prisma.egressCertificate.count();
    const withViolations = await prisma.egressCertificate.count({
      where: {
        OR: [
          { piiDetected: true },
          { secretsDetected: true },
          { policyViolations: true },
        ],
      },
    });
    const piiViolations = await prisma.egressCertificate.count({
      where: { piiDetected: true },
    });
    const secretsViolations = await prisma.egressCertificate.count({
      where: { secretsDetected: true },
    });
    const policyViolations = await prisma.egressCertificate.count({
      where: { policyViolations: true },
    });

    const avgScore = await prisma.egressCertificate.aggregate({
      _avg: { nearDupeScore: true },
    });

    return {
      total,
      with_violations: withViolations,
      pii_violations: piiViolations,
      secrets_violations: secretsViolations,
      policy_violations: policyViolations,
      avg_near_dupe_score: avgScore._avg.nearDupeScore || 0,
    };
  } catch (error) {
    console.error('Failed to get certificate statistics:', error);
    throw new Error(`Failed to get certificate statistics: ${error}`);
  }
} 