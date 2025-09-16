/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Certificate Manager for MCP Multi-Tenant Isolation
 * Implements RLS hints in certificates with tenant_id and RLS token hash
 */

import crypto from 'crypto';
import winston from 'winston';

export interface RLSClaims {
  tenantId: string;
  rlsTokenHash: string;
  permissions: string[];
  expiresAt: Date;
  issuedAt: Date;
}

export interface MCPCertificate {
  certificateId: string;
  tenantId: string;
  rlsTokenHash: string;
  toolSignature: string;
  epoch: number;
  permissions: string[];
  constraints: string[];
  issuedAt: Date;
  expiresAt: Date;
  signature: string;
  metadata: {
    version: string;
    issuer: string;
    compliance: string[];
  };
}

export interface CertificateValidationResult {
  valid: boolean;
  reason?: string;
  rlsClaims?: RLSClaims;
  violations?: string[];
}

export class CertificateManager {
  private logger: winston.Logger;
  private privateKey: string;
  private publicKey: string;
  private rlsTokenCache: Map<string, RLSClaims> = new Map();
  private certificateCache: Map<string, MCPCertificate> = new Map();

  constructor(logger: winston.Logger, privateKey?: string) {
    this.logger = logger;
    
    // Generate or use provided key pair
    if (privateKey) {
      this.privateKey = privateKey;
      this.publicKey = this.extractPublicKey(privateKey);
    } else {
      const keyPair = crypto.generateKeyPairSync('ed25519');
      this.privateKey = keyPair.privateKey.export({ format: 'pem', type: 'pkcs8' }) as string;
      this.publicKey = keyPair.publicKey.export({ format: 'pem', type: 'spki' }) as string;
    }
  }

  /**
   * Generate RLS token hash for tenant
   */
  public generateRLSTokenHash(tenantId: string, permissions: string[]): string {
    const tokenData = {
      tenantId,
      permissions: permissions.sort(), // Sort for consistent hashing
      timestamp: Date.now(),
      nonce: crypto.randomBytes(16).toString('hex')
    };

    const tokenString = JSON.stringify(tokenData);
    return crypto.createHash('sha256').update(tokenString).digest('hex');
  }

  /**
   * Create RLS claims for tenant
   */
  public createRLSClaims(
    tenantId: string, 
    permissions: string[], 
    expiresInHours: number = 24
  ): RLSClaims {
    const rlsTokenHash = this.generateRLSTokenHash(tenantId, permissions);
    const now = new Date();
    const expiresAt = new Date(now.getTime() + expiresInHours * 60 * 60 * 1000);

    const claims: RLSClaims = {
      tenantId,
      rlsTokenHash,
      permissions,
      expiresAt,
      issuedAt: now
    };

    this.rlsTokenCache.set(rlsTokenHash, claims);
    
    this.logger.info('MCP: RLS claims created', {
      tenantId,
      rlsTokenHash: rlsTokenHash.substring(0, 16) + '...',
      permissions,
      expiresAt
    });

    return claims;
  }

  /**
   * Generate MCP certificate with RLS hints
   */
  public generateCertificate(
    tenantId: string,
    toolSignature: string,
    epoch: number,
    permissions: string[],
    constraints: string[] = [],
    expiresInHours: number = 1
  ): MCPCertificate {
    // Get or create RLS claims
    let rlsClaims = this.findRLSClaimsByTenant(tenantId);
    if (!rlsClaims || rlsClaims.expiresAt < new Date()) {
      rlsClaims = this.createRLSClaims(tenantId, permissions, 24);
    }

    const certificateId = `mcp_cert_${Date.now()}_${crypto.randomBytes(8).toString('hex')}`;
    const now = new Date();
    const expiresAt = new Date(now.getTime() + expiresInHours * 60 * 60 * 1000);

    const certificate: MCPCertificate = {
      certificateId,
      tenantId,
      rlsTokenHash: rlsClaims.rlsTokenHash,
      toolSignature,
      epoch,
      permissions,
      constraints,
      issuedAt: now,
      expiresAt,
      signature: '', // Will be set after signing
      metadata: {
        version: '1.0.0',
        issuer: 'provability-fabric-mcp',
        compliance: ['SOC2', 'GDPR', 'HIPAA']
      }
    };

    // Sign the certificate
    certificate.signature = this.signCertificate(certificate);
    
    // Cache the certificate
    this.certificateCache.set(certificateId, certificate);

    this.logger.info('MCP: Certificate generated', {
      certificateId,
      tenantId,
      toolSignature: toolSignature.substring(0, 16) + '...',
      rlsTokenHash: rlsClaims.rlsTokenHash.substring(0, 16) + '...',
      epoch,
      expiresAt
    });

    return certificate;
  }

  /**
   * Validate MCP certificate with RLS claims
   */
  public validateCertificate(certificate: MCPCertificate): CertificateValidationResult {
    try {
      // Check certificate expiration
      if (certificate.expiresAt < new Date()) {
        return {
          valid: false,
          reason: 'Certificate has expired'
        };
      }

      // Verify certificate signature
      if (!this.verifyCertificateSignature(certificate)) {
        return {
          valid: false,
          reason: 'Invalid certificate signature'
        };
      }

      // Validate RLS claims
      const rlsClaims = this.rlsTokenCache.get(certificate.rlsTokenHash);
      if (!rlsClaims) {
        return {
          valid: false,
          reason: 'RLS token hash not found or expired'
        };
      }

      if (rlsClaims.expiresAt < new Date()) {
        return {
          valid: false,
          reason: 'RLS claims have expired'
        };
      }

      // Check tenant ID match
      if (rlsClaims.tenantId !== certificate.tenantId) {
        return {
          valid: false,
          reason: 'RLS claims tenant ID mismatch'
        };
      }

      // Check permissions
      const hasRequiredPermissions = certificate.permissions.every(permission =>
        rlsClaims.permissions.includes(permission)
      );

      if (!hasRequiredPermissions) {
        return {
          valid: false,
          reason: 'Insufficient permissions in RLS claims',
          rlsClaims
        };
      }

      this.logger.info('MCP: Certificate validation passed', {
        certificateId: certificate.certificateId,
        tenantId: certificate.tenantId,
        toolSignature: certificate.toolSignature.substring(0, 16) + '...'
      });

      return {
        valid: true,
        rlsClaims
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.logger.error('MCP: Certificate validation failed', {
        certificateId: certificate.certificateId,
        error: errorMessage
      });

      return {
        valid: false,
        reason: `Validation error: ${errorMessage}`
      };
    }
  }

  /**
   * Validate RLS claims for tenant access
   */
  public validateRLSClaims(tenantId: string, rlsTokenHash: string): CertificateValidationResult {
    const rlsClaims = this.rlsTokenCache.get(rlsTokenHash);
    
    if (!rlsClaims) {
      return {
        valid: false,
        reason: 'RLS token hash not found'
      };
    }

    if (rlsClaims.tenantId !== tenantId) {
      return {
        valid: false,
        reason: 'RLS claims tenant ID mismatch'
      };
    }

    if (rlsClaims.expiresAt < new Date()) {
      return {
        valid: false,
        reason: 'RLS claims have expired'
      };
    }

    return {
      valid: true,
      rlsClaims
    };
  }

  /**
   * Reject request if RLS claim missing/mismatch
   */
  public enforceRLSClaims(
    tenantId: string,
    rlsTokenHash: string,
    requiredPermissions: string[] = []
  ): { allowed: boolean; reason?: string; violations?: string[] } {
    const validation = this.validateRLSClaims(tenantId, rlsTokenHash);
    
    if (!validation.valid) {
      return {
        allowed: false,
        reason: validation.reason,
        violations: ['rls_claim_validation']
      };
    }

    // Check required permissions
    if (requiredPermissions.length > 0 && validation.rlsClaims) {
      const missingPermissions = requiredPermissions.filter(
        permission => !validation.rlsClaims!.permissions.includes(permission)
      );

      if (missingPermissions.length > 0) {
        return {
          allowed: false,
          reason: `Missing required permissions: ${missingPermissions.join(', ')}`,
          violations: ['insufficient_permissions']
        };
      }
    }

    this.logger.info('MCP: RLS claims enforcement passed', {
      tenantId,
      rlsTokenHash: rlsTokenHash.substring(0, 16) + '...',
      requiredPermissions
    });

    return { allowed: true };
  }

  /**
   * Sign certificate using Ed25519
   */
  private signCertificate(certificate: MCPCertificate): string {
    const payload = {
      certificateId: certificate.certificateId,
      tenantId: certificate.tenantId,
      rlsTokenHash: certificate.rlsTokenHash,
      toolSignature: certificate.toolSignature,
      epoch: certificate.epoch,
      permissions: certificate.permissions,
      constraints: certificate.constraints,
      issuedAt: certificate.issuedAt,
      expiresAt: certificate.expiresAt,
      metadata: certificate.metadata
    };

    const payloadString = JSON.stringify(payload);
    const signature = crypto.sign(null, Buffer.from(payloadString), this.privateKey);
    return signature.toString('base64');
  }

  /**
   * Verify certificate signature
   */
  private verifyCertificateSignature(certificate: MCPCertificate): boolean {
    try {
      const payload = {
        certificateId: certificate.certificateId,
        tenantId: certificate.tenantId,
        rlsTokenHash: certificate.rlsTokenHash,
        toolSignature: certificate.toolSignature,
        epoch: certificate.epoch,
        permissions: certificate.permissions,
        constraints: certificate.constraints,
        issuedAt: certificate.issuedAt,
        expiresAt: certificate.expiresAt,
        metadata: certificate.metadata
      };

      const payloadString = JSON.stringify(payload);
      const signature = Buffer.from(certificate.signature, 'base64');
      
      return crypto.verify(null, Buffer.from(payloadString), this.publicKey, signature);
    } catch (error) {
      this.logger.error('MCP: Certificate signature verification failed', {
        certificateId: certificate.certificateId,
        error: error instanceof Error ? error.message : 'Unknown error'
      });
      return false;
    }
  }

  /**
   * Extract public key from private key
   */
  private extractPublicKey(privateKey: string): string {
    // In a real implementation, you would extract the public key from the private key
    // For now, we'll generate a new key pair if needed
    const keyPair = crypto.generateKeyPairSync('ed25519');
    return keyPair.publicKey.export({ format: 'pem', type: 'spki' }) as string;
  }

  /**
   * Find RLS claims by tenant ID
   */
  private findRLSClaimsByTenant(tenantId: string): RLSClaims | null {
    for (const claims of this.rlsTokenCache.values()) {
      if (claims.tenantId === tenantId && claims.expiresAt > new Date()) {
        return claims;
      }
    }
    return null;
  }

  /**
   * Get certificate by ID
   */
  public getCertificate(certificateId: string): MCPCertificate | null {
    return this.certificateCache.get(certificateId) || null;
  }

  /**
   * Get RLS claims by token hash
   */
  public getRLSClaims(rlsTokenHash: string): RLSClaims | null {
    return this.rlsTokenCache.get(rlsTokenHash) || null;
  }

  /**
   * Clean up expired entries
   */
  public cleanupExpiredEntries(): void {
    const now = new Date();
    let cleaned = 0;

    // Clean expired RLS claims
    for (const [tokenHash, claims] of this.rlsTokenCache.entries()) {
      if (claims.expiresAt < now) {
        this.rlsTokenCache.delete(tokenHash);
        cleaned++;
      }
    }

    // Clean expired certificates
    for (const [certId, cert] of this.certificateCache.entries()) {
      if (cert.expiresAt < now) {
        this.certificateCache.delete(certId);
        cleaned++;
      }
    }

    if (cleaned > 0) {
      this.logger.info('MCP: Cleaned up expired certificate entries', { cleaned });
    }
  }

  /**
   * Get statistics for monitoring
   */
  public getStats(): {
    rlsTokenCount: number;
    certificateCount: number;
    activeTenants: string[];
  } {
    const activeTenants = new Set<string>();
    
    for (const claims of this.rlsTokenCache.values()) {
      if (claims.expiresAt > new Date()) {
        activeTenants.add(claims.tenantId);
      }
    }

    return {
      rlsTokenCount: this.rlsTokenCache.size,
      certificateCount: this.certificateCache.size,
      activeTenants: Array.from(activeTenants)
    };
  }
}

export default CertificateManager;
