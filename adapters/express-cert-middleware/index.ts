import type { Request, Response, NextFunction } from 'express';
import crypto from 'crypto';

export type CertSigner = (payload: any) => Promise<string>;

export interface CertMiddlewareOptions {
  tenantId?: string;
  signer?: CertSigner; // returns base64 signature string
}

export function createCertMiddleware(options: CertMiddlewareOptions = {}) {
  const tenantId = options.tenantId || 'demo-tenant';
  const signer = options.signer;

  return async function certMiddleware(req: Request, res: Response, next: NextFunction) {
    const start = process.hrtime.bigint();

    res.on('finish', async () => {
      try {
        const end = process.hrtime.bigint();
        const latencyMs = Number(end - start) / 1_000_000;

        // Minimal CERT-V1 payload (simplified)
        const cert: any = {
          bundle_id: 'standards-lane',
          policy_hash: 'placeholder-policy-hash',
          proof_hash: 'placeholder-proof-hash',
          automata_hash: 'placeholder-automata-hash',
          labeler_hash: 'placeholder-labeler-hash',
          ni_claim: 'global_non_interference',
          ni_monitor: res.statusCode < 400 ? 'accept' : 'reject',
          sidecar_build: 'express-mw@1.0.0',
          tenant_id: tenantId,
          session_id: req.headers['x-session-id'] || crypto.randomUUID(),
          timestamp: new Date().toISOString(),
          method: req.method,
          path: req.originalUrl,
          latency_ms: Math.round(latencyMs),
          egress_profile: 'HTTP-EGRESS@1.0',
        };

        // Optional signing
        if (signer) {
          const sig = await signer(cert);
          cert.sig = sig;
        }

        // Emit to stdout for demo; in production, POST to evidence-service
        // fetch(`${process.env.API_BASE_URL}/api/v1/evidence/store`, { method: 'POST', body: JSON.stringify(cert) })
        console.log(JSON.stringify(cert));
      } catch (e) {
        // Swallow errors to not affect main response
      }
    });

    next();
  };
}
