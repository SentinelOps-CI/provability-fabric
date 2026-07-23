// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

// Express types - using any for now to avoid dependency issues
type Request = any;
type Response = any;
type NextFunction = any;
import { ProvabilityFabricSDK, type TraceVerificationResult } from '../index';
import { createIdempotentRetry } from '../retry.js';
export {
  createIdempotentRetry,
  retryMiddleware,
  DEFAULT_IDEMPOTENT_METHODS,
  DEFAULT_RETRY_STATUS_CODES,
  type IdempotentRetryFn,
  type RetryMiddlewareOptions,
} from '../retry.js';

export interface PFMiddlewareOptions {
  sdk: ProvabilityFabricSDK;
  addHeaders?: boolean;
  verifyTrace?: boolean;
  timeout?: number;
}

/**
 * Express middleware that adds Provability Fabric headers and verification
 */
export function pfMiddleware(options: PFMiddlewareOptions) {
  const { sdk, addHeaders = true, verifyTrace = false, timeout = 5000 } = options;

  return async (req: Request, res: Response, next: NextFunction) => {
    try {
      // Add PF-Sig headers
      if (addHeaders) {
        res.set({
          'PF-Sig-Version': '1.0',
          'PF-Sig-Timestamp': new Date().toISOString(),
          'PF-Sig-Request-ID': req.headers['x-request-id'] || generateRequestId(),
        });
      }

      // Verify trace if requested
      if (verifyTrace && req.body?.trace) {
        const traceVerification: TraceVerificationResult = await Promise.race([
          sdk.verifyTrace(req.body.trace),
          new Promise<never>((_, reject) =>
            setTimeout(() => reject(new Error('Trace verification timeout')), timeout)
          ),
        ]);

        if (!traceVerification.valid) {
          return res.status(400).json({
            error: 'Invalid trace',
            details: traceVerification.reason
          });
        }
      }

      next();
    } catch (error) {
      console.error('PF Middleware error:', error);
      res.status(500).json({
        error: 'Internal server error',
        details: 'PF middleware failed'
      });
    }
  };
}

/**
 * Circuit breaker middleware for resilience
 */
export function circuitBreakerMiddleware(options: {
  failureThreshold: number;
  resetTimeout: number;
}) {
  let failureCount = 0;
  let lastFailureTime = 0;
  let isOpen = false;

  return (req: Request, res: Response, next: NextFunction) => {
    if (isOpen) {
      const now = Date.now();
      if (now - lastFailureTime > options.resetTimeout) {
        isOpen = false;
        failureCount = 0;
      } else {
        return res.status(503).json({
          error: 'Service temporarily unavailable',
          details: 'Circuit breaker is open'
        });
      }
    }

    // Track failures
    const originalSend = res.send;
    res.send = function(data: any) {
      if (res.statusCode >= 500) {
        failureCount++;
        if (failureCount >= options.failureThreshold) {
          isOpen = true;
          lastFailureTime = Date.now();
        }
      }
      return originalSend.call(this, data);
    };

    next();
  };
}

/**
 * Attach an idempotent outbound retry helper on `req.pfRetry`.
 *
 * Does **not** retry Express `next()` / inbound handling. Callers should use
 * `req.pfRetry(method, () => sdk.getClient().request(...))` for GET/HEAD/OPTIONS.
 */
export function attachRetryMiddleware(options: {
  maxRetries: number;
  baseDelay: number;
  maxDelay: number;
}) {
  const withRetry = createIdempotentRetry(options);
  return (req: Request, _res: Response, next: NextFunction) => {
    req.pfRetry = withRetry;
    next();
  };
}

function generateRequestId(): string {
  return `req_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}
