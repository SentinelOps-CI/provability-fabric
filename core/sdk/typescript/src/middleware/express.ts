// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Request, Response, NextFunction } from 'express';
import { ProvabilityFabricSDK } from '../index';

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
        const traceVerification = await Promise.race([
          sdk.verifyTrace(req.body.trace),
          new Promise((_, reject) => 
            setTimeout(() => reject(new Error('Trace verification timeout')), timeout)
          )
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
 * Retry middleware with exponential backoff
 */
export function retryMiddleware(options: {
  maxRetries: number;
  baseDelay: number;
  maxDelay: number;
}) {
  return async (req: Request, res: Response, next: NextFunction) => {
    let attempt = 0;
    const maxAttempts = options.maxRetries + 1;

    const attemptRequest = async (): Promise<any> => {
      try {
        attempt++;
        // TODO: Implement actual retry logic
        return next();
      } catch (error) {
        if (attempt >= maxAttempts) {
          throw error;
        }

        const delay = Math.min(
          options.baseDelay * Math.pow(2, attempt - 1),
          options.maxDelay
        );

        await new Promise(resolve => setTimeout(resolve, delay));
        return attemptRequest();
      }
    };

    try {
      await attemptRequest();
    } catch (error) {
      res.status(500).json({
        error: 'Request failed after retries',
        details: error.message
      });
    }
  };
}

function generateRequestId(): string {
  return `req_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}
