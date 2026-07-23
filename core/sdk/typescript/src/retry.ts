// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

/** Default HTTP methods safe to retry (RFC 9110 idempotent). */
export const DEFAULT_IDEMPOTENT_METHODS = ['GET', 'HEAD', 'OPTIONS'] as const;

/** Status codes that warrant a retry for idempotent outbound calls. */
export const DEFAULT_RETRY_STATUS_CODES = [408, 429, 500, 502, 503, 504] as const;

export interface RetryMiddlewareOptions {
  maxRetries: number;
  baseDelay: number;
  maxDelay: number;
  /** Methods eligible for retry (default GET/HEAD/OPTIONS). */
  idempotentMethods?: readonly string[];
  /** HTTP status codes that trigger retry (when error carries statusCode). */
  retryStatusCodes?: readonly number[];
}

export type IdempotentRetryFn = <T>(
  method: string,
  operation: () => Promise<T>
) => Promise<T>;

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function isRetriableError(
  error: unknown,
  retryStatusCodes: ReadonlySet<number>
): boolean {
  if (!error || typeof error !== 'object') {
    return true; // network / unknown — retry for idempotent calls
  }
  const err = error as { statusCode?: number; code?: string; name?: string };
  if (typeof err.statusCode === 'number') {
    return retryStatusCodes.has(err.statusCode);
  }
  // Timeouts and transport failures are retriable; auth/config are not.
  if (err.code === 'TIMEOUT' || err.code === 'NETWORK_ERROR') {
    return true;
  }
  if (err.code === 'NOT_CONNECTED' || err.code === 'CONFIGURATION_ERROR') {
    return false;
  }
  if (err.name === 'AbortError') {
    return false;
  }
  return true;
}

/**
 * Creates a retry wrapper for **idempotent outbound SDK calls** only.
 *
 * Non-idempotent methods (POST/PATCH/DELETE, etc.) run exactly once.
 * This is not Express `next()` retry middleware.
 */
export function createIdempotentRetry(
  options: RetryMiddlewareOptions
): IdempotentRetryFn {
  const maxRetries = Math.max(0, options.maxRetries);
  const baseDelay = Math.max(0, options.baseDelay);
  const maxDelay = Math.max(baseDelay, options.maxDelay);
  const methods = new Set(
    (options.idempotentMethods ?? DEFAULT_IDEMPOTENT_METHODS).map((m) =>
      m.toUpperCase()
    )
  );
  const retryStatusCodes = new Set(
    options.retryStatusCodes ?? DEFAULT_RETRY_STATUS_CODES
  );

  return async function withIdempotentRetry<T>(
    method: string,
    operation: () => Promise<T>
  ): Promise<T> {
    const upper = method.toUpperCase();
    if (!methods.has(upper)) {
      return operation();
    }

    const maxAttempts = maxRetries + 1;
    let attempt = 0;
    let lastError: unknown;

    while (attempt < maxAttempts) {
      attempt += 1;
      try {
        return await operation();
      } catch (error) {
        lastError = error;
        const canRetry =
          attempt < maxAttempts && isRetriableError(error, retryStatusCodes);
        if (!canRetry) {
          throw error;
        }
        const delay = Math.min(baseDelay * Math.pow(2, attempt - 1), maxDelay);
        await sleep(delay);
      }
    }

    throw lastError;
  };
}

/**
 * Factory for idempotent outbound SDK call retry (Wave 10.3).
 *
 * Historical name retained for SDK consumers; this is **not** blind Express
 * `next()` retry. Use the returned function around GET/HEAD/OPTIONS (or other
 * configured idempotent) outbound calls.
 *
 * @example
 * ```ts
 * const retry = retryMiddleware({ maxRetries: 3, baseDelay: 100, maxDelay: 5000 });
 * const health = await retry('GET', () => client.getHealth());
 * ```
 */
export function retryMiddleware(options: RetryMiddlewareOptions): IdempotentRetryFn {
  return createIdempotentRetry(options);
}
