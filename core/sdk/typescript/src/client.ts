// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import {
  createIdempotentRetry,
  type IdempotentRetryFn,
  type RetryMiddlewareOptions,
} from './retry.js';
import { ConfigurationError, ProvabilityFabricError } from './errors.js';

export type ConnectionState = 'disconnected' | 'connecting' | 'connected';

export interface ClientConfig {
  /** Base URL of ledger / API HTTP surfaces (e.g. http://localhost:4000). */
  endpoint: string;
  apiKey?: string;
  /** Per-request timeout in milliseconds (default 30000). */
  timeout?: number;
  /** Retries for idempotent methods only (default 3). */
  retries?: number;
  /** Initial backoff delay in milliseconds (default 100). */
  baseDelay?: number;
  /** Cap on backoff delay in milliseconds (default 5000). */
  maxDelay?: number;
}

export interface HealthResponse {
  status: string;
  timestamp?: string;
  [key: string]: unknown;
}

export interface StatusResponse {
  service?: string;
  status: string;
  timestamp?: string;
  [key: string]: unknown;
}

/**
 * HTTP client for Provability Fabric ledger / platform API surfaces.
 *
 * gRPC is deferred: no generated protos are consumed by this SDK today.
 * Prefer the HTTP paths already exposed by the ledger (`/health`, `/api/status`,
 * tenant REST) and SentinelOps-compatible `/api/v1/*` gateways.
 */
export class ProvabilityFabricClient {
  private readonly endpoint: string;
  private readonly apiKey?: string;
  private readonly timeoutMs: number;
  private readonly withRetry: IdempotentRetryFn;
  private state: ConnectionState = 'disconnected';
  private sessionAbort: AbortController | null = null;

  constructor(config: ClientConfig) {
    if (!config.endpoint || typeof config.endpoint !== 'string') {
      throw new ConfigurationError('ClientConfig.endpoint is required');
    }
    this.endpoint = config.endpoint.replace(/\/$/, '');
    this.apiKey = config.apiKey;
    this.timeoutMs = config.timeout ?? 30_000;

    const retryOptions: RetryMiddlewareOptions = {
      maxRetries: config.retries ?? 3,
      baseDelay: config.baseDelay ?? 100,
      maxDelay: config.maxDelay ?? 5_000,
    };
    this.withRetry = createIdempotentRetry(retryOptions);
  }

  getConnectionState(): ConnectionState {
    return this.state;
  }

  isConnected(): boolean {
    return this.state === 'connected';
  }

  /**
   * Establish a session: probe `/health` and mark connected on success.
   */
  async connect(): Promise<void> {
    if (this.state === 'connected') {
      return;
    }

    this.state = 'connecting';
    this.sessionAbort = new AbortController();
    try {
      await this.getHealth();
      this.state = 'connected';
    } catch (error) {
      this.state = 'disconnected';
      this.sessionAbort = null;
      throw error;
    }
  }

  /**
   * Tear down the session: abort in-flight work and mark disconnected.
   */
  async disconnect(): Promise<void> {
    if (this.sessionAbort) {
      this.sessionAbort.abort();
      this.sessionAbort = null;
    }
    this.state = 'disconnected';
  }

  /** Ledger / simple-server health probe. */
  async getHealth(): Promise<HealthResponse> {
    return this.request<HealthResponse>('GET', '/health');
  }

  /** Ledger `/api/status` (simple-server) when present. */
  async getStatus(): Promise<StatusResponse> {
    return this.request<StatusResponse>('GET', '/api/status');
  }

  /**
   * Low-level HTTP request. Idempotent methods (GET/HEAD/OPTIONS) are retried
   * with exponential backoff; mutating methods are attempted once.
   */
  async request<T>(
    method: string,
    path: string,
    body?: unknown,
    init?: { signal?: AbortSignal }
  ): Promise<T> {
    const normalizedPath = path.startsWith('/') ? path : `/${path}`;
    return this.withRetry(method, () => this.rawRequest<T>(method, normalizedPath, body, init));
  }

  private async rawRequest<T>(
    method: string,
    path: string,
    body?: unknown,
    init?: { signal?: AbortSignal }
  ): Promise<T> {
    if (this.state !== 'connected' && path !== '/health') {
      throw new ProvabilityFabricError(
        'Client is not connected; call connect() first',
        'NOT_CONNECTED'
      );
    }

    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), this.timeoutMs);

    const onSessionAbort = () => controller.abort();
    this.sessionAbort?.signal.addEventListener('abort', onSessionAbort);
    if (init?.signal) {
      if (init.signal.aborted) {
        controller.abort();
      } else {
        init.signal.addEventListener('abort', onSessionAbort);
      }
    }

    try {
      const headers: Record<string, string> = {
        Accept: 'application/json',
      };
      if (body !== undefined) {
        headers['Content-Type'] = 'application/json';
      }
      if (this.apiKey) {
        headers.Authorization = `Bearer ${this.apiKey}`;
      }

      const response = await fetch(`${this.endpoint}${path}`, {
        method: method.toUpperCase(),
        headers,
        body: body === undefined ? undefined : JSON.stringify(body),
        signal: controller.signal,
      });

      if (!response.ok) {
        throw new ProvabilityFabricError(
          `${method.toUpperCase()} ${path} failed: ${response.status}`,
          'HTTP_ERROR',
          response.status
        );
      }

      const contentType = response.headers.get('content-type') ?? '';
      if (contentType.includes('application/json')) {
        return (await response.json()) as T;
      }
      const text = await response.text();
      return (text ? JSON.parse(text) : {}) as T;
    } catch (error) {
      if (error instanceof ProvabilityFabricError) {
        throw error;
      }
      if (error instanceof Error && error.name === 'AbortError') {
        throw new ProvabilityFabricError(
          `Request aborted or timed out: ${method.toUpperCase()} ${path}`,
          'TIMEOUT'
        );
      }
      throw new ProvabilityFabricError(
        error instanceof Error ? error.message : String(error),
        'NETWORK_ERROR'
      );
    } finally {
      clearTimeout(timer);
      this.sessionAbort?.signal.removeEventListener('abort', onSessionAbort);
      init?.signal?.removeEventListener('abort', onSessionAbort);
    }
  }
}
