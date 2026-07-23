// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { verifyTracePayload, type TraceVerificationResult } from './verifyTrace.js';
import { ProvabilityFabricClient, type ClientConfig } from './client.js';
import { ConfigurationError } from './errors.js';

export type { TraceVerificationResult };

export * from './client';
export * from './middleware';
export * from './retry';
export * from './types';
export * from './utils';
export * from './errors';
export { SentinelOpsClient } from './platform-client';

/** SDK construction options (HTTP ledger / API surfaces). */
export interface ProvabilityFabricSDKConfig extends ClientConfig {
  /** Reserved for future gRPC transport; ignored today (HTTP only). */
  transport?: 'http' | 'grpc';
}

/**
 * Main SDK class.
 *
 * Transport is HTTP against existing ledger/API surfaces. gRPC is deferred
 * until generated protos are consumed by this package.
 */
export class ProvabilityFabricSDK {
  private readonly client: ProvabilityFabricClient;
  private readonly config: ProvabilityFabricSDKConfig;

  constructor(config: ProvabilityFabricSDKConfig) {
    if (!config?.endpoint) {
      throw new ConfigurationError('ProvabilityFabricSDK requires config.endpoint');
    }
    if (config.transport === 'grpc') {
      throw new ConfigurationError(
        'gRPC transport is deferred; use HTTP (default) against ledger/API surfaces'
      );
    }
    this.config = config;
    this.client = this.initializeClient();
  }

  /**
   * Build the HTTP client. gRPC is intentionally not initialized here.
   */
  private initializeClient(): ProvabilityFabricClient {
    return new ProvabilityFabricClient({
      endpoint: this.config.endpoint,
      apiKey: this.config.apiKey,
      timeout: this.config.timeout,
      retries: this.config.retries,
      baseDelay: this.config.baseDelay,
      maxDelay: this.config.maxDelay,
    });
  }

  getClient(): ProvabilityFabricClient {
    return this.client;
  }

  async connect(): Promise<void> {
    await this.client.connect();
  }

  async disconnect(): Promise<void> {
    await this.client.disconnect();
  }

  /**
   * Verify a trace with the Policy Kernel / local DSSE verifier.
   * Local verification; does not require connect().
   */
  async verifyTrace(trace: unknown): Promise<TraceVerificationResult> {
    try {
      return verifyTracePayload(trace);
    } catch (error) {
      throw new Error(`Trace verification failed: ${error}`);
    }
  }

  /**
   * Get SDK version
   */
  getVersion(): string {
    return '1.0.0';
  }
}

// Default export
export default ProvabilityFabricSDK;
