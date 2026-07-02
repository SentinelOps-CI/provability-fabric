// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { verifyTracePayload, type TraceVerificationResult } from './verifyTrace.js';

export type { TraceVerificationResult };

export * from './client';
export * from './middleware';
export * from './types';
export * from './utils';
export * from './errors';
export { SentinelOpsClient } from './platform-client';

// Main SDK class
export class ProvabilityFabricSDK {
  private client: any;
  private config: any;

  constructor(config: any) {
    this.config = config;
    this.client = this.initializeClient();
  }

  private initializeClient() {
    // Initialize gRPC client based on config
    return null; // TODO: Implement gRPC client
  }

  /**
   * Verify a trace with the Policy Kernel
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
