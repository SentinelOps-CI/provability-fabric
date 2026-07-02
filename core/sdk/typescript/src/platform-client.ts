// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

export interface PlatformClientConfig {
  baseUrl: string;
  apiKey?: string;
  timeoutMs?: number;
}

/**
 * HTTP client for SentinelOps / Provability Fabric platform APIs.
 * Used by demos and integrations that call spec, proof, build, runtime, and evidence services.
 */
export class SentinelOpsClient {
  private baseUrl: string;
  private apiKey?: string;
  private timeoutMs: number;

  constructor(baseUrl: string, apiKey?: string, timeoutMs = 60000) {
    this.baseUrl = baseUrl.replace(/\/$/, '');
    this.apiKey = apiKey;
    this.timeoutMs = timeoutMs;
  }

  private async request<T>(method: string, path: string, body?: unknown): Promise<T> {
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), this.timeoutMs);
    try {
      const headers: Record<string, string> = { 'Content-Type': 'application/json' };
      if (this.apiKey) headers.Authorization = `Bearer ${this.apiKey}`;
      const response = await fetch(`${this.baseUrl}${path}`, {
        method,
        headers,
        body: body === undefined ? undefined : JSON.stringify(body),
        signal: controller.signal,
      });
      if (!response.ok) {
        throw new Error(`${method} ${path} failed: ${response.status}`);
      }
      if (response.headers.get('content-type')?.includes('application/json')) {
        return (await response.json()) as T;
      }
      return (await response.arrayBuffer()) as unknown as T;
    } finally {
      clearTimeout(timer);
    }
  }

  async compilePolicy(request: { english: string; policy_id: string; version?: string }) {
    const data = await this.request<Record<string, unknown>>('POST', '/api/v1/policy/compile', {
      version: '1.0.0',
      ...request,
    });
    return {
      ...data,
      actionDsl: (data as { action_dsl?: unknown }).action_dsl ?? (data as { actionDsl?: unknown }).actionDsl,
    };
  }

  async runProofs(request: { policy_hash: string; action_dsl: unknown }) {
    return this.request('POST', '/api/v1/proofs/run', request);
  }

  async buildPolicy(request: {
    policy_hash: string;
    action_dsl: unknown;
    proof_hash: string;
  }) {
    return this.request('POST', '/api/v1/policy/build', request);
  }

  async getHealth(): Promise<{ status: string; services: Record<string, unknown> }> {
    return this.request('GET', '/api/v1/health');
  }

  async getSLO(): Promise<{
    latency: { p95: number };
    tps: number;
    error_rate: number;
  }> {
    return this.request('GET', '/api/v1/runtime/slo');
  }

  async rotateEpoch(oldEpoch: number, newEpoch: number, reason?: string) {
    return this.request('POST', '/api/v1/runtime/epoch/rotate', {
      old_epoch: oldEpoch,
      new_epoch: newEpoch,
      reason,
    });
  }

  async downloadPacket(sessionId: string): Promise<{ size: number; data?: unknown }> {
    const data = await this.request<{ packet_id?: string; id?: string }>(
      'POST',
      '/api/v1/compliance/packet',
      { session_id: sessionId }
    );
    const packetId = data.packet_id ?? data.id ?? sessionId;
    const blob = await this.request<ArrayBuffer>('GET', `/api/v1/compliance/packet/${packetId}`);
    return { size: blob.byteLength ?? 0, data: blob };
  }
}
