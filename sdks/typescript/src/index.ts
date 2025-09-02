// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

import axios, { AxiosInstance, AxiosResponse } from 'axios';

export interface PolicyCompileRequest {
  english: string;
  policy_id?: string;
  version?: string;
  metadata?: Record<string, string>;
}

export interface PolicyCompileResponse {
  actionDsl: any;
  diagnostics: Diagnostic[];
  policy_hash: string;
  timestamp: string;
}

export interface PolicyBuildRequest {
  policy_hash: string;
  action_dsl: Record<string, any>;
  proof_hash: string;
  metadata?: Record<string, string>;
  signing_key?: string;
}

export interface PolicyBuildResponse {
  build_id: string;
  dfa_hash: string;
  automata_hash: string;
  labeler_hash: string;
  proof_inputs: Record<string, any>;
  artifacts: string[];
  signature?: string;
  status: string;
  timestamp: string;
  execution_time_ms: number;
}

export interface ProofRunRequest {
  policy_hash: string;
  action_dsl: any;
  proof_inputs?: Record<string, any>;
  use_morph?: boolean;
  morph_shards?: number;
  metadata?: Record<string, string>;
}

export interface ProofRunResponse {
  proof_hash: string;
  status: string;
  shards?: ProofShard[];
  artifacts: string[];
  diagnostics: Diagnostic[];
  timestamp: string;
  execution_time_ms: number;
}

export interface ProofShard {
  shard_id: string;
  status: string;
  morphvm_id?: string;
  env_snapshot?: string;
  proof_hash?: string;
  execution_time_ms: number;
}

export interface Diagnostic {
  level: string;
  message: string;
  file?: string;
  line?: number;
  column?: number;
}

export interface DeployRequest {
  policy_hash: string;
  automata_hash: string;
  epoch: number;
}

export interface CertV1 {
  bundle_id: string;
  policy_hash: string;
  proof_hash: string;
  automata_hash: string;
  labeler_hash: string;
  ni_claim: string;
  ni_monitor: string;
  sidecar_build: string;
  attestation_ref?: string;
  extensions?: Record<string, any>;
  timestamp: string;
  tenant_id: string;
  session_id: string;
  morph?: {
    env_snapshot_digest: string;
    branch_id: string;
    base_image: string;
    morphvm_id?: string;
  };
}

export interface CertSearchRequest {
  tenant_id?: string;
  policy_hash?: string;
  session_id?: string;
  start_time?: Date;
  end_time?: Date;
  ni_monitor?: string;
  limit?: number;
  offset?: number;
}

export interface CertSearchResponse {
  certificates: CertV1[];
  total: number;
  limit: number;
  offset: number;
}

export interface ReplayRequest {
  decision_id: string;
  trace_file?: string;
  config?: {
    seed?: number;
    locale?: string;
    timezone?: string;
    chunk_size?: number;
    flush_cadence_ms?: number;
    padding_policy?: string;
    drift_threshold?: number;
  };
  use_morph?: boolean;
  metadata?: Record<string, string>;
}

export interface ReplayResponse {
  job_id: string;
  status: string;
  started_at: string;
}

export interface ReplayStatus {
  job_id: string;
  status: string;
  progress: number;
  low_view_match_pct: number;
  outputs: string[];
  artifacts: string[];
  started_at: string;
  completed_at?: string;
  execution_time_ms: number;
  drift_detected: boolean;
  error_message?: string;
}

export class SentinelOpsClient {
  private client: AxiosInstance;

  constructor(baseURL: string = 'http://localhost:8000', apiKey?: string) {
    this.client = axios.create({
      baseURL,
      timeout: 30000,
      headers: {
        'Content-Type': 'application/json',
        ...(apiKey && { 'Authorization': `Bearer ${apiKey}` }),
      },
    });

    // Response interceptor for error handling
    this.client.interceptors.response.use(
      (response) => response,
      (error) => {
        if (error.response?.status === 401) {
          throw new Error('Authentication required');
        } else if (error.response?.status >= 500) {
          throw new Error(`Server error: ${error.response.data?.error || error.message}`);
        }
        throw error;
      }
    );
  }

  // Policy API
  async compilePolicy(request: PolicyCompileRequest): Promise<PolicyCompileResponse> {
    const response = await this.client.post<PolicyCompileResponse>('/api/v1/policy/compile', request);
    return response.data;
  }

  async buildPolicy(request: PolicyBuildRequest): Promise<PolicyBuildResponse> {
    const response = await this.client.post<PolicyBuildResponse>('/api/v1/policy/build', request);
    return response.data;
  }

  async runProofs(request: ProofRunRequest): Promise<ProofRunResponse> {
    const response = await this.client.post<ProofRunResponse>('/api/v1/proofs/run', request);
    return response.data;
  }

  async deployPolicy(request: DeployRequest): Promise<any> {
    const response = await this.client.post('/api/v1/runtime/deploy', request);
    return response.data;
  }

  async listPolicies(): Promise<any[]> {
    const response = await this.client.get('/api/v1/policies');
    return response.data.policies;
  }

  // Certificate API
  async verifyCert(cert: CertV1): Promise<boolean> {
    try {
      const response = await this.client.post('/api/v1/evidence/cert', cert);
      return response.status === 201;
    } catch (error) {
      return false;
    }
  }

  async searchCertificates(request: CertSearchRequest): Promise<CertSearchResponse> {
    const response = await this.client.post<CertSearchResponse>('/api/v1/evidence/search', request);
    return response.data;
  }

  async getCertificate(certId: string): Promise<CertV1> {
    const response = await this.client.get<CertV1>(`/api/v1/evidence/cert/${certId}`);
    return response.data;
  }

  // Replay API
  async startReplay(request: ReplayRequest): Promise<ReplayResponse> {
    const response = await this.client.post<ReplayResponse>('/api/v1/replay', request);
    return response.data;
  }

  async getReplayStatus(jobId: string): Promise<ReplayStatus> {
    const response = await this.client.get<ReplayStatus>(`/api/v1/replay/${jobId}`);
    return response.data;
  }

  async downloadPacket(decisionId: string): Promise<Blob> {
    // First create the packet
    const packetResponse = await this.client.post('/api/v1/compliance/packet', {
      session_id: decisionId,
    });
    
    const packetId = packetResponse.data.packet_id;
    
    // Then download it
    const response = await this.client.get(`/api/v1/compliance/packet/${packetId}`, {
      responseType: 'blob',
    });
    
    return response.data;
  }

  // Epoch operations
  async rotateEpoch(oldEpoch: number, newEpoch: number, reason?: string): Promise<any> {
    const response = await this.client.post('/api/v1/runtime/epoch/rotate', {
      old_epoch: oldEpoch,
      new_epoch: newEpoch,
      reason,
    });
    return response.data;
  }

  // Health and monitoring
  async getHealth(): Promise<any> {
    const response = await this.client.get('/health');
    return response.data;
  }

  async getSLO(): Promise<any> {
    const response = await this.client.get('/api/v1/runtime/slo');
    return response.data;
  }

  // CI helpers
  async assertCertsValid(certs: CertV1[]): Promise<boolean> {
    for (const cert of certs) {
      if (!(await this.verifyCert(cert))) {
        return false;
      }
    }
    return true;
  }

  async assertLowView(replayId: string, threshold: number = 0.999): Promise<boolean> {
    const status = await this.getReplayStatus(replayId);
    return status.low_view_match_pct >= threshold;
  }

  // Convenience methods
  async waitForReplay(jobId: string, timeoutMs: number = 300000): Promise<ReplayStatus> {
    const startTime = Date.now();
    
    while (Date.now() - startTime < timeoutMs) {
      const status = await this.getReplayStatus(jobId);
      
      if (status.status === 'completed' || status.status === 'failed') {
        return status;
      }
      
      await new Promise(resolve => setTimeout(resolve, 2000));
    }
    
    throw new Error(`Replay timeout after ${timeoutMs}ms`);
  }
}

// Export everything
export * from './types';
export default SentinelOpsClient;