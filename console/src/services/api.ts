import axios from 'axios';

const API_BASE_URL = process.env.REACT_APP_API_BASE_URL || 'http://localhost:8000';

const api = axios.create({
  baseURL: API_BASE_URL,
  timeout: 30000,
  headers: {
    'Content-Type': 'application/json',
  },
});

// Spec Service APIs
export const compilePolicy = async (request: {
  english: string;
  policy_id: string;
  version: string;
  metadata?: Record<string, string>;
}) => {
  const response = await api.post('/api/v1/policy/compile', request);
  return response.data;
};

export const getPolicy = async (policyId: string) => {
  const response = await api.get(`/api/v1/policy/${policyId}`);
  return response.data;
};

export const listPolicies = async () => {
  const response = await api.get('/api/v1/policies');
  return response.data;
};

// Proof Service APIs
export const runProofs = async (request: {
  policy_hash: string;
  action_dsl: any;
  proof_inputs?: Record<string, any>;
  use_morph?: boolean;
  morph_shards?: number;
}) => {
  const response = await api.post('/api/v1/proofs/run', request);
  return response.data;
};

export const getProofArtifact = async (hash: string) => {
  const response = await api.get(`/api/v1/artifacts/${hash}`);
  return response.data;
};

export const listProofArtifacts = async () => {
  const response = await api.get('/api/v1/artifacts');
  return response.data;
};

// Build Orchestrator APIs
export const buildPolicy = async (request: {
  policy_hash: string;
  action_dsl: Record<string, any>;
  proof_hash: string;
  metadata?: Record<string, string>;
  signing_key?: string;
}) => {
  const response = await api.post('/api/v1/policy/build', request);
  return response.data;
};

export const getBuild = async (buildId: string) => {
  const response = await api.get(`/api/v1/builds/${buildId}`);
  return response.data;
};

export const listBuilds = async () => {
  const response = await api.get('/api/v1/builds');
  return response.data;
};

// Runtime APIs
export const deployPolicy = async (request: {
  policy_hash: string;
  automata_hash: string;
  epoch: number;
}) => {
  const response = await api.post('/api/v1/runtime/deploy', request);
  return response.data;
};

export const rotateEpoch = async (request: {
  old_epoch: number;
  new_epoch: number;
  reason?: string;
}) => {
  const response = await api.post('/api/v1/runtime/epoch/rotate', request);
  return response.data;
};

export const getRuntimeSLO = async () => {
  const response = await api.get('/api/v1/runtime/slo');
  return response.data;
};

// Evidence Service APIs
export const searchCertificates = async (request: {
  tenant_id?: string;
  policy_hash?: string;
  session_id?: string;
  start_time?: Date;
  end_time?: Date;
  ni_monitor?: string;
  limit?: number;
  offset?: number;
}) => {
  const response = await api.post('/api/v1/evidence/search', request);
  return response.data;
};

export const getCertificate = async (certId: string) => {
  const response = await api.get(`/api/v1/evidence/cert/${certId}`);
  return response.data;
};

export const buildCompliancePacket = async (request: {
  tenant_id?: string;
  policy_hash?: string;
  start_time?: Date;
  end_time?: Date;
}) => {
  const response = await api.post('/api/v1/compliance/packet', request);
  return response.data;
};

export const downloadCompliancePacket = async (packetId: string) => {
  const response = await api.get(`/api/v1/compliance/packet/${packetId}`, {
    responseType: 'blob',
  });
  return response.data;
};

// Replay Service APIs
export const startReplay = async (request: {
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
}) => {
  const response = await api.post('/api/v1/replay', request);
  return response.data;
};

export const getReplayStatus = async (jobId: string) => {
  const response = await api.get(`/api/v1/replay/${jobId}`);
  return response.data;
};

export const listReplays = async () => {
  const response = await api.get('/api/v1/replays');
  return response.data;
};

export const downloadReplayArtifact = async (jobId: string, artifact: string) => {
  const response = await api.get(`/api/v1/replay/${jobId}/artifact/${artifact}`, {
    responseType: 'blob',
  });
  return response.data;
};

// Health check for all services
export const checkServiceHealth = async (service: string) => {
  try {
    const response = await api.get(`/api/v1/health`, {
      timeout: 5000,
    });
    return { service, status: 'healthy', data: response.data };
  } catch (error) {
    return { service, status: 'unhealthy', error: (error as Error).message };
  }
};

// Error handling interceptor
api.interceptors.response.use(
  (response) => response,
  (error) => {
    if (error.response?.status === 401) {
      // Handle authentication errors
      console.error('Authentication required');
    } else if (error.response?.status >= 500) {
      // Handle server errors
      console.error('Server error:', error.response.data);
    }
    return Promise.reject(error);
  }
);

export default api;