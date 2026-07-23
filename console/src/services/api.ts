// console/src/services/api.ts
import axios, { AxiosHeaders } from 'axios';

/**
 * Choose a sane default base URL:
 * - In the browser, use same-origin (so Console → Nginx → api-gateway proxy works)
 * - As a fallback (e.g. in tests), use the docker compose service name for the gateway
 */
const DEFAULT_BASE =
  (typeof window !== 'undefined' && window.location?.origin)
    ? window.location.origin
    : 'http://api-gateway:8000';

const API_BASE_URL =
  (process.env.REACT_APP_API_BASE_URL?.trim() || DEFAULT_BASE);

/** Shared Axios instance */
const api = axios.create({
  baseURL: API_BASE_URL,
  timeout: 60000,
  headers: {
    'Content-Type': 'application/json',
  },
});

/**
 * ---- Interceptors ----
 * Axios v1 exposes `config.headers` as an AxiosHeaders object.
 * Do NOT replace it with a plain object; use AxiosHeaders to set values.
 */
api.interceptors.request.use((config) => {
  const headers = AxiosHeaders.from(config.headers);
  headers.set('X-Requested-With', 'XMLHttpRequest');
  config.headers = headers;
  return config;
});

api.interceptors.response.use(
  (response) => response,
  (error) => {
    // Basic shape-safe logging without depending on AxiosError type guards
    const status = error?.response?.status;
    if (status === 401) {
      console.error('Authentication required');
    } else if (status >= 500) {
      console.error('Server error:', error?.response?.data ?? error?.message);
    } else if (!status) {
      // Network or CORS errors often present without a status
      console.error('Network error:', error?.message);
    }
    return Promise.reject(error);
  }
);

/* =========================
 *      API FUNCTIONS
 * ========================= */

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
  start_time?: Date | string;
  end_time?: Date | string;
  ni_monitor?: string;
  limit?: number;
  offset?: number;
}) => {
  const response = await api.post('/api/v1/evidence/search', request);
  return response.data;
};

export const verifyCertificate = async (payload: {
  raw?: any;
  cert?: any;
  jwks_url?: string;
  pem_pub?: string;
}) => {
  const response = await api.post('/api/v1/evidence/validate', payload);
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

// Dev Mode (E4)
export const getDevModeStreamUrl = (jobId: string) => `${API_BASE_URL}/api/v1/replay/${jobId}/stream`;
export const getDFAState = async (jobId: string) => {
  const response = await api.get(`/api/v1/replay/${jobId}/dfa_state`);
  return response.data as { job_id: string; state_id: number };
};

// Telemetry (M1)
export const getTelemetryOpt = async () => {
  const response = await api.get('/api/v1/telemetry/opt');
  return response.data as { enabled: boolean };
};
export const setTelemetryOpt = async (enabled: boolean) => {
  const response = await api.post('/api/v1/telemetry/opt', { enabled });
  return response.data as { ok: boolean; enabled: boolean };
};
export const sendTelemetryEvent = async (type: string, data?: Record<string, any>) => {
  const payload = { type, ts: new Date().toISOString(), data: data ?? {} };
  const response = await api.post('/api/v1/telemetry/event', payload);
  return response.data;
};

// Health check for all services (via gateway)
export const checkServiceHealth = async (service: string) => {
  try {
    const response = await api.get('/api/v1/health', { timeout: 5000 });
    return { service, status: 'healthy', data: response.data };
  } catch (error: any) {
    return { service, status: 'unhealthy', error: error?.message ?? String(error) };
  }
};

// Enhanced Evidence API functions

/**
 * Get detailed certificate information (core or extended)
 */
export const getCertificateDetails = async (bundleId: string, sessionId: string): Promise<any> => {
  const response = await api.get(`/api/v1/evidence/cert/${bundleId}/${sessionId}`);
  return response.data;
};

/**
 * Promote a test vector to golden status
 */
export const promoteToGolden = async (decisionId: string, testVectorPath: string): Promise<void> => {
  await api.post(`/api/v1/replay/promote-golden`, {
    decision_id: decisionId,
    test_vector_path: testVectorPath,
  });
};

/**
 * Get enhanced replay status with metrics
 */
export const getEnhancedReplayStatus = async (jobId: string): Promise<any> => {
  const response = await api.get(`/api/v1/replay/enhanced/${jobId}`);
  return response.data;
};

/**
 * Start enhanced replay
 */
export const startEnhancedReplay = async (request: {
  decision_id: string;
  trace_file?: string;
  config?: any;
  use_morph?: boolean;
  metadata?: Record<string, string>;
}): Promise<any> => {
  const response = await api.post('/api/v1/replay/enhanced', request);
  return response.data;
};

export default api;
