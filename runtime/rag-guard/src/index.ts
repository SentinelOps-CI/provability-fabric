/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

export { RAGGuard } from './guard';
export { PIIDetector } from './detectors/pii';
export { SecretDetector } from './detectors/secrets';
export { LedgerClient } from './ledger';

export type {
  GuardConfig,
  GuardResponse,
  DetectionResult,
  PIIPattern,
  SecretPattern,
  IncidentPayload,
  LedgerResponse
} from './types';

// Convenience factory function
export function createRAGGuard(config: GuardConfig): RAGGuard {
  return new RAGGuard(config);
}

// Default configurations
export const defaultConfig: Partial<GuardConfig> = {
  enablePII: true,
  enableSecrets: true,
  timeout: 5000,
  retries: 3
};
