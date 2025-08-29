/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

export interface PIIPattern {
  name: string;
  pattern: RegExp;
  severity: 'low' | 'medium' | 'high' | 'critical';
  description: string;
}

export interface SecretPattern {
  name: string;
  pattern: RegExp;
  entropyThreshold?: number;
  severity: 'low' | 'medium' | 'high' | 'critical';
  description: string;
}

export interface DetectionResult {
  type: 'pii' | 'secret';
  name: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
  match: string;
  position: {
    start: number;
    end: number;
  };
  description: string;
}

export interface GuardConfig {
  ledgerUrl: string;
  tenantId: string;
  sessionId: string;
  enablePII: boolean;
  enableSecrets: boolean;
  customPatterns?: {
    pii?: PIIPattern[];
    secrets?: SecretPattern[];
  };
  timeout: number;
  retries: number;
}

export interface IncidentPayload {
  type: 'rag_content_blocked';
  timestamp: string;
  tenantId: string;
  sessionId: string;
  detections: DetectionResult[];
  originalContentLength: number;
  blockedContentHash: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
}

export interface GuardResponse {
  allowed: boolean;
  safeContent?: string;
  blockedDetections?: DetectionResult[];
  incidentId?: string;
}

export interface LedgerResponse {
  success: boolean;
  incidentId?: string;
  error?: string;
}
