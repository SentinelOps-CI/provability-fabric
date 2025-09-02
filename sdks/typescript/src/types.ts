// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

// Re-export all types for convenience
export * from './index';

// Additional utility types
export interface PlatformConfig {
  baseURL: string;
  apiKey?: string;
  timeout?: number;
  retries?: number;
}

export interface APIError {
  message: string;
  code?: string;
  details?: any;
}

export interface PaginationParams {
  limit?: number;
  offset?: number;
}

export interface TimeRange {
  start_time?: Date;
  end_time?: Date;
}

export interface TenantContext {
  tenant_id: string;
  permissions?: string[];
}

// Webhook types for real-time updates
export interface WebhookEvent {
  event_type: string;
  data: any;
  timestamp: string;
  tenant_id: string;
}

export interface PolicyWebhookEvent extends WebhookEvent {
  event_type: 'policy.compiled' | 'policy.deployed' | 'policy.failed';
  data: {
    policy_id: string;
    policy_hash: string;
    status: string;
  };
}

export interface ReplayWebhookEvent extends WebhookEvent {
  event_type: 'replay.started' | 'replay.completed' | 'replay.failed';
  data: {
    job_id: string;
    decision_id: string;
    status: string;
    low_view_match_pct?: number;
  };
}

export interface CertWebhookEvent extends WebhookEvent {
  event_type: 'cert.emitted' | 'cert.validation_failed';
  data: {
    session_id: string;
    ni_monitor: string;
    policy_hash: string;
  };
}