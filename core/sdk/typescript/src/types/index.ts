// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

// Core types for the Provability Fabric SDK
export interface Trace {
  id: string;
  timestamp: string;
  subject: Subject;
  steps: Step[];
  metadata: Record<string, any>;
}

export interface Subject {
  id: string;
  type: SubjectType;
  capabilities: string[];
  labels: Record<string, string>;
}

export enum SubjectType {
  USER = 'user',
  SERVICE = 'service',
  ENCLAVE = 'enclave',
  EXTERNAL = 'external'
}

export interface Step {
  id: string;
  tool: string;
  input: any;
  output: any;
  timestamp: string;
  duration: number;
  success: boolean;
  error?: string;
}

export interface VerificationResult {
  valid: boolean;
  trace: Trace;
  violations: Violation[];
  timestamp: string;
}

export interface Violation {
  type: ViolationType;
  severity: ViolationSeverity;
  message: string;
  stepId?: string;
  details: Record<string, any>;
}

export enum ViolationType {
  CAPABILITY_MISMATCH = 'capability_mismatch',
  LABEL_VIOLATION = 'label_violation',
  POLICY_VIOLATION = 'policy_violation',
  TIMEOUT = 'timeout',
  AUTHENTICATION_FAILED = 'authentication_failed'
}

export enum ViolationSeverity {
  LOW = 'low',
  MEDIUM = 'medium',
  HIGH = 'high',
  CRITICAL = 'critical'
}

export interface SDKConfig {
  endpoint: string;
  timeout: number;
  retries: number;
  circuitBreaker: CircuitBreakerConfig;
  authentication: AuthConfig;
}

export interface CircuitBreakerConfig {
  failureThreshold: number;
  resetTimeout: number;
  monitoringWindow: number;
}

export interface AuthConfig {
  type: AuthType;
  credentials: Record<string, string>;
  tokenRefreshInterval: number;
}

export enum AuthType {
  NONE = 'none',
  API_KEY = 'api_key',
  JWT = 'jwt',
  OAUTH = 'oauth'
}

export interface MiddlewareConfig {
  addHeaders: boolean;
  verifyTrace: boolean;
  timeout: number;
  circuitBreaker: boolean;
  retries: boolean;
}

// Error types
export class PFError extends Error {
  constructor(
    message: string,
    public code: string,
    public statusCode: number,
    public details?: Record<string, any>
  ) {
    super(message);
    this.name = 'PFError';
  }
}

export class ValidationError extends PFError {
  constructor(message: string, details?: Record<string, any>) {
    super(message, 'VALIDATION_ERROR', 400, details);
    this.name = 'ValidationError';
  }
}

export class AuthenticationError extends PFError {
  constructor(message: string, details?: Record<string, any>) {
    super(message, 'AUTHENTICATION_ERROR', 401, details);
    this.name = 'AuthenticationError';
  }
}

export class AuthorizationError extends PFError {
  constructor(message: string, details?: Record<string, any>) {
    super(message, 'AUTHORIZATION_ERROR', 403, details);
    this.name = 'AuthorizationError';
  }
}

export class TimeoutError extends PFError {
  constructor(message: string, details?: Record<string, any>) {
    super(message, 'TIMEOUT_ERROR', 408, details);
    this.name = 'TimeoutError';
  }
}

export class CircuitBreakerError extends PFError {
  constructor(message: string, details?: Record<string, any>) {
    super(message, 'CIRCUIT_BREAKER_ERROR', 503, details);
    this.name = 'CircuitBreakerError';
  }
}
