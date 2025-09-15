// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

export function formatTrace(trace: any): string {
  return JSON.stringify(trace, null, 2);
}

export function validateConfig(config: any): boolean {
  return config && typeof config === 'object';
}

export function generateTraceId(): string {
  return Math.random().toString(36).substring(2, 15);
}
