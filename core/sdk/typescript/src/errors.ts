// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

export class ProvabilityFabricError extends Error {
  constructor(message: string, public code?: string) {
    super(message);
    this.name = 'ProvabilityFabricError';
  }
}

export class VerificationError extends ProvabilityFabricError {
  constructor(message: string) {
    super(message, 'VERIFICATION_ERROR');
    this.name = 'VerificationError';
  }
}

export class ConfigurationError extends ProvabilityFabricError {
  constructor(message: string) {
    super(message, 'CONFIGURATION_ERROR');
    this.name = 'ConfigurationError';
  }
}
