/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Tool Signature Manager for MCP Fraud Prevention
 * Implements tool call shape hashing & allow-list with pre-hashed tool signatures
 */

import crypto from 'crypto';
import winston from 'winston';

export interface ToolSignature {
  name: string;
  schemaDigest: string;
  signature: string;
  version: string;
  createdAt: Date;
  expiresAt?: Date;
}

export interface ToolSchemaProperty {
  type: string;
  properties?: Record<string, ToolSchemaProperty>;
  items?: ToolSchemaProperty;
  enum?: string[];
  minimum?: number;
  maximum?: number;
}

export interface ToolSchema {
  type: string;
  properties: Record<string, ToolSchemaProperty>;
  required?: string[];
  additionalProperties?: boolean;
}

export interface PermissionMatrixEntry {
  toolSignature: string;
  tenantId: string;
  epoch: number;
  allowed: boolean;
  constraints: string[];
  expiresAt: Date;
}

export class ToolSignatureManager {
  private logger: winston.Logger;
  private signatureCache: Map<string, ToolSignature> = new Map();
  private permissionMatrix: Map<string, PermissionMatrixEntry> = new Map();
  private allowedTools: Set<string> = new Set();

  constructor(logger: winston.Logger) {
    this.logger = logger;
    this.initializeDefaultTools();
  }

  /**
   * Compute tool signature hash without mutating the allow-list (for validation).
   */
  private computeSignatureHash(name: string, schema: ToolSchema): string {
    const schemaDigest = this.computeSchemaDigest(schema);
    return this.computeToolSignature(name, schemaDigest);
  }

  /**
   * Pre-hash tool signatures (name + schema digest) and register in allow-list.
   */
  public generateToolSignature(name: string, schema: ToolSchema): ToolSignature {
    const schemaDigest = this.computeSchemaDigest(schema);
    const signature = this.computeToolSignature(name, schemaDigest);
    
    const toolSignature: ToolSignature = {
      name,
      schemaDigest,
      signature,
      version: '1.0.0',
      createdAt: new Date(),
      expiresAt: new Date(Date.now() + 24 * 60 * 60 * 1000) // 24 hours
    };

    this.signatureCache.set(signature, toolSignature);
    this.allowedTools.add(signature);
    
    this.logger.info('MCP: Tool signature generated', {
      name,
      signature,
      schemaDigest: schemaDigest.substring(0, 16) + '...'
    });

    return toolSignature;
  }

  /**
   * Compute schema digest using JSON Canonicalization Scheme (JCS)
   */
  private computeSchemaDigest(schema: ToolSchema): string {
    // Canonicalize JSON schema for consistent hashing
    const canonicalSchema = this.canonicalizeJson(schema);
    return crypto.createHash('sha256').update(canonicalSchema).digest('hex');
  }

  /**
   * Compute tool signature from name and schema digest
   */
  private computeToolSignature(name: string, schemaDigest: string): string {
    const combined = `${name}:${schemaDigest}`;
    return crypto.createHash('sha256').update(combined).digest('hex');
  }

  /**
   * JSON Canonicalization Scheme (JCS) implementation
   * Ensures consistent JSON serialization for hashing
   */
  private canonicalizeJson(obj: unknown): string {
    // Sort object keys recursively
    const canonicalize = (value: unknown): unknown => {
      if (value === null || typeof value !== 'object') {
        return value;
      }
      
      if (Array.isArray(value)) {
        return value.map(canonicalize);
      }
      
      // Sort object keys
      const sortedKeys = Object.keys(value as Record<string, unknown>).sort();
      const result: Record<string, unknown> = {};
      for (const key of sortedKeys) {
        result[key] = canonicalize((value as Record<string, unknown>)[key]);
      }
      return result;
    };

    const canonical = canonicalize(obj);
    return JSON.stringify(canonical);
  }

  /**
   * Validate tool call against allow-list
   */
  public validateToolCall(
    toolName: string, 
    toolArgs: Record<string, unknown>, 
    tenantId: string, 
    epoch: number
  ): { allowed: boolean; reason?: string; toolSignature?: string } {
    try {
      // Generate signature for the tool call
      const schema = this.getToolSchema(toolName);
      if (!schema) {
        return {
          allowed: false,
          reason: `Unknown tool: ${toolName}`
        };
      }

      const toolSignature = this.computeSignatureHash(toolName, schema);
      
      // Check if tool signature is in allow-list (must be pre-registered at init)
      if (!this.allowedTools.has(toolSignature)) {
        return {
          allowed: false,
          reason: `Tool signature not in allow-list: ${toolSignature}`
        };
      }

      // Check permission matrix for tenant/epoch combination
      const permissionKey = `${toolSignature}:${tenantId}:${epoch}`;
      const permission = this.permissionMatrix.get(permissionKey);
      
      if (permission && !permission.allowed) {
        return {
          allowed: false,
          reason: `Permission denied for tenant ${tenantId} at epoch ${epoch}`,
          toolSignature
        };
      }

      // Validate input arguments against schema
      const validationResult = this.validateInputs(toolArgs, schema);
      if (!validationResult.valid) {
        return {
          allowed: false,
          reason: `Input validation failed: ${validationResult.errors.join(', ')}`,
          toolSignature
        };
      }

      this.logger.info('MCP: Tool call validated', {
        toolName,
        toolSignature,
        tenantId,
        epoch
      });

      return {
        allowed: true,
        toolSignature
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.logger.error('MCP: Tool call validation failed', {
        toolName,
        tenantId,
        epoch,
        error: errorMessage
      });

      return {
        allowed: false,
        reason: `Validation error: ${errorMessage}`
      };
    }
  }

  /**
   * Add permission matrix entry for sidecar checks
   */
  public addPermissionEntry(
    toolSignature: string,
    tenantId: string,
    epoch: number,
    allowed: boolean,
    constraints: string[] = [],
    expiresAt?: Date
  ): void {
    const permissionKey = `${toolSignature}:${tenantId}:${epoch}`;
    const entry: PermissionMatrixEntry = {
      toolSignature,
      tenantId,
      epoch,
      allowed,
      constraints,
      expiresAt: expiresAt || new Date(Date.now() + 60 * 60 * 1000) // 1 hour default
    };

    this.permissionMatrix.set(permissionKey, entry);
    
    this.logger.info('MCP: Permission entry added', {
      toolSignature,
      tenantId,
      epoch,
      allowed,
      constraints
    });
  }

  /**
   * Check sidecar constraints (tool_sig, tenant, epoch)
   */
  public checkSidecarConstraints(
    toolSignature: string,
    tenantId: string,
    epoch: number
  ): { allowed: boolean; reason?: string; constraints?: string[] } {
    const permissionKey = `${toolSignature}:${tenantId}:${epoch}`;
    const permission = this.permissionMatrix.get(permissionKey);

    if (!permission) {
      // No explicit permission, check if tool is generally allowed
      if (this.allowedTools.has(toolSignature)) {
        return { allowed: true };
      }
      return {
        allowed: false,
        reason: `No permission found for tool signature ${toolSignature}`
      };
    }

    if (permission.expiresAt && new Date() > permission.expiresAt) {
      return {
        allowed: false,
        reason: `Permission expired for tool signature ${toolSignature}`
      };
    }

    return {
      allowed: permission.allowed,
      reason: permission.allowed ? undefined : 'Permission explicitly denied',
      constraints: permission.constraints
    };
  }

  /**
   * Validate inputs against schema using JCS
   */
  private validateInputs(inputs: Record<string, unknown>, schema: ToolSchema): { valid: boolean; errors: string[] } {
    const errors: string[] = [];
    
    try {
      // Canonicalize inputs for validation
      const canonicalInputs = this.canonicalizeJson(inputs);
      const parsedInputs = JSON.parse(canonicalInputs);

      // Check required properties
      if (schema.required) {
        for (const requiredProp of schema.required) {
          if (!(requiredProp in parsedInputs)) {
            errors.push(`Missing required property: ${requiredProp}`);
          }
        }
      }

      // Validate property types
      if (schema.properties) {
        for (const [propName, propSchema] of Object.entries(schema.properties)) {
          if (propName in parsedInputs) {
            const propValue = parsedInputs[propName];
            const propType = propSchema.type;
            
            if (propType === 'string' && typeof propValue !== 'string') {
              errors.push(`Property ${propName} must be a string`);
            } else if (propType === 'number' && typeof propValue !== 'number') {
              errors.push(`Property ${propName} must be a number`);
            } else if (propType === 'boolean' && typeof propValue !== 'boolean') {
              errors.push(`Property ${propName} must be a boolean`);
            } else if (propType === 'array' && !Array.isArray(propValue)) {
              errors.push(`Property ${propName} must be an array`);
            } else if (propType === 'object' && (typeof propValue !== 'object' || Array.isArray(propValue))) {
              errors.push(`Property ${propName} must be an object`);
            }
          }
        }
      }

      // Check for additional properties if not allowed
      if (schema.additionalProperties === false) {
        const allowedProps = new Set(Object.keys(schema.properties || {}));
        for (const propName of Object.keys(parsedInputs)) {
          if (!allowedProps.has(propName)) {
            errors.push(`Additional property not allowed: ${propName}`);
          }
        }
      }

      return {
        valid: errors.length === 0,
        errors
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      errors.push(`Input validation error: ${errorMessage}`);
      return { valid: false, errors };
    }
  }

  /**
   * Get tool schema by name
   */
  private getToolSchema(toolName: string): ToolSchema | null {
    const schemas: Record<string, ToolSchema> = {
      'query_capsules': {
        type: 'object',
        properties: {
          filter: {
            type: 'object',
            properties: {
              status: { type: 'string', enum: ['active', 'paused', 'terminated'] },
              tags: { type: 'array', items: { type: 'string' } },
              behaviorHash: { type: 'string' }
            }
          },
          limit: { type: 'number', minimum: 1, maximum: 1000 }
        },
        required: []
      },
      'verify_behavior_guarantee': {
        type: 'object',
        properties: {
          capsuleId: { type: 'string' },
          behaviorSpec: { type: 'string' },
          proofType: { type: 'string', enum: ['lean', 'marabou', 'dryvr'] }
        },
        required: ['capsuleId', 'behaviorSpec']
      },
      'log_audit_event': {
        type: 'object',
        properties: {
          eventType: { type: 'string' },
          agentId: { type: 'string' },
          details: { type: 'object' },
          severity: { type: 'string', enum: ['info', 'warning', 'error', 'critical'] }
        },
        required: ['eventType', 'agentId', 'details']
      },
      'ingest_transaction': {
        type: 'object',
        properties: {
          transaction_id: { type: 'string' },
          amount: { type: 'number', minimum: 0 },
          merchant: { type: 'string' },
          user_id: { type: 'string' },
          card_number: { type: 'string' },
          location: { type: 'string' },
          tenant_id: { type: 'string' }
        },
        required: ['transaction_id', 'amount', 'merchant', 'user_id', 'tenant_id']
      },
      'score_fraud': {
        type: 'object',
        properties: {
          transaction_id: { type: 'string' },
          tenant_id: { type: 'string' }
        },
        required: ['transaction_id', 'tenant_id']
      },
      'get_transaction': {
        type: 'object',
        properties: {
          transaction_id: { type: 'string' },
          tenant_id: { type: 'string' }
        },
        required: ['transaction_id', 'tenant_id']
      }
    };

    return schemas[toolName] || null;
  }

  /**
   * Initialize default allowed tools
   */
  private initializeDefaultTools(): void {
    const defaultTools = [
      'query_capsules',
      'verify_behavior_guarantee', 
      'log_audit_event',
      'ingest_transaction',
      'score_fraud',
      'get_transaction'
    ];

    for (const toolName of defaultTools) {
      const schema = this.getToolSchema(toolName);
      if (schema) {
        this.generateToolSignature(toolName, schema);
      }
    }

    this.logger.info('MCP: Default tools initialized', {
      toolCount: this.allowedTools.size
    });
  }

  /**
   * Get cache statistics for monitoring
   */
  public getCacheStats(): {
    signatureCacheSize: number;
    permissionMatrixSize: number;
    allowedToolsCount: number;
  } {
    return {
      signatureCacheSize: this.signatureCache.size,
      permissionMatrixSize: this.permissionMatrix.size,
      allowedToolsCount: this.allowedTools.size
    };
  }

  /**
   * Clean up expired entries
   */
  public cleanupExpiredEntries(): void {
    const now = new Date();
    let cleaned = 0;

    // Clean expired signatures
    for (const [signature, toolSig] of this.signatureCache.entries()) {
      if (toolSig.expiresAt && now > toolSig.expiresAt) {
        this.signatureCache.delete(signature);
        this.allowedTools.delete(signature);
        cleaned++;
      }
    }

    // Clean expired permissions
    for (const [key, permission] of this.permissionMatrix.entries()) {
      if (now > permission.expiresAt) {
        this.permissionMatrix.delete(key);
        cleaned++;
      }
    }

    if (cleaned > 0) {
      this.logger.info('MCP: Cleaned up expired entries', { cleaned });
    }
  }
}

export default ToolSignatureManager;
