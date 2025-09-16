/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * JCS (JSON Canonicalization Scheme) Validator for MCP Fraud Prevention
 * Implements early input rejection via JCS'ed schema validation
 */

import crypto from 'crypto';
import winston from 'winston';

export interface ValidationResult {
  valid: boolean;
  errors: string[];
  warnings: string[];
  canonicalized?: string;
  schemaDigest?: string;
}

export interface SchemaDefinition {
  type: string;
  properties?: Record<string, any>;
  required?: string[];
  additionalProperties?: boolean;
  pattern?: string;
  minLength?: number;
  maxLength?: number;
  minimum?: number;
  maximum?: number;
  enum?: any[];
  items?: any;
  oneOf?: any[];
  anyOf?: any[];
  allOf?: any[];
  not?: any;
}

export interface ValidationRule {
  field: string;
  type: 'string' | 'number' | 'boolean' | 'array' | 'object' | 'null';
  required?: boolean;
  pattern?: RegExp;
  minLength?: number;
  maxLength?: number;
  minimum?: number;
  maximum?: number;
  enum?: any[];
  customValidator?: (value: any) => { valid: boolean; error?: string };
}

export class JCSValidator {
  private logger: winston.Logger;
  private schemaCache: Map<string, SchemaDefinition> = new Map();
  private validationCache: Map<string, ValidationResult> = new Map();

  constructor(logger: winston.Logger) {
    this.logger = logger;
    this.initializeDefaultSchemas();
  }

  /**
   * Validate input using JCS canonicalization and schema validation
   */
  public validateInput(
    input: any,
    schema: SchemaDefinition,
    options: {
      strictMode?: boolean;
      allowAdditionalProperties?: boolean;
      customRules?: ValidationRule[];
    } = {}
  ): ValidationResult {
    try {
      const errors: string[] = [];
      const warnings: string[] = [];

      // Step 1: Canonicalize input using JCS
      const canonicalized = this.canonicalizeJson(input);
      const schemaDigest = this.computeSchemaDigest(schema);

      // Step 2: Parse canonicalized input
      let parsedInput: any;
      try {
        parsedInput = JSON.parse(canonicalized);
      } catch (error) {
        return {
          valid: false,
          errors: ['Input is not valid JSON'],
          canonicalized,
          schemaDigest
        };
      }

      // Step 3: Basic type validation
      if (schema.type && typeof parsedInput !== schema.type) {
        errors.push(`Expected type '${schema.type}', got '${typeof parsedInput}'`);
      }

      // Step 4: Object property validation
      if (schema.type === 'object' && typeof parsedInput === 'object' && !Array.isArray(parsedInput)) {
        this.validateObjectProperties(parsedInput, schema, errors, warnings, options);
      }

      // Step 5: Array validation
      if (schema.type === 'array' && Array.isArray(parsedInput)) {
        this.validateArrayItems(parsedInput, schema, errors, warnings, options);
      }

      // Step 6: String validation
      if (schema.type === 'string' && typeof parsedInput === 'string') {
        this.validateString(parsedInput, schema, errors, warnings);
      }

      // Step 7: Number validation
      if (schema.type === 'number' && typeof parsedInput === 'number') {
        this.validateNumber(parsedInput, schema, errors, warnings);
      }

      // Step 8: Custom validation rules
      if (options.customRules) {
        this.applyCustomRules(parsedInput, options.customRules, errors, warnings);
      }

      // Step 9: Pattern validation
      if (schema.pattern && typeof parsedInput === 'string') {
        const regex = new RegExp(schema.pattern);
        if (!regex.test(parsedInput)) {
          errors.push(`String does not match required pattern: ${schema.pattern}`);
        }
      }

      // Step 10: Enum validation
      if (schema.enum && !schema.enum.includes(parsedInput)) {
        errors.push(`Value '${parsedInput}' is not in allowed enum values: ${schema.enum.join(', ')}`);
      }

      // Step 11: OneOf/AnyOf/AllOf validation
      this.validateCompositionSchemas(parsedInput, schema, errors, warnings);

      const result: ValidationResult = {
        valid: errors.length === 0,
        errors,
        warnings,
        canonicalized,
        schemaDigest
      };

      // Cache result for performance
      const cacheKey = this.generateCacheKey(input, schema);
      this.validationCache.set(cacheKey, result);

      this.logger.debug('MCP: JCS validation completed', {
        valid: result.valid,
        errorCount: errors.length,
        warningCount: warnings.length,
        schemaDigest: schemaDigest.substring(0, 16) + '...'
      });

      return result;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.logger.error('MCP: JCS validation failed', {
        error: errorMessage,
        inputType: typeof input
      });

      return {
        valid: false,
        errors: [`Validation error: ${errorMessage}`],
        warnings: []
      };
    }
  }

  /**
   * Early rejection for malformed inputs before expensive operations
   */
  public earlyReject(input: any, schema: SchemaDefinition): { reject: boolean; reason?: string } {
    try {
      // Quick type check
      if (schema.type && typeof input !== schema.type) {
        return {
          reject: true,
          reason: `Type mismatch: expected ${schema.type}, got ${typeof input}`
        };
      }

      // Quick required field check
      if (schema.required && Array.isArray(schema.required)) {
        for (const field of schema.required) {
          if (!(field in input)) {
            return {
              reject: true,
              reason: `Missing required field: ${field}`
            };
          }
        }
      }

      // Quick string length check
      if (schema.type === 'string' && typeof input === 'string') {
        if (schema.minLength && input.length < schema.minLength) {
          return {
            reject: true,
            reason: `String too short: minimum length ${schema.minLength}`
          };
        }
        if (schema.maxLength && input.length > schema.maxLength) {
          return {
            reject: true,
            reason: `String too long: maximum length ${schema.maxLength}`
          };
        }
      }

      // Quick number range check
      if (schema.type === 'number' && typeof input === 'number') {
        if (schema.minimum !== undefined && input < schema.minimum) {
          return {
            reject: true,
            reason: `Number too small: minimum value ${schema.minimum}`
          };
        }
        if (schema.maximum !== undefined && input > schema.maximum) {
          return {
            reject: true,
            reason: `Number too large: maximum value ${schema.maximum}`
          };
        }
      }

      return { reject: false };
    } catch (error) {
      return {
        reject: true,
        reason: `Early validation error: ${error instanceof Error ? error.message : 'Unknown error'}`
      };
    }
  }

  /**
   * JSON Canonicalization Scheme (JCS) implementation
   */
  private canonicalizeJson(obj: any): string {
    const canonicalize = (value: any): any => {
      if (value === null || typeof value !== 'object') {
        return value;
      }
      
      if (Array.isArray(value)) {
        return value.map(canonicalize);
      }
      
      // Sort object keys recursively
      const sortedKeys = Object.keys(value).sort();
      const result: any = {};
      for (const key of sortedKeys) {
        result[key] = canonicalize(value[key]);
      }
      return result;
    };

    const canonical = canonicalize(obj);
    return JSON.stringify(canonical);
  }

  /**
   * Compute schema digest for caching
   */
  private computeSchemaDigest(schema: SchemaDefinition): string {
    const canonicalSchema = this.canonicalizeJson(schema);
    return crypto.createHash('sha256').update(canonicalSchema).digest('hex');
  }

  /**
   * Validate object properties
   */
  private validateObjectProperties(
    obj: any,
    schema: SchemaDefinition,
    errors: string[],
    warnings: string[],
    options: any
  ): void {
    if (!schema.properties) return;

    // Check required properties
    if (schema.required) {
      for (const field of schema.required) {
        if (!(field in obj)) {
          errors.push(`Missing required property: ${field}`);
        }
      }
    }

    // Validate each property
    for (const [propName, propSchema] of Object.entries(schema.properties)) {
      if (propName in obj) {
        const propValue = obj[propName];
        const propType = propSchema.type;

        // Type validation
        if (propType === 'string' && typeof propValue !== 'string') {
          errors.push(`Property '${propName}' must be a string`);
        } else if (propType === 'number' && typeof propValue !== 'number') {
          errors.push(`Property '${propName}' must be a number`);
        } else if (propType === 'boolean' && typeof propValue !== 'boolean') {
          errors.push(`Property '${propName}' must be a boolean`);
        } else if (propType === 'array' && !Array.isArray(propValue)) {
          errors.push(`Property '${propName}' must be an array`);
        } else if (propType === 'object' && (typeof propValue !== 'object' || Array.isArray(propValue))) {
          errors.push(`Property '${propName}' must be an object`);
        }

        // Recursive validation for nested objects
        if (propType === 'object' && typeof propValue === 'object' && !Array.isArray(propValue)) {
          this.validateObjectProperties(propValue, propSchema, errors, warnings, options);
        }
      }
    }

    // Check for additional properties
    if (schema.additionalProperties === false) {
      const allowedProps = new Set(Object.keys(schema.properties));
      for (const propName of Object.keys(obj)) {
        if (!allowedProps.has(propName)) {
          errors.push(`Additional property '${propName}' not allowed`);
        }
      }
    }
  }

  /**
   * Validate array items
   */
  private validateArrayItems(
    arr: any[],
    schema: SchemaDefinition,
    errors: string[],
    warnings: string[],
    options: any
  ): void {
    if (schema.items) {
      for (let i = 0; i < arr.length; i++) {
        const itemResult = this.validateInput(arr[i], schema.items, options);
        if (!itemResult.valid) {
          errors.push(`Array item at index ${i}: ${itemResult.errors.join(', ')}`);
        }
      }
    }
  }

  /**
   * Validate string constraints
   */
  private validateString(
    str: string,
    schema: SchemaDefinition,
    errors: string[],
    warnings: string[]
  ): void {
    if (schema.minLength !== undefined && str.length < schema.minLength) {
      errors.push(`String length ${str.length} is less than minimum ${schema.minLength}`);
    }
    if (schema.maxLength !== undefined && str.length > schema.maxLength) {
      errors.push(`String length ${str.length} exceeds maximum ${schema.maxLength}`);
    }
    if (schema.pattern) {
      const regex = new RegExp(schema.pattern);
      if (!regex.test(str)) {
        errors.push(`String does not match pattern: ${schema.pattern}`);
      }
    }
  }

  /**
   * Validate number constraints
   */
  private validateNumber(
    num: number,
    schema: SchemaDefinition,
    errors: string[],
    warnings: string[]
  ): void {
    if (schema.minimum !== undefined && num < schema.minimum) {
      errors.push(`Number ${num} is less than minimum ${schema.minimum}`);
    }
    if (schema.maximum !== undefined && num > schema.maximum) {
      errors.push(`Number ${num} exceeds maximum ${schema.maximum}`);
    }
  }

  /**
   * Apply custom validation rules
   */
  private applyCustomRules(
    input: any,
    rules: ValidationRule[],
    errors: string[],
    warnings: string[]
  ): void {
    for (const rule of rules) {
      if (rule.field in input) {
        const value = input[rule.field];
        
        // Type check
        if (typeof value !== rule.type) {
          errors.push(`Field '${rule.field}' must be of type '${rule.type}'`);
          continue;
        }

        // Custom validator
        if (rule.customValidator) {
          const result = rule.customValidator(value);
          if (!result.valid) {
            errors.push(`Field '${rule.field}': ${result.error || 'Custom validation failed'}`);
          }
        }
      } else if (rule.required) {
        errors.push(`Required field '${rule.field}' is missing`);
      }
    }
  }

  /**
   * Validate composition schemas (oneOf, anyOf, allOf)
   */
  private validateCompositionSchemas(
    input: any,
    schema: SchemaDefinition,
    errors: string[],
    warnings: string[]
  ): void {
    if (schema.oneOf) {
      const validCount = schema.oneOf.filter(subSchema => 
        this.validateInput(input, subSchema).valid
      ).length;
      if (validCount !== 1) {
        errors.push(`Input must match exactly one of the oneOf schemas (matched ${validCount})`);
      }
    }

    if (schema.anyOf) {
      const validCount = schema.anyOf.filter(subSchema => 
        this.validateInput(input, subSchema).valid
      ).length;
      if (validCount === 0) {
        errors.push('Input must match at least one of the anyOf schemas');
      }
    }

    if (schema.allOf) {
      for (const subSchema of schema.allOf) {
        const result = this.validateInput(input, subSchema);
        if (!result.valid) {
          errors.push(`Input must match allOf schema: ${result.errors.join(', ')}`);
        }
      }
    }

    if (schema.not) {
      const result = this.validateInput(input, schema.not);
      if (result.valid) {
        errors.push('Input must not match the not schema');
      }
    }
  }

  /**
   * Generate cache key for validation results
   */
  private generateCacheKey(input: any, schema: SchemaDefinition): string {
    const inputHash = crypto.createHash('sha256').update(JSON.stringify(input)).digest('hex');
    const schemaHash = this.computeSchemaDigest(schema);
    return `${inputHash}:${schemaHash}`;
  }

  /**
   * Initialize default schemas for common MCP operations
   */
  private initializeDefaultSchemas(): void {
    const schemas: Record<string, SchemaDefinition> = {
      tool_call: {
        type: 'object',
        properties: {
          name: { type: 'string', minLength: 1, maxLength: 100 },
          arguments: { type: 'object' }
        },
        required: ['name', 'arguments'],
        additionalProperties: false
      },
      tenant_context: {
        type: 'object',
        properties: {
          tenantId: { type: 'string', pattern: '^[a-zA-Z0-9_-]+$' },
          userId: { type: 'string', minLength: 1 },
          permissions: { type: 'array', items: { type: 'string' } }
        },
        required: ['tenantId', 'userId'],
        additionalProperties: false
      },
      fraud_transaction: {
        type: 'object',
        properties: {
          transaction_id: { type: 'string', minLength: 1, maxLength: 50 },
          amount: { type: 'number', minimum: 0, maximum: 1000000 },
          merchant: { type: 'string', minLength: 1, maxLength: 100 },
          user_id: { type: 'string', minLength: 1, maxLength: 50 },
          tenant_id: { type: 'string', pattern: '^[a-zA-Z0-9_-]+$' }
        },
        required: ['transaction_id', 'amount', 'merchant', 'user_id', 'tenant_id'],
        additionalProperties: false
      }
    };

    for (const [name, schema] of Object.entries(schemas)) {
      this.schemaCache.set(name, schema);
    }

    this.logger.info('MCP: Default JCS schemas initialized', {
      schemaCount: Object.keys(schemas).length
    });
  }

  /**
   * Get schema by name
   */
  public getSchema(name: string): SchemaDefinition | null {
    return this.schemaCache.get(name) || null;
  }

  /**
   * Add custom schema
   */
  public addSchema(name: string, schema: SchemaDefinition): void {
    this.schemaCache.set(name, schema);
    this.logger.info('MCP: Custom schema added', { name });
  }

  /**
   * Get validation statistics
   */
  public getStats(): {
    schemaCount: number;
    cacheSize: number;
    cacheHitRate: number;
  } {
    return {
      schemaCount: this.schemaCache.size,
      cacheSize: this.validationCache.size,
      cacheHitRate: 0 // TODO: Implement hit rate tracking
    };
  }

  /**
   * Clear validation cache
   */
  public clearCache(): void {
    this.validationCache.clear();
    this.logger.info('MCP: Validation cache cleared');
  }
}

export default JCSValidator;
