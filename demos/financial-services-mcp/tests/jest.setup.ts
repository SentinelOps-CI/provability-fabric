/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Jest Test Setup Configuration
 * Global test environment configuration and utilities
 */

import { performance } from 'perf_hooks';

// Extend Jest matchers with custom financial testing matchers
declare global {
  namespace jest {
    interface Matchers<R> {
      toBeWithinLatencyThreshold(maxLatencyMs: number): R;
      toMeetThroughputRequirement(minTps: number): R;
      toHaveValidFraudProbability(): R;
      toBeValidAuditEvent(): R;
      toHaveSecureHash(): R;
      toMeetComplianceRequirements(): R;
    }
  }
}

// Custom Jest matchers for financial services testing
expect.extend({
  toBeWithinLatencyThreshold(received: number, maxLatencyMs: number) {
    const pass = received <= maxLatencyMs;
    
    if (pass) {
      return {
        message: () => `Expected latency ${received}ms to exceed ${maxLatencyMs}ms`,
        pass: true,
      };
    } else {
      return {
        message: () => `Expected latency ${received}ms to be within ${maxLatencyMs}ms threshold`,
        pass: false,
      };
    }
  },

  toMeetThroughputRequirement(received: number, minTps: number) {
    const pass = received >= minTps;
    
    if (pass) {
      return {
        message: () => `Expected throughput ${received} TPS to be below ${minTps} TPS`,
        pass: true,
      };
    } else {
      return {
        message: () => `Expected throughput ${received} TPS to meet minimum ${minTps} TPS requirement`,
        pass: false,
      };
    }
  },

  toHaveValidFraudProbability(received: any) {
    const isValid = 
      typeof received === 'object' &&
      typeof received.fraudProbability === 'number' &&
      received.fraudProbability >= 0 &&
      received.fraudProbability <= 1 &&
      ['approve', 'reject', 'review'].includes(received.decision);
    
    if (isValid) {
      return {
        message: () => `Expected fraud analysis to be invalid`,
        pass: true,
      };
    } else {
      return {
        message: () => `Expected valid fraud analysis with fraudProbability (0-1) and decision (approve/reject/review), received: ${JSON.stringify(received)}`,
        pass: false,
      };
    }
  },

  toBeValidAuditEvent(received: any) {
    const requiredFields = ['id', 'timestamp', 'eventType', 'actorId', 'resourceId', 'action', 'details', 'institutionId'];
    const missingFields = requiredFields.filter(field => !received[field]);
    
    const isValid = missingFields.length === 0 && 
                   typeof received.timestamp === 'number' &&
                   received.timestamp > 0;
    
    if (isValid) {
      return {
        message: () => `Expected audit event to be invalid`,
        pass: true,
      };
    } else {
      return {
        message: () => `Expected valid audit event with all required fields. Missing: ${missingFields.join(', ')}`,
        pass: false,
      };
    }
  },

  toHaveSecureHash(received: any) {
    const hasHash = received.hash && typeof received.hash === 'string';
    const isValidLength = hasHash && received.hash.length === 64; // SHA-256 hex length
    const isHexadecimal = hasHash && /^[a-f0-9]+$/i.test(received.hash);
    
    const isValid = hasHash && isValidLength && isHexadecimal;
    
    if (isValid) {
      return {
        message: () => `Expected hash to be invalid`,
        pass: true,
      };
    } else {
      return {
        message: () => `Expected valid SHA-256 hash (64 character hexadecimal string), received: ${received.hash}`,
        pass: false,
      };
    }
  },

  toMeetComplianceRequirements(received: any) {
    const hasRequiredFields = received.complianceStatus && received.violations;
    const validStatus = ['COMPLIANT', 'WARNING', 'VIOLATION'].includes(received.complianceStatus);
    const hasValidViolations = Array.isArray(received.violations);
    
    const isValid = hasRequiredFields && validStatus && hasValidViolations;
    
    if (isValid) {
      return {
        message: () => `Expected compliance report to be invalid`,
        pass: true,
      };
    } else {
      return {
        message: () => `Expected valid compliance report with complianceStatus and violations array`,
        pass: false,
      };
    }
  }
});

// Global test utilities
(global as any).TestUtilities = {
  // Measure execution time of async operations
  async measureLatency<T>(operation: () => Promise<T>): Promise<{ result: T; latency: number }> {
    const start = performance.now();
    const result = await operation();
    const latency = performance.now() - start;
    return { result, latency };
  },

  // Generate test transaction data
  generateTestTransaction(overrides: any = {}) {
    return {
      id: `test_tx_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      amount: 1000,
      currency: 'USD',
      fromAccount: 'ACC_TEST_001',
      toAccount: 'ACC_TEST_002',
      timestamp: Date.now(),
      institutionId: 'BANK_TEST_001',
      ...overrides
    };
  },

  // Generate test audit event data
  generateTestAuditEvent(transactionId: string, institutionId: string = 'BANK_TEST_001') {
    return {
      eventType: 'test_event',
      actorId: 'test_actor',
      resourceId: transactionId,
      action: 'test_action',
      details: {
        testData: true,
        timestamp: Date.now()
      },
      institutionId
    };
  },

  // Wait for a specified number of milliseconds
  async sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  },

  // Retry an operation with exponential backoff
  async retry<T>(
    operation: () => Promise<T>,
    maxAttempts: number = 3,
    baseDelayMs: number = 1000
  ): Promise<T> {
    let lastError: Error;
    
    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
      try {
        return await operation();
      } catch (error) {
        lastError = error as Error;
        
        if (attempt === maxAttempts) {
          throw lastError;
        }
        
        const delay = baseDelayMs * Math.pow(2, attempt - 1);
        console.warn(`Attempt ${attempt} failed, retrying in ${delay}ms:`, error);
        await this.sleep(delay);
      }
    }
    
    throw lastError!;
  }
};

// Configure global test timeouts
jest.setTimeout(60000); // 60 second default timeout

// Global test setup
beforeAll(async () => {
  // Set test environment variables
  process.env.NODE_ENV = 'test';
  process.env.LOG_LEVEL = 'error'; // Reduce log noise during testing
  
  // Clear any existing test data
  console.log('🧹 Setting up test environment...');
});

// Global test teardown
afterAll(async () => {
  // Cleanup any global resources
  console.log('🧹 Cleaning up test environment...');
});

// Performance monitoring for slow tests
const originalTest = test;
global.test = (name: string, fn: any, timeout?: number) => {
  return originalTest(name, async () => {
    const start = performance.now();
    
    try {
      await fn();
    } finally {
      const duration = performance.now() - start;
      
      if (duration > 5000) { // Log slow tests (> 5 seconds)
        console.warn(`⚠️  Slow test detected: "${name}" took ${duration.toFixed(2)}ms`);
      }
    }
  }, timeout);
};

// Enhanced error reporting
process.on('unhandledRejection', (reason, promise) => {
  console.error('Unhandled Rejection at:', promise, 'reason:', reason);
});

process.on('uncaughtException', (error) => {
  console.error('Uncaught Exception:', error);
});

// Test data cleanup helper
export const cleanupTestData = async () => {
  // This function can be called by individual test files to clean up their data
  console.log('🧹 Cleaning up test data...');
  
  // In a real implementation, this would:
  // - Remove test transactions from database
  // - Clear test cache entries
  // - Reset test counters and metrics
  // - Clean up temporary files
};

// Export test utilities for use in test files
export const TestHelpers = {
  generateTestTransaction: (global as any).TestUtilities.generateTestTransaction,
  generateTestAuditEvent: (global as any).TestUtilities.generateTestAuditEvent,
  measureLatency: (global as any).TestUtilities.measureLatency,
  sleep: (global as any).TestUtilities.sleep,
  retry: (global as any).TestUtilities.retry,
  cleanupTestData
};

console.log('✅ Jest test environment configured with financial services testing utilities');
