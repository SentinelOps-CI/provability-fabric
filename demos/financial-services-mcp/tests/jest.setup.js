/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * Jest Test Setup Configuration
 * Global test environment configuration and utilities
 */
import { performance } from 'perf_hooks';
// Custom Jest matchers for financial services testing
expect.extend({
    toBeWithinLatencyThreshold(received, maxLatencyMs) {
        const pass = received <= maxLatencyMs;
        if (pass) {
            return {
                message: () => `Expected latency ${received}ms to exceed ${maxLatencyMs}ms`,
                pass: true,
            };
        }
        else {
            return {
                message: () => `Expected latency ${received}ms to be within ${maxLatencyMs}ms threshold`,
                pass: false,
            };
        }
    },
    toMeetThroughputRequirement(received, minTps) {
        const pass = received >= minTps;
        if (pass) {
            return {
                message: () => `Expected throughput ${received} TPS to be below ${minTps} TPS`,
                pass: true,
            };
        }
        else {
            return {
                message: () => `Expected throughput ${received} TPS to meet minimum ${minTps} TPS requirement`,
                pass: false,
            };
        }
    },
    toHaveValidFraudProbability(received) {
        const isValid = typeof received === 'object' &&
            typeof received.fraudProbability === 'number' &&
            received.fraudProbability >= 0 &&
            received.fraudProbability <= 1 &&
            ['approve', 'reject', 'review'].includes(received.decision);
        if (isValid) {
            return {
                message: () => `Expected fraud analysis to be invalid`,
                pass: true,
            };
        }
        else {
            return {
                message: () => `Expected valid fraud analysis with fraudProbability (0-1) and decision (approve/reject/review), received: ${JSON.stringify(received)}`,
                pass: false,
            };
        }
    },
    toBeValidAuditEvent(received) {
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
        }
        else {
            return {
                message: () => `Expected valid audit event with all required fields. Missing: ${missingFields.join(', ')}`,
                pass: false,
            };
        }
    },
    toHaveSecureHash(received) {
        const hasHash = received.hash && typeof received.hash === 'string';
        const isValidLength = hasHash && received.hash.length === 64; // SHA-256 hex length
        const isHexadecimal = hasHash && /^[a-f0-9]+$/i.test(received.hash);
        const isValid = hasHash && isValidLength && isHexadecimal;
        if (isValid) {
            return {
                message: () => `Expected hash to be invalid`,
                pass: true,
            };
        }
        else {
            return {
                message: () => `Expected valid SHA-256 hash (64 character hexadecimal string), received: ${received.hash}`,
                pass: false,
            };
        }
    },
    toMeetComplianceRequirements(received) {
        const hasRequiredFields = received.complianceStatus && received.violations;
        const validStatus = ['COMPLIANT', 'WARNING', 'VIOLATION'].includes(received.complianceStatus);
        const hasValidViolations = Array.isArray(received.violations);
        const isValid = hasRequiredFields && validStatus && hasValidViolations;
        if (isValid) {
            return {
                message: () => `Expected compliance report to be invalid`,
                pass: true,
            };
        }
        else {
            return {
                message: () => `Expected valid compliance report with complianceStatus and violations array`,
                pass: false,
            };
        }
    }
});
// Global test utilities
global.TestUtilities = {
    // Measure execution time of async operations
    async measureLatency(operation) {
        const start = performance.now();
        const result = await operation();
        const latency = performance.now() - start;
        return { result, latency };
    },
    // Generate test transaction data
    generateTestTransaction(overrides = {}) {
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
    generateTestAuditEvent(transactionId, institutionId = 'BANK_TEST_001') {
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
    async sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    },
    // Retry an operation with exponential backoff
    async retry(operation, maxAttempts = 3, baseDelayMs = 1000) {
        let lastError;
        for (let attempt = 1; attempt <= maxAttempts; attempt++) {
            try {
                return await operation();
            }
            catch (error) {
                lastError = error;
                if (attempt === maxAttempts) {
                    throw lastError;
                }
                const delay = baseDelayMs * Math.pow(2, attempt - 1);
                console.warn(`Attempt ${attempt} failed, retrying in ${delay}ms:`, error);
                await this.sleep(delay);
            }
        }
        throw lastError;
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
global.test = (name, fn, timeout) => {
    return originalTest(name, async () => {
        const start = performance.now();
        try {
            await fn();
        }
        finally {
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
    generateTestTransaction: global.TestUtilities.generateTestTransaction,
    generateTestAuditEvent: global.TestUtilities.generateTestAuditEvent,
    measureLatency: global.TestUtilities.measureLatency,
    sleep: global.TestUtilities.sleep,
    retry: global.TestUtilities.retry,
    cleanupTestData
};
console.log('✅ Jest test environment configured with financial services testing utilities');
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiamVzdC5zZXR1cC5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbImplc3Quc2V0dXAudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUE7Ozs7OztHQU1HO0FBRUgsT0FBTyxFQUFFLFdBQVcsRUFBRSxNQUFNLFlBQVksQ0FBQztBQWdCekMsc0RBQXNEO0FBQ3RELE1BQU0sQ0FBQyxNQUFNLENBQUM7SUFDWiwwQkFBMEIsQ0FBQyxRQUFnQixFQUFFLFlBQW9CO1FBQy9ELE1BQU0sSUFBSSxHQUFHLFFBQVEsSUFBSSxZQUFZLENBQUM7UUFFdEMsSUFBSSxJQUFJLEVBQUUsQ0FBQztZQUNULE9BQU87Z0JBQ0wsT0FBTyxFQUFFLEdBQUcsRUFBRSxDQUFDLG9CQUFvQixRQUFRLGdCQUFnQixZQUFZLElBQUk7Z0JBQzNFLElBQUksRUFBRSxJQUFJO2FBQ1gsQ0FBQztRQUNKLENBQUM7YUFBTSxDQUFDO1lBQ04sT0FBTztnQkFDTCxPQUFPLEVBQUUsR0FBRyxFQUFFLENBQUMsb0JBQW9CLFFBQVEsbUJBQW1CLFlBQVksY0FBYztnQkFDeEYsSUFBSSxFQUFFLEtBQUs7YUFDWixDQUFDO1FBQ0osQ0FBQztJQUNILENBQUM7SUFFRCwyQkFBMkIsQ0FBQyxRQUFnQixFQUFFLE1BQWM7UUFDMUQsTUFBTSxJQUFJLEdBQUcsUUFBUSxJQUFJLE1BQU0sQ0FBQztRQUVoQyxJQUFJLElBQUksRUFBRSxDQUFDO1lBQ1QsT0FBTztnQkFDTCxPQUFPLEVBQUUsR0FBRyxFQUFFLENBQUMsdUJBQXVCLFFBQVEsb0JBQW9CLE1BQU0sTUFBTTtnQkFDOUUsSUFBSSxFQUFFLElBQUk7YUFDWCxDQUFDO1FBQ0osQ0FBQzthQUFNLENBQUM7WUFDTixPQUFPO2dCQUNMLE9BQU8sRUFBRSxHQUFHLEVBQUUsQ0FBQyx1QkFBdUIsUUFBUSx3QkFBd0IsTUFBTSxrQkFBa0I7Z0JBQzlGLElBQUksRUFBRSxLQUFLO2FBQ1osQ0FBQztRQUNKLENBQUM7SUFDSCxDQUFDO0lBRUQsMkJBQTJC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