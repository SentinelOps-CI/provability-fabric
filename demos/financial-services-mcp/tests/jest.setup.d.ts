/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * Jest Test Setup Configuration
 * Global test environment configuration and utilities
 */
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
export declare const cleanupTestData: () => Promise<void>;
export declare const TestHelpers: {
    generateTestTransaction: any;
    generateTestAuditEvent: any;
    measureLatency: any;
    sleep: any;
    retry: any;
    cleanupTestData: () => Promise<void>;
};
//# sourceMappingURL=jest.setup.d.ts.map