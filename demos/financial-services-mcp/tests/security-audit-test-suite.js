/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * Security and Audit Trail Testing Suite
 * Comprehensive security validation and audit integrity testing
 */
import { describe, test, expect, beforeAll, afterAll, beforeEach } from '@jest/globals';
import axios from 'axios';
import { performance } from 'perf_hooks';
import { Pool } from 'pg';
import { createClient } from 'redis';
import { createHash } from 'crypto';
const securityConfig = {
    mcpServerUrl: process.env.MCP_SERVER_URL || 'http://localhost:8080',
    fraudAgentUrl: process.env.FRAUD_AGENT_URL || 'http://localhost:8082',
    auditServiceUrl: process.env.AUDIT_SERVICE_URL || 'http://localhost:8083',
    databaseUrl: process.env.DATABASE_URL || 'postgresql://fintech_user:secure_fintech_2025@localhost:5433/financial_services',
    redisUrl: process.env.REDIS_URL || 'redis://localhost:6380',
    securityTests: {
        maxSqlInjectionAttempts: 50,
        maxXssAttempts: 30,
        maxAuthBypassAttempts: 25,
        maxDataLeakageTests: 20
    },
    auditRequirements: {
        mandatoryFields: ['id', 'timestamp', 'eventType', 'actorId', 'resourceId', 'action', 'details', 'institutionId', 'hash'],
        hashAlgorithm: 'sha256',
        maxChainVerificationTime: 1000, // 1 second
        retentionRequirements: {
            minRetentionDays: 2555, // 7 years
            maxQueryTimeMs: 100
        }
    }
};
class SecurityTestUtilities {
    static dbPool;
    static redisClient;
    static async setupSecurityEnvironment() {
        this.dbPool = new Pool({
            connectionString: securityConfig.databaseUrl,
            max: 10,
            idleTimeoutMillis: 30000,
            connectionTimeoutMillis: 2000,
        });
        this.redisClient = createClient({ url: securityConfig.redisUrl });
        await this.redisClient.connect();
        console.log('🔒 Security test environment initialized');
    }
    static async cleanup() {
        if (this.dbPool) {
            // Clean up test data
            await this.dbPool.query("DELETE FROM audit_events WHERE event_type LIKE '%security_test%'");
            await this.dbPool.query("DELETE FROM transactions WHERE id LIKE 'sec_%'");
            await this.dbPool.end();
        }
        if (this.redisClient) {
            await this.redisClient.quit();
        }
    }
    static generateSqlInjectionPayloads() {
        return [
            "'; DROP TABLE transactions; --",
            "' OR '1'='1",
            "'; INSERT INTO transactions VALUES ('malicious'); --",
            "' UNION SELECT * FROM account_holders --",
            "'; UPDATE transactions SET amount = 999999 WHERE id = '1'; --",
            "' OR 1=1 LIMIT 1 OFFSET 1 --",
            "'; EXEC xp_cmdshell('dir'); --",
            "' AND (SELECT COUNT(*) FROM transactions) > 0 --",
            "'; DECLARE @cmd VARCHAR(255) = 'dir'; EXEC(@cmd); --",
            "' OR SLEEP(5) --"
        ];
    }
    static generateXssPayloads() {
        return [
            "<script>alert('XSS')</script>",
            "javascript:alert('XSS')",
            "<img src=x onerror=alert('XSS')>",
            "<svg onload=alert('XSS')>",
            "'; alert('XSS'); //",
            "<iframe src='javascript:alert(\"XSS\")'></iframe>",
            "<body onload=alert('XSS')>",
            "<input onfocus=alert('XSS') autofocus>",
            "<details open ontoggle=alert('XSS')>",
            "<marquee onstart=alert('XSS')>"
        ];
    }
    static generateMaliciousTransactionData() {
        const sqlPayloads = this.generateSqlInjectionPayloads();
        const xssPayloads = this.generateXssPayloads();
        const maliciousData = [];
        // SQL injection attempts in transaction fields
        for (let i = 0; i < Math.min(10, sqlPayloads.length); i++) {
            maliciousData.push({
                id: `sec_sql_${i}_${Date.now()}`,
                amount: 1000,
                currency: 'USD',
                fromAccount: sqlPayloads[i],
                toAccount: 'ACC_TARGET_001',
                timestamp: Date.now(),
                institutionId: 'BANK_US_001'
            });
        }
        // XSS attempts in transaction metadata
        for (let i = 0; i < Math.min(10, xssPayloads.length); i++) {
            maliciousData.push({
                id: `sec_xss_${i}_${Date.now()}`,
                amount: 1000,
                currency: 'USD',
                fromAccount: 'ACC_SOURCE_001',
                toAccount: 'ACC_TARGET_001',
                timestamp: Date.now(),
                institutionId: 'BANK_US_001',
                metadata: {
                    description: xssPayloads[i],
                    reference: xssPayloads[i]
                }
            });
        }
        // Boundary value attacks
        maliciousData.push({
            id: `sec_boundary_${Date.now()}`,
            amount: Number.MAX_SAFE_INTEGER,
            currency: 'A'.repeat(100), // Overly long currency
            fromAccount: 'A'.repeat(1000), // Overly long account ID
            toAccount: 'ACC_TARGET_001',
            timestamp: Date.now(),
            institutionId: 'BANK_US_001'
        });
        return maliciousData;
    }
    static async testDatabaseDirectAccess() {
        const vulnerabilities = [];
        // Test 1: Try to access data from other institutions
        let canAccessOtherInstitutions = false;
        try {
            const result = await this.dbPool.query(`
        SELECT COUNT(*) as count 
        FROM transactions 
        WHERE institution_id != 'BANK_US_001'
      `);
            if (result.rows[0].count > 0) {
                canAccessOtherInstitutions = true;
                vulnerabilities.push('Can access cross-institutional data without proper isolation');
            }
        }
        catch (error) {
            // Error is expected due to RLS - this is good
        }
        // Test 2: Try to modify audit trail
        let canModifyAuditTrail = false;
        try {
            await this.dbPool.query(`
        UPDATE audit_events 
        SET details = '{"modified": true}' 
        WHERE id = (SELECT id FROM audit_events LIMIT 1)
      `);
            canModifyAuditTrail = true;
            vulnerabilities.push('Can modify audit trail records');
        }
        catch (error) {
            // Error is expected - audit trail should be immutable
        }
        // Test 3: Try to escalate privileges
        let canEscalatePrivileges = false;
        try {
            await this.dbPool.query('CREATE USER malicious_user WITH SUPERUSER');
            canEscalatePrivileges = true;
            vulnerabilities.push('Can escalate database privileges');
        }
        catch (error) {
            // Error is expected - should not be able to create users
        }
        return {
            canAccessOtherInstitutions,
            canModifyAuditTrail,
            canEscalatePrivileges,
            vulnerabilities
        };
    }
    static calculateExpectedHash(event) {
        const data = JSON.stringify({
            id: event.id,
            timestamp: event.timestamp,
            eventType: event.eventType,
            actorId: event.actorId,
            resourceId: event.resourceId,
            action: event.action,
            details: event.details,
            institutionId: event.institutionId,
            previousHash: event.previousHash
        });
        return createHash('sha256').update(data).digest('hex');
    }
}
class AuditTrailValidator {
    dbPool;
    constructor(dbPool) {
        this.dbPool = dbPool;
    }
    async validateAuditChainIntegrity(institutionId) {
        const startTime = performance.now();
        const result = await this.dbPool.query(`
      SELECT id, timestamp, event_type, actor_id, resource_id, action, details, 
             institution_id, hash, previous_hash
      FROM audit_events 
      WHERE institution_id = $1
      ORDER BY timestamp ASC
    `, [institutionId]);
        const events = result.rows;
        let brokenChains = 0;
        let invalidHashes = 0;
        let missingFields = 0;
        let previousHash = null;
        for (const event of events) {
            // Check for missing mandatory fields
            for (const field of securityConfig.auditRequirements.mandatoryFields) {
                if (!event[field.toLowerCase().replace(/([A-Z])/g, '_$1')]) {
                    missingFields++;
                    break;
                }
            }
            // Validate hash chain
            if (previousHash && event.previous_hash !== previousHash) {
                brokenChains++;
            }
            // Validate hash integrity
            const expectedHash = SecurityTestUtilities.calculateExpectedHash(event);
            if (event.hash !== expectedHash) {
                invalidHashes++;
            }
            previousHash = event.hash;
        }
        const performanceMs = performance.now() - startTime;
        const isValid = brokenChains === 0 && invalidHashes === 0 && missingFields === 0;
        return {
            isValid,
            totalEvents: events.length,
            brokenChains,
            invalidHashes,
            missingFields,
            performanceMs
        };
    }
    async validateAuditRetention() {
        const startTime = performance.now();
        const result = await this.dbPool.query(`
      SELECT 
        MIN(timestamp) as oldest_timestamp,
        MAX(timestamp) as newest_timestamp,
        COUNT(*) as total_count
      FROM audit_events
    `);
        const queryPerformanceMs = performance.now() - startTime;
        if (result.rows.length === 0 || !result.rows[0].oldest_timestamp) {
            return {
                meetsRetentionRequirements: false,
                oldestEventDays: 0,
                totalEventCount: 0,
                queryPerformanceMs
            };
        }
        const { oldest_timestamp, total_count } = result.rows[0];
        const oldestEventMs = parseInt(oldest_timestamp);
        const oldestEventDays = (Date.now() - oldestEventMs) / (1000 * 60 * 60 * 24);
        const meetsRetentionRequirements = oldestEventDays <= securityConfig.auditRequirements.retentionRequirements.minRetentionDays;
        return {
            meetsRetentionRequirements: !meetsRetentionRequirements, // If oldest is within retention, we need more data
            oldestEventDays,
            totalEventCount: parseInt(total_count),
            queryPerformanceMs
        };
    }
    async validateAuditImmutability() {
        let attemptedModifications = 0;
        let successfulModifications = 0;
        // Get a sample audit event to attempt modification
        const sampleResult = await this.dbPool.query(`
      SELECT id, hash FROM audit_events LIMIT 1
    `);
        if (sampleResult.rows.length === 0) {
            return {
                isImmutable: true,
                attemptedModifications: 0,
                successfulModifications: 0,
                auditTrailCompromised: false
            };
        }
        const sampleEvent = sampleResult.rows[0];
        const originalHash = sampleEvent.hash;
        // Attempt 1: Direct hash modification
        attemptedModifications++;
        try {
            await this.dbPool.query(`
        UPDATE audit_events 
        SET hash = 'modified_hash_123' 
        WHERE id = $1
      `, [sampleEvent.id]);
            // Check if modification succeeded
            const checkResult = await this.dbPool.query(`
        SELECT hash FROM audit_events WHERE id = $1
      `, [sampleEvent.id]);
            if (checkResult.rows[0].hash !== originalHash) {
                successfulModifications++;
            }
        }
        catch (error) {
            // Expected - should fail
        }
        // Attempt 2: Details modification
        attemptedModifications++;
        try {
            await this.dbPool.query(`
        UPDATE audit_events 
        SET details = '{"tampered": true}' 
        WHERE id = $1
      `, [sampleEvent.id]);
            successfulModifications++;
        }
        catch (error) {
            // Expected - should fail
        }
        // Attempt 3: Deletion
        attemptedModifications++;
        try {
            const deleteResult = await this.dbPool.query(`
        DELETE FROM audit_events WHERE id = $1
      `, [sampleEvent.id]);
            if (deleteResult.rowCount > 0) {
                successfulModifications++;
            }
        }
        catch (error) {
            // Expected - should fail
        }
        return {
            isImmutable: successfulModifications === 0,
            attemptedModifications,
            successfulModifications,
            auditTrailCompromised: successfulModifications > 0
        };
    }
}
// Test suite setup
beforeAll(async () => {
    console.log('🔒 Starting Security and Audit Trail Test Suite');
    await SecurityTestUtilities.setupSecurityEnvironment();
}, 60000);
afterAll(async () => {
    await SecurityTestUtilities.cleanup();
}, 30000);
// Security vulnerability tests
describe('Security Vulnerability Assessment', () => {
    test('SQL injection resistance', async () => {
        console.log('💉 Testing SQL injection resistance');
        const maliciousTransactions = SecurityTestUtilities.generateMaliciousTransactionData();
        const sqlInjectionAttempts = maliciousTransactions.filter(t => t.id.includes('sql'));
        let successfulInjections = 0;
        let blockedAttempts = 0;
        const results = [];
        for (const transaction of sqlInjectionAttempts) {
            try {
                const response = await axios.post(`${securityConfig.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { securityTest: true }
                }, {
                    timeout: 10000,
                    headers: { 'Content-Type': 'application/json' }
                });
                // If we get a normal response, the injection was likely blocked
                if (response.status === 200 && response.data.fraudProbability !== undefined) {
                    blockedAttempts++;
                    results.push({
                        payload: transaction.fromAccount,
                        blocked: true,
                        response: 'Normal fraud analysis response'
                    });
                }
                else {
                    successfulInjections++;
                    results.push({
                        payload: transaction.fromAccount,
                        blocked: false,
                        response: response.data
                    });
                }
            }
            catch (error) {
                // Error responses might indicate injection was blocked or caused system issues
                if (error.response?.status === 400) {
                    blockedAttempts++;
                    results.push({
                        payload: transaction.fromAccount,
                        blocked: true,
                        response: 'Bad request - likely blocked'
                    });
                }
                else {
                    // Unexpected errors could indicate successful injection
                    console.warn(`Unexpected error for payload: ${transaction.fromAccount}`);
                    results.push({
                        payload: transaction.fromAccount,
                        blocked: false,
                        response: error.message
                    });
                }
            }
        }
        console.log(`📊 SQL Injection Test Results:`);
        console.log(`   Attempts: ${sqlInjectionAttempts.length}`);
        console.log(`   Blocked: ${blockedAttempts}`);
        console.log(`   Successful: ${successfulInjections}`);
        // All SQL injection attempts should be blocked
        expect(successfulInjections).toBe(0);
        expect(blockedAttempts).toBe(sqlInjectionAttempts.length);
    }, 60000);
    test('Cross-site scripting (XSS) protection', async () => {
        console.log('🌐 Testing XSS protection');
        const maliciousTransactions = SecurityTestUtilities.generateMaliciousTransactionData();
        const xssAttempts = maliciousTransactions.filter(t => t.id.includes('xss'));
        let sanitizedResponses = 0;
        let unsanitizedResponses = 0;
        for (const transaction of xssAttempts) {
            try {
                const response = await axios.post(`${securityConfig.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { securityTest: true }
                }, {
                    timeout: 10000,
                    headers: { 'Content-Type': 'application/json' }
                });
                // Check if response contains unsanitized script tags
                const responseText = JSON.stringify(response.data);
                if (responseText.includes('<script>') || responseText.includes('javascript:')) {
                    unsanitizedResponses++;
                    console.warn(`Unsanitized XSS payload in response: ${transaction.metadata?.description}`);
                }
                else {
                    sanitizedResponses++;
                }
            }
            catch (error) {
                // Errors are acceptable for XSS attempts
                sanitizedResponses++;
            }
        }
        console.log(`📊 XSS Protection Test Results:`);
        console.log(`   Attempts: ${xssAttempts.length}`);
        console.log(`   Sanitized: ${sanitizedResponses}`);
        console.log(`   Unsanitized: ${unsanitizedResponses}`);
        // All XSS attempts should be sanitized
        expect(unsanitizedResponses).toBe(0);
        expect(sanitizedResponses).toBe(xssAttempts.length);
    }, 60000);
    test('Database access control validation', async () => {
        console.log('🛡️  Testing database access controls');
        const dbSecurityTest = await SecurityTestUtilities.testDatabaseDirectAccess();
        console.log(`📊 Database Security Test Results:`);
        console.log(`   Cross-institutional access: ${dbSecurityTest.canAccessOtherInstitutions ? '❌ VULNERABLE' : '✅ PROTECTED'}`);
        console.log(`   Audit trail modification: ${dbSecurityTest.canModifyAuditTrail ? '❌ VULNERABLE' : '✅ PROTECTED'}`);
        console.log(`   Privilege escalation: ${dbSecurityTest.canEscalatePrivileges ? '❌ VULNERABLE' : '✅ PROTECTED'}`);
        if (dbSecurityTest.vulnerabilities.length > 0) {
            console.log(`⚠️  Vulnerabilities found:`);
            for (const vuln of dbSecurityTest.vulnerabilities) {
                console.log(`     - ${vuln}`);
            }
        }
        // All security controls should be in place
        expect(dbSecurityTest.canAccessOtherInstitutions).toBe(false);
        expect(dbSecurityTest.canModifyAuditTrail).toBe(false);
        expect(dbSecurityTest.canEscalatePrivileges).toBe(false);
        expect(dbSecurityTest.vulnerabilities).toHaveLength(0);
    }, 30000);
    test('Multi-tenant data isolation', async () => {
        console.log('🏦 Testing multi-tenant data isolation');
        const institutions = ['BANK_US_001', 'BANK_UK_001', 'BANK_EU_001'];
        const testTransactions = [];
        // Create test transactions for each institution
        for (const institutionId of institutions) {
            for (let i = 0; i < 5; i++) {
                const transaction = {
                    id: `isolation_test_${institutionId}_${i}_${Date.now()}`,
                    amount: 1000 + i * 100,
                    currency: 'USD',
                    fromAccount: `ACC_${institutionId}_${i}`,
                    toAccount: `ACC_${institutionId}_TARGET`,
                    timestamp: Date.now(),
                    institutionId
                };
                testTransactions.push(transaction);
                // Analyze transaction
                await axios.post(`${securityConfig.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { institutionId }
                }, {
                    headers: {
                        'X-Institution-ID': institutionId,
                        'Content-Type': 'application/json'
                    }
                });
            }
        }
        // Wait for audit events to be created
        await new Promise(resolve => setTimeout(resolve, 2000));
        // Verify data isolation by checking each institution can only access its own data
        const isolationResults = [];
        for (const institutionId of institutions) {
            try {
                // Query audit events for this institution
                const auditResponse = await axios.get(`${securityConfig.auditServiceUrl}/events`, {
                    params: {
                        institutionId,
                        eventType: 'fraud_analysis_completed',
                        limit: 50
                    }
                });
                const events = auditResponse.data.events || [];
                // Check that all returned events belong to this institution
                const foreignEvents = events.filter((event) => event.institutionId !== institutionId);
                isolationResults.push({
                    institutionId,
                    ownEvents: events.filter((event) => event.institutionId === institutionId).length,
                    foreignEvents: foreignEvents.length,
                    isolated: foreignEvents.length === 0
                });
            }
            catch (error) {
                isolationResults.push({
                    institutionId,
                    ownEvents: 0,
                    foreignEvents: 0,
                    isolated: true,
                    error: error.message
                });
            }
        }
        console.log(`📊 Data Isolation Test Results:`);
        for (const result of isolationResults) {
            console.log(`   ${result.institutionId}: ${result.ownEvents} own events, ${result.foreignEvents} foreign events, Isolated: ${result.isolated ? '✅' : '❌'}`);
        }
        // All institutions should have proper data isolation
        for (const result of isolationResults) {
            expect(result.isolated).toBe(true);
            expect(result.foreignEvents).toBe(0);
        }
    }, 60000);
});
// Audit trail integrity tests
describe('Audit Trail Integrity Validation', () => {
    let auditValidator;
    beforeEach(async () => {
        auditValidator = new AuditTrailValidator(SecurityTestUtilities['dbPool']);
    });
    test('Audit chain integrity verification', async () => {
        console.log('🔗 Testing audit chain integrity');
        // Create test transactions to generate audit events
        const testTransactions = [];
        for (let i = 0; i < 10; i++) {
            const transaction = {
                id: `audit_chain_test_${i}_${Date.now()}`,
                amount: 1000 + i * 100,
                currency: 'USD',
                fromAccount: `ACC_CHAIN_${i}`,
                toAccount: 'ACC_CHAIN_TARGET',
                timestamp: Date.now() + i * 1000, // Spread over time
                institutionId: 'BANK_US_001'
            };
            testTransactions.push(transaction);
            // Analyze transaction to create audit events
            await axios.post(`${securityConfig.fraudAgentUrl}/analyze`, {
                transaction,
                options: { createAuditEvent: true }
            });
            // Small delay to ensure proper ordering
            await new Promise(resolve => setTimeout(resolve, 100));
        }
        // Wait for all audit events to be processed
        await new Promise(resolve => setTimeout(resolve, 2000));
        // Validate the audit chain
        const validationResult = await auditValidator.validateAuditChainIntegrity('BANK_US_001');
        console.log(`📊 Audit Chain Validation Results:`);
        console.log(`   Total events: ${validationResult.totalEvents}`);
        console.log(`   Broken chains: ${validationResult.brokenChains}`);
        console.log(`   Invalid hashes: ${validationResult.invalidHashes}`);
        console.log(`   Missing fields: ${validationResult.missingFields}`);
        console.log(`   Validation time: ${validationResult.performanceMs.toFixed(2)}ms`);
        console.log(`   Chain integrity: ${validationResult.isValid ? '✅ VALID' : '❌ INVALID'}`);
        // Audit chain should be valid
        expect(validationResult.isValid).toBe(true);
        expect(validationResult.brokenChains).toBe(0);
        expect(validationResult.invalidHashes).toBe(0);
        expect(validationResult.missingFields).toBe(0);
        // Performance should meet requirements
        expect(validationResult.performanceMs).toBeLessThan(securityConfig.auditRequirements.maxChainVerificationTime);
    }, 60000);
    test('Audit trail immutability enforcement', async () => {
        console.log('🔒 Testing audit trail immutability');
        const immutabilityResult = await auditValidator.validateAuditImmutability();
        console.log(`📊 Audit Immutability Test Results:`);
        console.log(`   Modification attempts: ${immutabilityResult.attemptedModifications}`);
        console.log(`   Successful modifications: ${immutabilityResult.successfulModifications}`);
        console.log(`   Audit trail immutable: ${immutabilityResult.isImmutable ? '✅ YES' : '❌ NO'}`);
        console.log(`   Trail compromised: ${immutabilityResult.auditTrailCompromised ? '❌ YES' : '✅ NO'}`);
        // Audit trail should be immutable
        expect(immutabilityResult.isImmutable).toBe(true);
        expect(immutabilityResult.successfulModifications).toBe(0);
        expect(immutabilityResult.auditTrailCompromised).toBe(false);
    }, 30000);
    test('Audit event completeness validation', async () => {
        console.log('📋 Testing audit event completeness');
        // Create a test transaction
        const transaction = {
            id: `completeness_test_${Date.now()}`,
            amount: 5000,
            currency: 'USD',
            fromAccount: 'ACC_COMPLETENESS_SOURCE',
            toAccount: 'ACC_COMPLETENESS_TARGET',
            timestamp: Date.now(),
            institutionId: 'BANK_US_001'
        };
        // Analyze transaction
        const fraudResponse = await axios.post(`${securityConfig.fraudAgentUrl}/analyze`, {
            transaction,
            options: { createAuditEvent: true }
        });
        expect(fraudResponse.status).toBe(200);
        // Create additional audit event
        const auditResponse = await axios.post(`${securityConfig.auditServiceUrl}/events`, {
            eventType: 'completeness_test',
            actorId: 'test_actor',
            resourceId: transaction.id,
            action: 'completeness_validation',
            details: {
                transactionId: transaction.id,
                fraudProbability: fraudResponse.data.fraudProbability,
                testData: true
            },
            institutionId: transaction.institutionId
        });
        expect(auditResponse.status).toBe(201);
        // Wait for processing
        await new Promise(resolve => setTimeout(resolve, 1000));
        // Query the audit events
        const queryResponse = await axios.get(`${securityConfig.auditServiceUrl}/events`, {
            params: {
                institutionId: transaction.institutionId,
                resourceId: transaction.id,
                limit: 10
            }
        });
        expect(queryResponse.status).toBe(200);
        const events = queryResponse.data.events || [];
        console.log(`📊 Audit Completeness Results:`);
        console.log(`   Events found: ${events.length}`);
        // Validate that all required fields are present
        let completeEvents = 0;
        let incompleteEvents = 0;
        for (const event of events) {
            const hasAllFields = securityConfig.auditRequirements.mandatoryFields.every(field => {
                const dbField = field.toLowerCase().replace(/([A-Z])/g, '_$1');
                return event[dbField] !== undefined && event[dbField] !== null;
            });
            if (hasAllFields) {
                completeEvents++;
            }
            else {
                incompleteEvents++;
                console.warn(`Incomplete event found: ${event.id}`);
            }
        }
        console.log(`   Complete events: ${completeEvents}`);
        console.log(`   Incomplete events: ${incompleteEvents}`);
        // All events should be complete
        expect(events.length).toBeGreaterThan(0);
        expect(incompleteEvents).toBe(0);
        expect(completeEvents).toBe(events.length);
    }, 30000);
    test('Audit performance under load', async () => {
        console.log('⚡ Testing audit performance under load');
        const eventCount = 100;
        const startTime = performance.now();
        const eventPromises = [];
        // Create multiple audit events concurrently
        for (let i = 0; i < eventCount; i++) {
            const eventPromise = axios.post(`${securityConfig.auditServiceUrl}/events`, {
                eventType: 'performance_test',
                actorId: `test_actor_${i}`,
                resourceId: `resource_${i}`,
                action: 'performance_validation',
                details: {
                    batchId: Math.floor(i / 10),
                    index: i,
                    timestamp: Date.now(),
                    testData: true
                },
                institutionId: 'BANK_US_001'
            });
            eventPromises.push(eventPromise);
        }
        // Wait for all events to complete
        const results = await Promise.allSettled(eventPromises);
        const createTime = performance.now() - startTime;
        const successfulCreations = results.filter(r => r.status === 'fulfilled').length;
        const failedCreations = results.filter(r => r.status === 'rejected').length;
        console.log(`📊 Audit Performance Results:`);
        console.log(`   Events created: ${successfulCreations}/${eventCount}`);
        console.log(`   Failed creations: ${failedCreations}`);
        console.log(`   Total time: ${createTime.toFixed(2)}ms`);
        console.log(`   Average time per event: ${(createTime / eventCount).toFixed(2)}ms`);
        console.log(`   Events per second: ${((eventCount / createTime) * 1000).toFixed(0)}`);
        // Performance requirements
        const avgTimePerEvent = createTime / eventCount;
        expect(successfulCreations).toBeGreaterThan(eventCount * 0.95); // 95% success rate
        expect(avgTimePerEvent).toBeLessThan(10); // Less than 10ms per event on average
        // Wait for processing
        await new Promise(resolve => setTimeout(resolve, 2000));
        // Verify audit chain integrity after bulk operations
        const validationResult = await auditValidator.validateAuditChainIntegrity('BANK_US_001');
        expect(validationResult.isValid).toBe(true);
    }, 60000);
});
export default {};
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2VjdXJpdHktYXVkaXQtdGVzdC1zdWl0ZS5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbInNlY3VyaXR5LWF1ZGl0LXRlc3Qtc3VpdGUudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUE7Ozs7OztHQU1HO0FBRUgsT0FBTyxFQUFFLFFBQVEsRUFBRSxJQUFJLEVBQUUsTUFBTSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFFLE1BQU0sZUFBZSxDQUFDO0FBQ3hGLE9BQU8sS0FBSyxNQUFNLE9BQU8sQ0FBQztBQUMxQixPQUFPLEVBQUUsV0FBVyxFQUFFLE1BQU0sWUFBWSxDQUFDO0FBQ3pDLE9BQU8sRUFBRSxJQUFJLEVBQUUsTUFBTSxJQUFJLENBQUM7QUFDMUIsT0FBTyxFQUFFLFlBQVksRUFBRSxNQUFNLE9BQU8sQ0FBQztBQUNyQyxPQUFPLEVBQUUsVUFBVSxFQUFlLE1BQU0sUUFBUSxDQUFDO0FBeUJqRCxNQUFNLGNBQWMsR0FBdUI7SUFDekMsWUFBWSxFQUFFLE9BQU8sQ0FBQyxHQUFHLENBQUMsY0FBYyxJQUFJLHVCQUF1QjtJQUNuRSxhQUFhLEVBQUUsT0FBTyxDQUFDLEdBQUcsQ0FBQyxlQUFlLElBQUksdUJBQXVCO0lBQ3JFLGVBQWUsRUFBRSxPQUFPLENBQUMsR0FBRyxDQUFDLGlCQUFpQixJQUFJLHVCQUF1QjtJQUN6RSxXQUFXLEVBQUUsT0FBTyxDQUFDLEdBQUcsQ0FBQyxZQUFZLElBQUksaUZBQWlGO0lBQzFILFFBQVEsRUFBRSxPQUFPLENBQUMsR0FBRyxDQUFDLFNBQVMsSUFBSSx3QkFBd0I7SUFDM0QsYUFBYSxFQUFFO1FBQ2IsdUJBQXVCLEVBQUUsRUFBRTtRQUMzQixjQUFjLEVBQUUsRUFBRTtRQUNsQixxQkFBcUIsRUFBRSxFQUFFO1FBQ3pCLG1CQUFtQixFQUFFLEVBQUU7S0FDeEI7SUFDRCxpQkFBaUIsRUFBRTtRQUNqQixlQUFlLEVBQUUsQ0FBQyxJQUFJLEVBQUUsV0FBVyxFQUFFLFdBQVcsRUFB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