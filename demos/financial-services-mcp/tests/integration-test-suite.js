/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * End-to-End Integration Testing Suite
 * Comprehensive testing for Financial Services MCP implementation
 */
import { describe, test, expect, beforeAll, afterAll, beforeEach } from '@jest/globals';
import axios from 'axios';
import WebSocket from 'ws';
import { performance } from 'perf_hooks';
import { Pool } from 'pg';
import { createClient } from 'redis';
const config = {
    mcpServerUrl: process.env.MCP_SERVER_URL || 'http://localhost:8080',
    fraudAgentUrl: process.env.FRAUD_AGENT_URL || 'http://localhost:8082',
    auditServiceUrl: process.env.AUDIT_SERVICE_URL || 'http://localhost:8083',
    dashboardUrl: process.env.DASHBOARD_URL || 'http://localhost:3001',
    databaseUrl: process.env.DATABASE_URL || 'postgresql://fintech_user:secure_fintech_2025@localhost:5433/financial_services',
    redisUrl: process.env.REDIS_URL || 'redis://localhost:6380',
    testTimeout: 30000, // 30 seconds
    performanceThresholds: {
        maxLatencyMs: 5.0,
        minThroughputTps: 1000,
        minAccuracy: 0.95,
        minAvailability: 99.9
    }
};
// Test data generators
class TestDataGenerator {
    static generateTransaction(institutionId = 'BANK_US_001') {
        return {
            id: `test_tx_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
            amount: Math.random() * 10000 + 100,
            currency: 'USD',
            fromAccount: `ACC_${institutionId}_${Math.floor(Math.random() * 1000)}`,
            toAccount: `ACC_${institutionId}_${Math.floor(Math.random() * 1000)}`,
            timestamp: Date.now(),
            institutionId
        };
    }
    static generateFraudulentTransaction(institutionId = 'BANK_US_001') {
        return {
            id: `fraud_tx_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
            amount: Math.random() * 50000 + 10000, // Higher amounts
            currency: 'USD',
            fromAccount: `ACC_${institutionId}_suspicious`,
            toAccount: `ACC_UNKNOWN_${Math.floor(Math.random() * 100)}`,
            timestamp: Date.now() - Math.random() * 60000, // Random time in last minute
            institutionId,
            metadata: {
                suspicious: true,
                testFraud: true
            }
        };
    }
    static generateAuditEvent(transactionId, institutionId) {
        return {
            eventType: 'integration_test',
            actorId: 'test_system',
            resourceId: transactionId,
            action: 'test_transaction',
            details: {
                testRun: true,
                timestamp: Date.now(),
                testId: Math.random().toString(36).substr(2, 9)
            },
            institutionId
        };
    }
    static generateBatchTransactions(count, institutionId = 'BANK_US_001') {
        const transactions = [];
        for (let i = 0; i < count; i++) {
            transactions.push(this.generateTransaction(institutionId));
        }
        return transactions;
    }
}
// Test utilities
class TestUtilities {
    static dbPool;
    static redisClient;
    static async setupDatabase() {
        this.dbPool = new Pool({
            connectionString: config.databaseUrl,
            max: 5
        });
        // Test database connectivity
        await this.dbPool.query('SELECT 1');
    }
    static async setupRedis() {
        this.redisClient = createClient({ url: config.redisUrl });
        await this.redisClient.connect();
    }
    static async cleanup() {
        // Clean up test data
        if (this.dbPool) {
            await this.dbPool.query("DELETE FROM audit_events WHERE event_type = 'integration_test'");
            await this.dbPool.query("DELETE FROM transactions WHERE id LIKE 'test_tx_%' OR id LIKE 'fraud_tx_%'");
            await this.dbPool.end();
        }
        if (this.redisClient) {
            await this.redisClient.flushDb();
            await this.redisClient.quit();
        }
    }
    static async waitForServices() {
        const services = [
            { name: 'MCP Server', url: `${config.mcpServerUrl}/health` },
            { name: 'Fraud Agent', url: `${config.fraudAgentUrl}/health` },
            { name: 'Audit Service', url: `${config.auditServiceUrl}/health` },
            { name: 'Dashboard', url: `${config.dashboardUrl}/health` }
        ];
        const maxRetries = 30;
        const retryDelay = 2000;
        for (const service of services) {
            let retries = 0;
            while (retries < maxRetries) {
                try {
                    const response = await axios.get(service.url, { timeout: 5000 });
                    if (response.status === 200) {
                        console.log(`✅ ${service.name} is ready`);
                        break;
                    }
                }
                catch (error) {
                    retries++;
                    if (retries === maxRetries) {
                        throw new Error(`❌ ${service.name} failed to start after ${maxRetries} retries`);
                    }
                    console.log(`⏳ Waiting for ${service.name}... (${retries}/${maxRetries})`);
                    await new Promise(resolve => setTimeout(resolve, retryDelay));
                }
            }
        }
    }
    static async measureLatency(operation) {
        const start = performance.now();
        const result = await operation();
        const latency = performance.now() - start;
        return { result, latency };
    }
    static async measureThroughput(operationFactory, count, maxConcurrency = 50) {
        const start = performance.now();
        const results = [];
        // Execute operations in batches to control concurrency
        for (let i = 0; i < count; i += maxConcurrency) {
            const batch = [];
            const batchEnd = Math.min(i + maxConcurrency, count);
            for (let j = i; j < batchEnd; j++) {
                batch.push(operationFactory(j));
            }
            const batchResults = await Promise.allSettled(batch);
            results.push(...batchResults
                .filter(r => r.status === 'fulfilled')
                .map(r => r.value));
        }
        const duration = (performance.now() - start) / 1000; // Convert to seconds
        const throughput = results.length / duration;
        const avgLatency = (performance.now() - start) / results.length;
        return { results, throughput, avgLatency };
    }
}
// Test suite setup
beforeAll(async () => {
    console.log('🚀 Starting Financial Services MCP Integration Tests');
    await TestUtilities.setupDatabase();
    await TestUtilities.setupRedis();
    await TestUtilities.waitForServices();
    console.log('✅ Test environment ready');
}, 120000); // 2 minute timeout for setup
afterAll(async () => {
    console.log('🧹 Cleaning up test environment');
    await TestUtilities.cleanup();
}, 30000);
// Health and connectivity tests
describe('Service Health Checks', () => {
    test('All services are healthy', async () => {
        const services = [
            { name: 'MCP Server', url: `${config.mcpServerUrl}/health` },
            { name: 'Fraud Agent', url: `${config.fraudAgentUrl}/health` },
            { name: 'Audit Service', url: `${config.auditServiceUrl}/health` },
            { name: 'Dashboard', url: `${config.dashboardUrl}/health` }
        ];
        for (const service of services) {
            const response = await axios.get(service.url);
            expect(response.status).toBe(200);
            expect(response.data).toHaveProperty('status', 'healthy');
        }
    }, config.testTimeout);
    test('Database connectivity', async () => {
        const result = await TestUtilities['dbPool'].query('SELECT NOW() as current_time');
        expect(result.rows).toHaveLength(1);
        expect(result.rows[0]).toHaveProperty('current_time');
    });
    test('Redis connectivity', async () => {
        await TestUtilities['redisClient'].set('test_key', 'test_value');
        const value = await TestUtilities['redisClient'].get('test_key');
        expect(value).toBe('test_value');
    });
});
// MCP Server integration tests
describe('MCP Server Integration', () => {
    let mcpClient;
    beforeEach(() => {
        mcpClient = axios.create({
            baseURL: config.mcpServerUrl,
            timeout: 10000,
            headers: { 'Content-Type': 'application/json' }
        });
    });
    test('MCP server tools listing', async () => {
        const response = await mcpClient.post('/mcp/jsonrpc', {
            jsonrpc: '2.0',
            method: 'tools/list',
            id: 1
        });
        expect(response.status).toBe(200);
        expect(response.data).toHaveProperty('result');
        expect(response.data.result).toHaveProperty('tools');
        expect(Array.isArray(response.data.result.tools)).toBe(true);
        expect(response.data.result.tools.length).toBeGreaterThan(0);
        const toolNames = response.data.result.tools.map((tool) => tool.name);
        expect(toolNames).toContain('analyze_transaction');
        expect(toolNames).toContain('query_transaction_history');
        expect(toolNames).toContain('create_audit_event');
    });
    test('Transaction analysis tool call', async () => {
        const transaction = TestDataGenerator.generateTransaction();
        const { result, latency } = await TestUtilities.measureLatency(async () => {
            return await mcpClient.post('/mcp/jsonrpc', {
                jsonrpc: '2.0',
                method: 'tools/call',
                params: {
                    name: 'analyze_transaction',
                    arguments: {
                        transaction,
                        options: { performanceMode: 'realtime' }
                    }
                },
                id: 2
            });
        });
        expect(result.status).toBe(200);
        expect(result.data).toHaveProperty('result');
        expect(latency).toBeLessThan(config.performanceThresholds.maxLatencyMs);
        const analysisResult = JSON.parse(result.data.result.content[0].text);
        expect(analysisResult).toHaveProperty('transactionId', transaction.id);
        expect(analysisResult).toHaveProperty('fraudProbability');
        expect(analysisResult).toHaveProperty('decision');
        expect(analysisResult.fraudProbability).toBeGreaterThanOrEqual(0);
        expect(analysisResult.fraudProbability).toBeLessThanOrEqual(1);
        expect(['approve', 'reject', 'review']).toContain(analysisResult.decision);
    });
    test('Query transaction history tool call', async () => {
        const { result, latency } = await TestUtilities.measureLatency(async () => {
            return await mcpClient.post('/mcp/jsonrpc', {
                jsonrpc: '2.0',
                method: 'tools/call',
                params: {
                    name: 'query_transaction_history',
                    arguments: {
                        accountId: 'ACC_US_001_123',
                        timeRange: {
                            start: Date.now() - 3600000, // 1 hour ago
                            end: Date.now()
                        },
                        institutionId: 'BANK_US_001',
                        limit: 50
                    }
                },
                id: 3
            });
        });
        expect(result.status).toBe(200);
        expect(result.data).toHaveProperty('result');
        expect(latency).toBeLessThan(config.performanceThresholds.maxLatencyMs);
        const historyResult = JSON.parse(result.data.result.content[0].text);
        expect(historyResult).toHaveProperty('transactions');
        expect(Array.isArray(historyResult.transactions)).toBe(true);
    });
    test('MCP resources listing', async () => {
        const response = await mcpClient.post('/mcp/jsonrpc', {
            jsonrpc: '2.0',
            method: 'resources/list',
            id: 4
        });
        expect(response.status).toBe(200);
        expect(response.data).toHaveProperty('result');
        expect(response.data.result).toHaveProperty('resources');
        expect(Array.isArray(response.data.result.resources)).toBe(true);
        const resourceUris = response.data.result.resources.map((resource) => resource.uri);
        expect(resourceUris).toContain('financial://transactions/realtime');
        expect(resourceUris).toContain('financial://audit/blockchain');
    });
});
// Fraud Detection Agent integration tests
describe('Fraud Detection Agent Integration', () => {
    let fraudClient;
    beforeEach(() => {
        fraudClient = axios.create({
            baseURL: config.fraudAgentUrl,
            timeout: 10000,
            headers: { 'Content-Type': 'application/json' }
        });
    });
    test('Single transaction fraud analysis', async () => {
        const transaction = TestDataGenerator.generateTransaction();
        const { result, latency } = await TestUtilities.measureLatency(async () => {
            return await fraudClient.post('/analyze', {
                transaction,
                options: { performanceMode: 'realtime', includeReasons: true }
            });
        });
        expect(result.status).toBe(200);
        expect(latency).toBeLessThan(config.performanceThresholds.maxLatencyMs);
        const analysis = result.data;
        expect(analysis).toHaveProperty('transactionId', transaction.id);
        expect(analysis).toHaveProperty('fraudProbability');
        expect(analysis).toHaveProperty('confidence');
        expect(analysis).toHaveProperty('decision');
        expect(analysis).toHaveProperty('riskFactors');
        expect(analysis).toHaveProperty('processingTimeMs');
        expect(analysis.fraudProbability).toBeGreaterThanOrEqual(0);
        expect(analysis.fraudProbability).toBeLessThanOrEqual(1);
        expect(analysis.confidence).toBeGreaterThanOrEqual(0);
        expect(analysis.confidence).toBeLessThanOrEqual(1);
        expect(['approve', 'reject', 'review']).toContain(analysis.decision);
        expect(Array.isArray(analysis.riskFactors)).toBe(true);
    });
    test('Fraudulent transaction detection', async () => {
        const fraudulentTransaction = TestDataGenerator.generateFraudulentTransaction();
        const response = await fraudClient.post('/analyze', {
            transaction: fraudulentTransaction,
            options: { performanceMode: 'realtime' }
        });
        expect(response.status).toBe(200);
        const analysis = response.data;
        // Fraudulent transactions should have higher fraud probability
        expect(analysis.fraudProbability).toBeGreaterThan(0.1);
        expect(analysis.riskFactors.length).toBeGreaterThan(0);
    });
    test('Batch transaction analysis', async () => {
        const transactions = TestDataGenerator.generateBatchTransactions(10);
        const { result, latency } = await TestUtilities.measureLatency(async () => {
            return await fraudClient.post('/analyze/batch', {
                transactions,
                options: { performanceMode: 'realtime' }
            });
        });
        expect(result.status).toBe(200);
        expect(latency).toBeLessThan(config.performanceThresholds.maxLatencyMs * 2); // Allow more time for batch
        const batchResult = result.data;
        expect(batchResult).toHaveProperty('results');
        expect(batchResult).toHaveProperty('batchSize', 10);
        expect(Array.isArray(batchResult.results)).toBe(true);
        expect(batchResult.results).toHaveLength(10);
        // Validate each result
        for (const analysis of batchResult.results) {
            expect(analysis).toHaveProperty('fraudProbability');
            expect(analysis).toHaveProperty('decision');
            expect(analysis.fraudProbability).toBeGreaterThanOrEqual(0);
            expect(analysis.fraudProbability).toBeLessThanOrEqual(1);
        }
    });
    test('Pattern learning endpoint', async () => {
        const transactions = TestDataGenerator.generateBatchTransactions(5);
        const labels = [false, false, true, false, true]; // Mix of fraud and legitimate
        const response = await fraudClient.post('/learn', {
            transactions,
            labels
        });
        expect(response.status).toBe(200);
        expect(response.data).toHaveProperty('message');
        expect(response.data).toHaveProperty('samplesProcessed', 5);
    });
    test('Performance metrics endpoint', async () => {
        const response = await fraudClient.get('/metrics');
        expect(response.status).toBe(200);
        expect(response.data).toHaveProperty('performance');
        expect(response.data).toHaveProperty('timestamp');
        const metrics = response.data.performance;
        if (Object.keys(metrics).length > 0) {
            // Check that metrics have proper structure
            const sampleMetric = Object.values(metrics)[0];
            expect(sampleMetric).toHaveProperty('count');
            expect(sampleMetric).toHaveProperty('min');
            expect(sampleMetric).toHaveProperty('max');
            expect(sampleMetric).toHaveProperty('p95');
            expect(sampleMetric).toHaveProperty('p99');
        }
    });
});
// Audit Trail Service integration tests
describe('Audit Trail Service Integration', () => {
    let auditClient;
    beforeEach(() => {
        auditClient = axios.create({
            baseURL: config.auditServiceUrl,
            timeout: 10000,
            headers: { 'Content-Type': 'application/json' }
        });
    });
    test('Single audit event creation', async () => {
        const transaction = TestDataGenerator.generateTransaction();
        const auditEvent = TestDataGenerator.generateAuditEvent(transaction.id, transaction.institutionId);
        const { result, latency } = await TestUtilities.measureLatency(async () => {
            return await auditClient.post('/events', auditEvent);
        });
        expect(result.status).toBe(201);
        expect(latency).toBeLessThan(config.performanceThresholds.maxLatencyMs);
        const response = result.data;
        expect(response).toHaveProperty('eventId');
        expect(response).toHaveProperty('hash');
        expect(response).toHaveProperty('timestamp');
        expect(response).toHaveProperty('status', 'created');
    });
    test('Batch audit events creation', async () => {
        const events = [];
        for (let i = 0; i < 5; i++) {
            const transaction = TestDataGenerator.generateTransaction();
            events.push(TestDataGenerator.generateAuditEvent(transaction.id, transaction.institutionId));
        }
        const { result, latency } = await TestUtilities.measureLatency(async () => {
            return await auditClient.post('/events/batch', { events });
        });
        expect(result.status).toBe(201);
        expect(latency).toBeLessThan(config.performanceThresholds.maxLatencyMs * 2);
        const response = result.data;
        expect(response).toHaveProperty('batchId');
        expect(response).toHaveProperty('eventsCreated', 5);
        expect(response).toHaveProperty('results');
        expect(Array.isArray(response.results)).toBe(true);
        expect(response.results).toHaveLength(5);
    });
    test('Audit events query', async () => {
        // First, create some test events
        const testEvents = [];
        for (let i = 0; i < 3; i++) {
            const transaction = TestDataGenerator.generateTransaction();
            const event = TestDataGenerator.generateAuditEvent(transaction.id, transaction.institutionId);
            await auditClient.post('/events', event);
            testEvents.push(event);
        }
        // Wait a bit for events to be stored
        await new Promise(resolve => setTimeout(resolve, 1000));
        const response = await auditClient.get('/events', {
            params: {
                institutionId: 'BANK_US_001',
                eventType: 'integration_test',
                limit: 10
            }
        });
        expect(response.status).toBe(200);
        expect(response.data).toHaveProperty('events');
        expect(response.data).toHaveProperty('count');
        expect(Array.isArray(response.data.events)).toBe(true);
        expect(response.data.events.length).toBeGreaterThanOrEqual(3);
    });
    test('Audit trail integrity verification', async () => {
        // Create a test event first
        const transaction = TestDataGenerator.generateTransaction();
        const auditEvent = TestDataGenerator.generateAuditEvent(transaction.id, transaction.institutionId);
        const createResponse = await auditClient.post('/events', auditEvent);
        // Wait for processing
        await new Promise(resolve => setTimeout(resolve, 2000));
        const response = await auditClient.post('/verify', {
            institutionId: transaction.institutionId,
            startTime: Date.now() - 60000, // Last minute
            endTime: Date.now()
        });
        expect(response.status).toBe(200);
        const verification = response.data;
        expect(verification).toHaveProperty('isValid');
        expect(verification).toHaveProperty('eventCount');
        expect(verification).toHaveProperty('verifiedAt');
        expect(verification).toHaveProperty('verificationTimeMs');
        expect(verification.isValid).toBe(true);
        expect(verification.eventCount).toBeGreaterThanOrEqual(1);
    });
    test('Compliance report generation', async () => {
        const response = await auditClient.post('/compliance/report', {
            institutionId: 'BANK_US_001',
            reportType: 'SOX_COMPLIANCE',
            periodStart: Date.now() - 3600000, // 1 hour ago
            periodEnd: Date.now()
        });
        expect(response.status).toBe(200);
        const report = response.data;
        expect(report).toHaveProperty('reportId');
        expect(report).toHaveProperty('institutionId', 'BANK_US_001');
        expect(report).toHaveProperty('reportType', 'SOX_COMPLIANCE');
        expect(report).toHaveProperty('complianceStatus');
        expect(report).toHaveProperty('violations');
        expect(report).toHaveProperty('hash');
        expect(['COMPLIANT', 'WARNING', 'VIOLATION']).toContain(report.complianceStatus);
        expect(Array.isArray(report.violations)).toBe(true);
    });
});
// End-to-end workflow tests
describe('End-to-End Workflow Integration', () => {
    test('Complete transaction processing pipeline', async () => {
        const transaction = TestDataGenerator.generateTransaction();
        console.log(`Testing complete pipeline for transaction: ${transaction.id}`);
        // Step 1: Analyze transaction for fraud
        const fraudAnalysis = await axios.post(`${config.fraudAgentUrl}/analyze`, {
            transaction,
            options: { performanceMode: 'realtime' }
        });
        expect(fraudAnalysis.status).toBe(200);
        const analysisResult = fraudAnalysis.data;
        // Step 2: Create audit event for the analysis
        const auditEvent = {
            eventType: 'fraud_analysis_completed',
            actorId: 'fraud_agent',
            resourceId: transaction.id,
            action: 'analyze_transaction',
            details: {
                fraudProbability: analysisResult.fraudProbability,
                decision: analysisResult.decision,
                testRun: true
            },
            institutionId: transaction.institutionId
        };
        const auditResponse = await axios.post(`${config.auditServiceUrl}/events`, auditEvent);
        expect(auditResponse.status).toBe(201);
        // Step 3: Query MCP server for transaction context
        const mcpResponse = await axios.post(`${config.mcpServerUrl}/mcp/jsonrpc`, {
            jsonrpc: '2.0',
            method: 'tools/call',
            params: {
                name: 'query_transaction_history',
                arguments: {
                    accountId: transaction.fromAccount,
                    timeRange: {
                        start: Date.now() - 3600000,
                        end: Date.now()
                    },
                    institutionId: transaction.institutionId
                }
            },
            id: 1
        });
        expect(mcpResponse.status).toBe(200);
        // Step 4: Verify audit trail integrity
        await new Promise(resolve => setTimeout(resolve, 2000)); // Wait for processing
        const verificationResponse = await axios.post(`${config.auditServiceUrl}/verify`, {
            institutionId: transaction.institutionId,
            startTime: Date.now() - 60000,
            endTime: Date.now()
        });
        expect(verificationResponse.status).toBe(200);
        expect(verificationResponse.data.isValid).toBe(true);
        console.log(`✅ Complete pipeline test passed for transaction: ${transaction.id}`);
    }, 30000);
    test('Multi-tenant transaction isolation', async () => {
        const institutions = ['BANK_US_001', 'BANK_UK_001', 'BANK_EU_001'];
        const transactions = institutions.map(inst => TestDataGenerator.generateTransaction(inst));
        // Process transactions for different institutions
        const analysisPromises = transactions.map(transaction => axios.post(`${config.fraudAgentUrl}/analyze`, {
            transaction,
            options: { institutionId: transaction.institutionId }
        }, {
            headers: { 'X-Institution-ID': transaction.institutionId }
        }));
        const analyses = await Promise.all(analysisPromises);
        // All should succeed
        analyses.forEach(analysis => {
            expect(analysis.status).toBe(200);
        });
        // Create audit events for each institution
        const auditPromises = transactions.map((transaction, index) => {
            const analysisResult = analyses[index].data;
            return axios.post(`${config.auditServiceUrl}/events`, {
                eventType: 'multi_tenant_test',
                actorId: 'integration_test',
                resourceId: transaction.id,
                action: 'fraud_analysis',
                details: {
                    fraudProbability: analysisResult.fraudProbability,
                    decision: analysisResult.decision,
                    testRun: true
                },
                institutionId: transaction.institutionId
            });
        });
        const auditResponses = await Promise.all(auditPromises);
        auditResponses.forEach(response => {
            expect(response.status).toBe(201);
        });
        // Verify each institution can only see its own events
        for (const institution of institutions) {
            const eventsResponse = await axios.get(`${config.auditServiceUrl}/events`, {
                params: {
                    institutionId: institution,
                    eventType: 'multi_tenant_test',
                    limit: 10
                }
            });
            expect(eventsResponse.status).toBe(200);
            const events = eventsResponse.data.events;
            // Should only have events for this institution
            events.forEach((event) => {
                expect(event.institutionId).toBe(institution);
            });
        }
    }, 45000);
    test('High-volume concurrent processing', async () => {
        const transactionCount = 100;
        const maxConcurrency = 20;
        console.log(`Testing high-volume processing: ${transactionCount} transactions`);
        const { results, throughput, avgLatency } = await TestUtilities.measureThroughput(async (index) => {
            const transaction = TestDataGenerator.generateTransaction();
            const response = await axios.post(`${config.fraudAgentUrl}/analyze`, {
                transaction,
                options: { performanceMode: 'realtime' }
            });
            return {
                transactionId: transaction.id,
                success: response.status === 200,
                fraudProbability: response.data.fraudProbability,
                latency: response.data.processingTimeMs
            };
        }, transactionCount, maxConcurrency);
        console.log(`Throughput: ${throughput.toFixed(2)} TPS`);
        console.log(`Average latency: ${avgLatency.toFixed(2)}ms`);
        console.log(`Successful requests: ${results.filter(r => r.success).length}/${transactionCount}`);
        // Performance assertions
        expect(throughput).toBeGreaterThan(config.performanceThresholds.minThroughputTps);
        expect(avgLatency).toBeLessThan(config.performanceThresholds.maxLatencyMs);
        // Availability assertion
        const successRate = (results.filter(r => r.success).length / transactionCount) * 100;
        expect(successRate).toBeGreaterThan(config.performanceThresholds.minAvailability);
        // Fraud detection quality assertion
        const fraudAnalyses = results.filter(r => r.success);
        const validAnalyses = fraudAnalyses.filter(r => r.fraudProbability >= 0 && r.fraudProbability <= 1);
        const qualityRate = (validAnalyses.length / fraudAnalyses.length) * 100;
        expect(qualityRate).toBeGreaterThan(config.performanceThresholds.minAccuracy * 100);
    }, 120000); // 2 minute timeout for high-volume test
});
// Performance and stress tests
describe('Performance Validation', () => {
    test('Latency requirements compliance', async () => {
        const testCount = 50;
        const latencies = [];
        for (let i = 0; i < testCount; i++) {
            const transaction = TestDataGenerator.generateTransaction();
            const { latency } = await TestUtilities.measureLatency(async () => {
                return await axios.post(`${config.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { performanceMode: 'realtime' }
                });
            });
            latencies.push(latency);
        }
        // Calculate percentiles
        const sortedLatencies = latencies.sort((a, b) => a - b);
        const p95 = sortedLatencies[Math.floor(testCount * 0.95)];
        const p99 = sortedLatencies[Math.floor(testCount * 0.99)];
        const mean = latencies.reduce((sum, l) => sum + l, 0) / latencies.length;
        console.log(`Latency stats: Mean: ${mean.toFixed(2)}ms, P95: ${p95.toFixed(2)}ms, P99: ${p99.toFixed(2)}ms`);
        // Assert latency requirements
        expect(p95).toBeLessThan(config.performanceThresholds.maxLatencyMs);
        expect(p99).toBeLessThan(config.performanceThresholds.maxLatencyMs * 2);
        expect(mean).toBeLessThan(config.performanceThresholds.maxLatencyMs * 0.5);
    });
    test('System stability under sustained load', async () => {
        const duration = 30000; // 30 seconds
        const targetTps = 100;
        const interval = 1000 / targetTps; // milliseconds between requests
        console.log(`Testing system stability: ${targetTps} TPS for ${duration / 1000} seconds`);
        const startTime = Date.now();
        const results = [];
        while (Date.now() - startTime < duration) {
            const requestStart = performance.now();
            try {
                const transaction = TestDataGenerator.generateTransaction();
                const response = await axios.post(`${config.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { performanceMode: 'realtime' }
                }, { timeout: 5000 });
                const latency = performance.now() - requestStart;
                results.push({
                    success: response.status === 200,
                    latency,
                    timestamp: Date.now()
                });
            }
            catch (error) {
                const latency = performance.now() - requestStart;
                results.push({
                    success: false,
                    latency,
                    timestamp: Date.now()
                });
            }
            // Wait for next request
            const elapsed = performance.now() - requestStart;
            const waitTime = Math.max(0, interval - elapsed);
            await new Promise(resolve => setTimeout(resolve, waitTime));
        }
        const actualDuration = (Date.now() - startTime) / 1000;
        const actualTps = results.length / actualDuration;
        const successRate = (results.filter(r => r.success).length / results.length) * 100;
        const avgLatency = results.reduce((sum, r) => sum + r.latency, 0) / results.length;
        console.log(`Actual TPS: ${actualTps.toFixed(2)}`);
        console.log(`Success rate: ${successRate.toFixed(2)}%`);
        console.log(`Average latency: ${avgLatency.toFixed(2)}ms`);
        // Assert system stability
        expect(successRate).toBeGreaterThan(config.performanceThresholds.minAvailability);
        expect(avgLatency).toBeLessThan(config.performanceThresholds.maxLatencyMs);
        expect(actualTps).toBeGreaterThan(targetTps * 0.9); // Within 10% of target
    }, 60000); // 1 minute timeout
});
// Dashboard and monitoring tests
describe('Dashboard and Monitoring Integration', () => {
    test('Dashboard health and metrics endpoints', async () => {
        const healthResponse = await axios.get(`${config.dashboardUrl}/health`);
        expect(healthResponse.status).toBe(200);
        const metricsResponse = await axios.get(`${config.dashboardUrl}/api/metrics`);
        expect(metricsResponse.status).toBe(200);
        expect(metricsResponse.data).toHaveProperty('timestamp');
    });
    test('Real-time metrics via WebSocket', async () => {
        return new Promise((resolve, reject) => {
            const ws = new WebSocket(`${config.dashboardUrl.replace('http', 'ws')}/ws/metrics`);
            let messageReceived = false;
            ws.on('open', () => {
                console.log('WebSocket connected to dashboard');
            });
            ws.on('message', (data) => {
                try {
                    const metrics = JSON.parse(data.toString());
                    expect(metrics).toHaveProperty('timestamp');
                    expect(metrics).toHaveProperty('transactions');
                    expect(metrics).toHaveProperty('latency');
                    messageReceived = true;
                    ws.close();
                    resolve();
                }
                catch (error) {
                    reject(error);
                }
            });
            ws.on('error', (error) => {
                reject(error);
            });
            // Timeout after 10 seconds
            setTimeout(() => {
                if (!messageReceived) {
                    ws.close();
                    reject(new Error('WebSocket timeout: no metrics received'));
                }
            }, 10000);
        });
    });
});
// Final integration verification
describe('System Integration Verification', () => {
    test('Complete system integration verification', async () => {
        console.log('🔍 Running complete system integration verification...');
        // Test data
        const institutions = ['BANK_US_001', 'BANK_UK_001', 'BANK_EU_001'];
        const transactionsPerInstitution = 5;
        const allTransactions = [];
        // Generate test transactions for each institution
        institutions.forEach(institutionId => {
            const transactions = TestDataGenerator.generateBatchTransactions(transactionsPerInstitution, institutionId);
            allTransactions.push(...transactions);
        });
        console.log(`Generated ${allTransactions.length} test transactions across ${institutions.length} institutions`);
        // Process all transactions through the complete pipeline
        const pipelineResults = [];
        for (const transaction of allTransactions) {
            try {
                // 1. Fraud analysis
                const fraudResponse = await axios.post(`${config.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { performanceMode: 'realtime' }
                });
                // 2. Audit event creation
                const auditEvent = {
                    eventType: 'final_integration_test',
                    actorId: 'integration_test_suite',
                    resourceId: transaction.id,
                    action: 'complete_pipeline_test',
                    details: {
                        fraudProbability: fraudResponse.data.fraudProbability,
                        decision: fraudResponse.data.decision,
                        testRun: true,
                        institutionId: transaction.institutionId
                    },
                    institutionId: transaction.institutionId
                };
                const auditResponse = await axios.post(`${config.auditServiceUrl}/events`, auditEvent);
                // 3. MCP server interaction
                const mcpResponse = await axios.post(`${config.mcpServerUrl}/mcp/jsonrpc`, {
                    jsonrpc: '2.0',
                    method: 'tools/call',
                    params: {
                        name: 'get_real_time_risk_score',
                        arguments: {
                            accountId: transaction.fromAccount,
                            institutionId: transaction.institutionId,
                            windowMinutes: 60
                        }
                    },
                    id: transaction.id
                });
                pipelineResults.push({
                    transactionId: transaction.id,
                    institutionId: transaction.institutionId,
                    fraudAnalysisSuccess: fraudResponse.status === 200,
                    auditEventSuccess: auditResponse.status === 201,
                    mcpQuerySuccess: mcpResponse.status === 200,
                    fraudProbability: fraudResponse.data.fraudProbability,
                    decision: fraudResponse.data.decision
                });
            }
            catch (error) {
                console.error(`Pipeline failed for transaction ${transaction.id}:`, error);
                pipelineResults.push({
                    transactionId: transaction.id,
                    institutionId: transaction.institutionId,
                    fraudAnalysisSuccess: false,
                    auditEventSuccess: false,
                    mcpQuerySuccess: false,
                    error: error instanceof Error ? error.message : 'Unknown error'
                });
            }
        }
        // Wait for all audit events to be processed
        await new Promise(resolve => setTimeout(resolve, 5000));
        // Verify audit trail integrity for each institution
        const auditVerifications = [];
        for (const institutionId of institutions) {
            try {
                const verificationResponse = await axios.post(`${config.auditServiceUrl}/verify`, {
                    institutionId,
                    startTime: Date.now() - 300000, // Last 5 minutes
                    endTime: Date.now()
                });
                auditVerifications.push({
                    institutionId,
                    success: verificationResponse.status === 200,
                    isValid: verificationResponse.data.isValid,
                    eventCount: verificationResponse.data.eventCount
                });
            }
            catch (error) {
                auditVerifications.push({
                    institutionId,
                    success: false,
                    error: error instanceof Error ? error.message : 'Unknown error'
                });
            }
        }
        // Calculate overall success metrics
        const totalTransactions = pipelineResults.length;
        const successfulPipelines = pipelineResults.filter(r => r.fraudAnalysisSuccess && r.auditEventSuccess && r.mcpQuerySuccess).length;
        const successRate = (successfulPipelines / totalTransactions) * 100;
        const validFraudAnalyses = pipelineResults.filter(r => r.fraudAnalysisSuccess &&
            r.fraudProbability >= 0 &&
            r.fraudProbability <= 1 &&
            ['approve', 'reject', 'review'].includes(r.decision)).length;
        const fraudAnalysisQuality = (validFraudAnalyses / totalTransactions) * 100;
        const validAuditTrails = auditVerifications.filter(v => v.success && v.isValid).length;
        const auditIntegrityRate = (validAuditTrails / institutions.length) * 100;
        // Log results
        console.log('🎯 Final Integration Verification Results:');
        console.log(`Total transactions processed: ${totalTransactions}`);
        console.log(`Successful end-to-end pipelines: ${successfulPipelines}/${totalTransactions} (${successRate.toFixed(2)}%)`);
        console.log(`Fraud analysis quality: ${fraudAnalysisQuality.toFixed(2)}%`);
        console.log(`Audit trail integrity: ${auditIntegrityRate.toFixed(2)}%`);
        // Assertions for final verification
        expect(successRate).toBeGreaterThan(config.performanceThresholds.minAvailability);
        expect(fraudAnalysisQuality).toBeGreaterThan(config.performanceThresholds.minAccuracy * 100);
        expect(auditIntegrityRate).toBe(100); // All audit trails must be valid
        // Institution isolation verification
        institutions.forEach(institutionId => {
            const institutionResults = pipelineResults.filter(r => r.institutionId === institutionId);
            const institutionSuccessRate = (institutionResults.filter(r => r.fraudAnalysisSuccess && r.auditEventSuccess && r.mcpQuerySuccess).length / institutionResults.length) * 100;
            expect(institutionSuccessRate).toBeGreaterThan(config.performanceThresholds.minAvailability);
        });
        console.log('✅ Complete system integration verification PASSED');
    }, 180000); // 3 minute timeout for comprehensive test
});
export default {};
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiaW50ZWdyYXRpb24tdGVzdC1zdWl0ZS5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbImludGVncmF0aW9uLXRlc3Qtc3VpdGUudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUE7Ozs7OztHQU1HO0FBRUgsT0FBTyxFQUFFLFFBQVEsRUFBRSxJQUFJLEVBQUUsTUFBTSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFFLE1BQU0sZUFBZSxDQUFDO0FBQ3hGLE9BQU8sS0FBd0IsTUFBTSxPQUFPLENBQUM7QUFDN0MsT0FBTyxTQUFTLE1BQU0sSUFBSSxDQUFDO0FBQzNCLE9BQU8sRUFBRSxXQUFXLEVBQUUsTUFBTSxZQUFZLENBQUM7QUFDekMsT0FBTyxFQUFFLElBQUksRUFBRSxNQUFNLElBQUksQ0FBQztBQUMxQixPQUFPLEVBQUUsWUFBWSxFQUFFLE1BQU0sT0FBTyxDQUFDO0FBbUJyQyxNQUFNLE1BQU0sR0FBZTtJQUN6QixZQUFZLEVBQUUsT0FBTyxDQUFDLEdBQUcsQ0FBQyxjQUFjLElBQUksdUJBQXVCO0lBQ25FLGFBQWEsRUFBRSxPQUFPLENBQUMsR0FBRyxDQUFDLGVBQWUsSUFBSSx1QkFBdUI7SUFDckUsZUFBZSxFQUFFLE9BQU8sQ0FBQyxHQUFHLENBQUMsaUJBQWlCLElBQUksdUJBQXVCO0lBQ3pFLFlBQVksRUFBRSxPQUFPLENBQUMsR0FBRyxDQUFDLGFBQWEsSUFBSSx1QkFBdUI7SUFDbEUsV0FBVyxFQUFFLE9BQU8sQ0FBQyxHQUFHLENBQUMsWUFBWSxJQUFJLGlGQUFpRjtJQUMxSCxRQUFRLEVBQUUsT0FBTyxDQUFDLEdBQUcsQ0FBQyxTQUFTLElBQUksd0JBQXdCO0lBQzNELFdBQVcsRUFBRSxLQUFLLEVBQUUsYUFBYTtJQUNqQyxxQkFBcUIsRUFBRTtRQUNyQixZQUFZLEVBQUUsR0FBRztRQUNqQixnQkFBZ0IsRUFBRSxJQUFJO1FBQ3RCLFdBQVcsRUFBRSxJQUFJO1FBQ2pCLGVBQWUsRUFBRSxJQUFJO0tBQ3RC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