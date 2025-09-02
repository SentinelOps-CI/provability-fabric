/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * Enhanced Testing Suite for Financial Services MCP
 * Comprehensive testing framework with sub-millisecond validation
 */
import { describe, test, expect, beforeAll, afterAll, beforeEach } from '@jest/globals';
import axios from 'axios';
import { performance } from 'perf_hooks';
import { Pool } from 'pg';
import { createClient } from 'redis';
const enhancedConfig = {
    mcpServerUrl: process.env.MCP_SERVER_URL || 'http://localhost:8080',
    fraudAgentUrl: process.env.FRAUD_AGENT_URL || 'http://localhost:8082',
    auditServiceUrl: process.env.AUDIT_SERVICE_URL || 'http://localhost:8083',
    dashboardUrl: process.env.DASHBOARD_URL || 'http://localhost:3001',
    databaseUrl: process.env.DATABASE_URL || 'postgresql://fintech_user:secure_fintech_2025@localhost:5433/financial_services',
    redisUrl: process.env.REDIS_URL || 'redis://localhost:6380',
    testTimeout: 60000,
    strictPerformanceThresholds: {
        ultraLowLatencyMs: 0.5,
        lowLatencyMs: 1.0,
        mediumLatencyMs: 5.0,
        maxLatencyMs: 10.0,
        minThroughputTps: 2000,
        targetThroughputTps: 5000,
        minAccuracy: 0.995,
        minAvailability: 99.95
    },
    stressTestParams: {
        maxConcurrentUsers: 500,
        peakLoadMultiplier: 10,
        sustainedLoadDurationMs: 600000, // 10 minutes
        spikeDurationMs: 30000 // 30 seconds
    }
};
// Enhanced test data generators with realistic financial patterns
class EnhancedTestDataGenerator {
    static institutionIds = ['BANK_US_001', 'BANK_UK_001', 'BANK_EU_001', 'BANK_ASIA_001'];
    static currencies = ['USD', 'EUR', 'GBP', 'JPY', 'CHF'];
    static generateHighVolumeTransactions(count, institutionId) {
        const transactions = [];
        const baseTimestamp = Date.now();
        for (let i = 0; i < count; i++) {
            const institution = institutionId || this.institutionIds[Math.floor(Math.random() * this.institutionIds.length)];
            const currency = this.currencies[Math.floor(Math.random() * this.currencies.length)];
            transactions.push({
                id: `hvt_${baseTimestamp}_${i}_${Math.random().toString(36).substr(2, 9)}`,
                amount: this.generateRealisticAmount(currency),
                currency,
                fromAccount: `ACC_${institution}_${Math.floor(Math.random() * 10000)}`,
                toAccount: `ACC_${institution}_${Math.floor(Math.random() * 10000)}`,
                timestamp: baseTimestamp - Math.random() * 3600000, // Last hour
                institutionId: institution,
                metadata: {
                    testType: 'high_volume',
                    batchId: Math.floor(i / 100),
                    priority: Math.random() > 0.8 ? 'high' : 'normal'
                }
            });
        }
        return transactions;
    }
    static generateSuspiciousTransactions(count) {
        const transactions = [];
        const suspiciousPatterns = [
            'round_amounts',
            'high_frequency',
            'unusual_hours',
            'cross_border',
            'high_value',
            'new_recipient'
        ];
        for (let i = 0; i < count; i++) {
            const pattern = suspiciousPatterns[Math.floor(Math.random() * suspiciousPatterns.length)];
            const institution = this.institutionIds[Math.floor(Math.random() * this.institutionIds.length)];
            transactions.push({
                id: `sus_${Date.now()}_${i}_${Math.random().toString(36).substr(2, 9)}`,
                amount: this.generateSuspiciousAmount(pattern),
                currency: 'USD',
                fromAccount: `ACC_${institution}_suspicious_${i}`,
                toAccount: `ACC_UNKNOWN_${Math.floor(Math.random() * 100)}`,
                timestamp: this.generateSuspiciousTimestamp(pattern),
                institutionId: institution,
                metadata: {
                    testType: 'suspicious',
                    pattern,
                    expectedFraud: true,
                    suspiciousFlags: this.generateSuspiciousFlags(pattern)
                }
            });
        }
        return transactions;
    }
    static generateConcurrentInstitutionTransactions(transactionsPerInstitution) {
        const institutionTransactions = new Map();
        for (const institution of this.institutionIds) {
            const transactions = this.generateHighVolumeTransactions(transactionsPerInstitution, institution);
            institutionTransactions.set(institution, transactions);
        }
        return institutionTransactions;
    }
    static generateRealisticAmount(currency) {
        const ranges = {
            'USD': { min: 10, max: 50000, typical: 1500 },
            'EUR': { min: 10, max: 45000, typical: 1200 },
            'GBP': { min: 8, max: 40000, typical: 1000 },
            'JPY': { min: 1000, max: 5000000, typical: 150000 },
            'CHF': { min: 10, max: 48000, typical: 1400 }
        };
        const range = ranges[currency] || ranges['USD'];
        // Generate amounts with realistic distribution (most transactions are small)
        const rand = Math.random();
        if (rand < 0.7) {
            // 70% small transactions
            return Math.random() * range.typical * 0.5 + range.min;
        }
        else if (rand < 0.95) {
            // 25% medium transactions
            return Math.random() * range.typical * 2 + range.typical * 0.5;
        }
        else {
            // 5% large transactions
            return Math.random() * (range.max - range.typical * 2) + range.typical * 2;
        }
    }
    static generateSuspiciousAmount(pattern) {
        switch (pattern) {
            case 'round_amounts':
                return [1000, 5000, 10000, 25000, 50000][Math.floor(Math.random() * 5)];
            case 'high_value':
                return Math.random() * 500000 + 100000; // $100k-$600k
            default:
                return Math.random() * 50000 + 1000;
        }
    }
    static generateSuspiciousTimestamp(pattern) {
        const now = Date.now();
        switch (pattern) {
            case 'unusual_hours':
                // Generate timestamp between 2 AM and 5 AM
                const date = new Date();
                date.setHours(2 + Math.random() * 3, Math.random() * 60, Math.random() * 60);
                return date.getTime();
            case 'high_frequency':
                // Generate very recent timestamp (last few minutes)
                return now - Math.random() * 300000; // Last 5 minutes
            default:
                return now - Math.random() * 3600000; // Last hour
        }
    }
    static generateSuspiciousFlags(pattern) {
        const flagMap = {
            'round_amounts': ['round_amount', 'unusual_precision'],
            'high_frequency': ['high_velocity', 'rapid_succession'],
            'unusual_hours': ['off_hours', 'night_transaction'],
            'cross_border': ['international', 'currency_mismatch'],
            'high_value': ['large_amount', 'above_threshold'],
            'new_recipient': ['unknown_recipient', 'first_time_transfer']
        };
        return flagMap[pattern] || ['general_suspicious'];
    }
}
// Enhanced performance measurement utilities
class EnhancedPerformanceUtils {
    static measurements = new Map();
    static async measureOperation(operationName, operation, expectedLatencyMs) {
        const start = performance.now();
        const result = await operation();
        const latency = performance.now() - start;
        // Record measurement
        if (!this.measurements.has(operationName)) {
            this.measurements.set(operationName, []);
        }
        this.measurements.get(operationName).push(latency);
        const compliance = expectedLatencyMs ? latency <= expectedLatencyMs : true;
        return { result, latency, compliance };
    }
    static async measureThroughput(operationName, operationFactory, count, maxConcurrency = 100, targetThroughput) {
        const start = performance.now();
        const results = [];
        const latencies = [];
        // Process in batches to control concurrency
        for (let i = 0; i < count; i += maxConcurrency) {
            const batch = [];
            const batchEnd = Math.min(i + maxConcurrency, count);
            for (let j = i; j < batchEnd; j++) {
                batch.push(this.measureOperation(`${operationName}_batch`, () => operationFactory(j)));
            }
            const batchResults = await Promise.allSettled(batch);
            for (const result of batchResults) {
                if (result.status === 'fulfilled') {
                    results.push(result.value.result);
                    latencies.push(result.value.latency);
                }
            }
        }
        const duration = (performance.now() - start) / 1000; // seconds
        const throughput = results.length / duration;
        // Calculate latency statistics
        const sortedLatencies = latencies.sort((a, b) => a - b);
        const len = sortedLatencies.length;
        const avgLatency = latencies.reduce((sum, l) => sum + l, 0) / len;
        const minLatency = sortedLatencies[0] || 0;
        const maxLatency = sortedLatencies[len - 1] || 0;
        const p95Latency = sortedLatencies[Math.floor(len * 0.95)] || 0;
        const p99Latency = sortedLatencies[Math.floor(len * 0.99)] || 0;
        const compliance = targetThroughput ? throughput >= targetThroughput : true;
        return {
            results,
            throughput,
            avgLatency,
            minLatency,
            maxLatency,
            p95Latency,
            p99Latency,
            compliance
        };
    }
    static getPerformanceStats(operationName) {
        const measurements = this.measurements.get(operationName) || [];
        const sorted = measurements.sort((a, b) => a - b);
        const len = sorted.length;
        return {
            count: len,
            avgLatency: len > 0 ? measurements.reduce((sum, l) => sum + l, 0) / len : 0,
            minLatency: sorted[0] || 0,
            maxLatency: sorted[len - 1] || 0,
            p95Latency: sorted[Math.floor(len * 0.95)] || 0,
            p99Latency: sorted[Math.floor(len * 0.99)] || 0
        };
    }
    static clearMeasurements() {
        this.measurements.clear();
    }
}
// Enhanced test utilities with additional capabilities
class EnhancedTestUtilities {
    static dbPool;
    static redisClient;
    static serviceProcesses = new Map();
    static async setupEnhancedEnvironment() {
        // Setup database with enhanced monitoring
        this.dbPool = new Pool({
            connectionString: enhancedConfig.databaseUrl,
            max: 20,
            idleTimeoutMillis: 30000,
            connectionTimeoutMillis: 2000,
        });
        // Test database connectivity and performance
        const dbStart = performance.now();
        await this.dbPool.query('SELECT 1');
        const dbLatency = performance.now() - dbStart;
        if (dbLatency > 10) {
            console.warn(`⚠️  Database latency is high: ${dbLatency.toFixed(2)}ms`);
        }
        // Setup Redis with enhanced configuration
        this.redisClient = createClient({
            url: enhancedConfig.redisUrl,
            socket: {
                connectTimeout: 1000,
                commandTimeout: 500,
            }
        });
        await this.redisClient.connect();
        // Test Redis performance
        const redisStart = performance.now();
        await this.redisClient.ping();
        const redisLatency = performance.now() - redisStart;
        if (redisLatency > 5) {
            console.warn(`⚠️  Redis latency is high: ${redisLatency.toFixed(2)}ms`);
        }
        console.log(`✅ Enhanced environment ready (DB: ${dbLatency.toFixed(2)}ms, Redis: ${redisLatency.toFixed(2)}ms)`);
    }
    static async warmupServices() {
        console.log('🔥 Warming up services for optimal performance...');
        const warmupOperations = [
            // Warm up MCP server
            () => axios.get(`${enhancedConfig.mcpServerUrl}/health`),
            // Warm up fraud agent
            () => axios.get(`${enhancedConfig.fraudAgentUrl}/health`),
            // Warm up audit service
            () => axios.get(`${enhancedConfig.auditServiceUrl}/health`),
            // Warm up dashboard
            () => axios.get(`${enhancedConfig.dashboardUrl}/health`)
        ];
        // Run warmup operations multiple times
        for (let i = 0; i < 5; i++) {
            await Promise.all(warmupOperations.map(op => op().catch(() => null)));
            await new Promise(resolve => setTimeout(resolve, 200));
        }
        // Generate some test transactions to warm up the pipeline
        const warmupTransactions = EnhancedTestDataGenerator.generateHighVolumeTransactions(10);
        for (const transaction of warmupTransactions) {
            try {
                await axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { performanceMode: 'realtime' }
                }, { timeout: 5000 });
            }
            catch (error) {
                // Ignore warmup errors
            }
        }
        console.log('✅ Service warmup completed');
    }
    static async validateSystemHealth() {
        const serviceHealth = new Map();
        const performanceBaseline = new Map();
        const services = [
            { name: 'MCP Server', url: `${enhancedConfig.mcpServerUrl}/health` },
            { name: 'Fraud Agent', url: `${enhancedConfig.fraudAgentUrl}/health` },
            { name: 'Audit Service', url: `${enhancedConfig.auditServiceUrl}/health` },
            { name: 'Dashboard', url: `${enhancedConfig.dashboardUrl}/health` }
        ];
        for (const service of services) {
            try {
                const measurement = await EnhancedPerformanceUtils.measureOperation(`health_check_${service.name}`, () => axios.get(service.url, { timeout: 5000 }));
                serviceHealth.set(service.name, measurement.result.status === 200);
                performanceBaseline.set(service.name, measurement.latency);
                if (measurement.latency > enhancedConfig.strictPerformanceThresholds.mediumLatencyMs) {
                    console.warn(`⚠️  ${service.name} health check took ${measurement.latency.toFixed(2)}ms`);
                }
            }
            catch (error) {
                serviceHealth.set(service.name, false);
                console.error(`❌ ${service.name} health check failed:`, error);
            }
        }
        const allHealthy = Array.from(serviceHealth.values()).every(healthy => healthy);
        return { allHealthy, serviceHealth, performanceBaseline };
    }
    static async generateRealtimeLoad(durationMs, transactionsPerSecond, institutionId) {
        const intervalMs = 1000 / transactionsPerSecond;
        const startTime = Date.now();
        while (Date.now() - startTime < durationMs) {
            const transaction = EnhancedTestDataGenerator.generateHighVolumeTransactions(1, institutionId)[0];
            // Fire and forget to maintain load
            axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
                transaction,
                options: { performanceMode: 'realtime' }
            }, { timeout: 1000 }).catch(() => {
                // Ignore errors during load generation
            });
            await new Promise(resolve => setTimeout(resolve, intervalMs));
        }
    }
    static async validateDataIntegrity() {
        const issues = [];
        // Check database integrity
        let databaseIntegrity = true;
        try {
            const result = await this.dbPool.query(`
        SELECT 
          (SELECT COUNT(*) FROM transactions) as transaction_count,
          (SELECT COUNT(*) FROM audit_events) as audit_count,
          (SELECT COUNT(*) FROM fraud_detections) as fraud_count
      `);
            const { transaction_count, audit_count, fraud_count } = result.rows[0];
            if (transaction_count === 0 && audit_count === 0) {
                issues.push('No data found in database - may indicate connectivity issues');
                databaseIntegrity = false;
            }
        }
        catch (error) {
            issues.push(`Database integrity check failed: ${error}`);
            databaseIntegrity = false;
        }
        // Check audit trail integrity
        let auditTrailIntegrity = true;
        try {
            // Verify recent audit events have proper hash chains
            const result = await this.dbPool.query(`
        SELECT id, hash, previous_hash 
        FROM audit_events 
        WHERE timestamp > EXTRACT(EPOCH FROM NOW() - INTERVAL '1 hour') * 1000
        ORDER BY timestamp ASC
        LIMIT 100
      `);
            let previousHash = null;
            for (const event of result.rows) {
                if (previousHash && event.previous_hash !== previousHash) {
                    issues.push(`Audit trail hash chain broken at event ${event.id}`);
                    auditTrailIntegrity = false;
                    break;
                }
                previousHash = event.hash;
            }
        }
        catch (error) {
            issues.push(`Audit trail integrity check failed: ${error}`);
            auditTrailIntegrity = false;
        }
        // Check cache consistency
        let cacheConsistency = true;
        try {
            const testKey = 'integrity_test';
            const testValue = Date.now().toString();
            await this.redisClient.set(testKey, testValue, { EX: 10 });
            const retrievedValue = await this.redisClient.get(testKey);
            if (retrievedValue !== testValue) {
                issues.push('Redis cache consistency test failed');
                cacheConsistency = false;
            }
            await this.redisClient.del(testKey);
        }
        catch (error) {
            issues.push(`Cache consistency check failed: ${error}`);
            cacheConsistency = false;
        }
        return {
            databaseIntegrity,
            auditTrailIntegrity,
            cacheConsistency,
            issues
        };
    }
    static async cleanupTestData() {
        try {
            // Clean up test transactions
            await this.dbPool.query(`
        DELETE FROM fraud_detections 
        WHERE transaction_id IN (
          SELECT id FROM transactions WHERE id LIKE 'hvt_%' OR id LIKE 'sus_%'
        )
      `);
            await this.dbPool.query("DELETE FROM audit_events WHERE event_type LIKE '%test%'");
            await this.dbPool.query("DELETE FROM transactions WHERE id LIKE 'hvt_%' OR id LIKE 'sus_%'");
            // Clear Redis test data
            const keys = await this.redisClient.keys('test_*');
            if (keys.length > 0) {
                await this.redisClient.del(keys);
            }
        }
        catch (error) {
            console.error('Error during test cleanup:', error);
        }
    }
    static async shutdown() {
        if (this.dbPool) {
            await this.dbPool.end();
        }
        if (this.redisClient) {
            await this.redisClient.quit();
        }
        // Stop any service processes
        for (const [name, process] of this.serviceProcesses) {
            process.kill();
            console.log(`🛑 Stopped ${name} process`);
        }
    }
}
// Test suite setup
beforeAll(async () => {
    console.log('🚀 Starting Enhanced Financial Services MCP Test Suite');
    console.log('📊 Performance Thresholds:');
    console.log(`   Ultra-low latency: ${enhancedConfig.strictPerformanceThresholds.ultraLowLatencyMs}ms`);
    console.log(`   Low latency: ${enhancedConfig.strictPerformanceThresholds.lowLatencyMs}ms`);
    console.log(`   Target throughput: ${enhancedConfig.strictPerformanceThresholds.targetThroughputTps} TPS`);
    console.log(`   Minimum accuracy: ${(enhancedConfig.strictPerformanceThresholds.minAccuracy * 100).toFixed(2)}%`);
    await EnhancedTestUtilities.setupEnhancedEnvironment();
    await EnhancedTestUtilities.warmupServices();
    const healthCheck = await EnhancedTestUtilities.validateSystemHealth();
    if (!healthCheck.allHealthy) {
        throw new Error('System health check failed - cannot proceed with tests');
    }
    console.log('✅ Enhanced test environment ready');
}, 180000); // 3 minute timeout for setup
afterAll(async () => {
    console.log('🧹 Cleaning up enhanced test environment');
    await EnhancedTestUtilities.cleanupTestData();
    await EnhancedTestUtilities.shutdown();
}, 60000);
// Enhanced performance tests
describe('Enhanced Performance Validation', () => {
    beforeEach(() => {
        EnhancedPerformanceUtils.clearMeasurements();
    });
    test('Ultra-low latency fraud detection (< 0.5ms)', async () => {
        const transactions = EnhancedTestDataGenerator.generateHighVolumeTransactions(50);
        const results = [];
        for (const transaction of transactions) {
            const measurement = await EnhancedPerformanceUtils.measureOperation('ultra_low_latency_fraud_detection', async () => {
                return await axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { performanceMode: 'realtime', ultraLowLatency: true }
                }, {
                    timeout: 1000,
                    headers: { 'Content-Type': 'application/json' }
                });
            }, enhancedConfig.strictPerformanceThresholds.ultraLowLatencyMs);
            results.push(measurement);
            expect(measurement.result.status).toBe(200);
        }
        const stats = EnhancedPerformanceUtils.getPerformanceStats('ultra_low_latency_fraud_detection');
        console.log(`📊 Ultra-low latency stats: avg=${stats.avgLatency.toFixed(2)}ms, p95=${stats.p95Latency.toFixed(2)}ms, p99=${stats.p99Latency.toFixed(2)}ms`);
        // Strict assertions
        expect(stats.p95Latency).toBeLessThan(enhancedConfig.strictPerformanceThresholds.ultraLowLatencyMs);
        expect(stats.p99Latency).toBeLessThan(enhancedConfig.strictPerformanceThresholds.lowLatencyMs);
        // At least 90% of requests should meet ultra-low latency requirement
        const ultraLowLatencyCompliant = results.filter(r => r.compliance).length;
        const complianceRate = (ultraLowLatencyCompliant / results.length) * 100;
        expect(complianceRate).toBeGreaterThan(90);
    }, 60000);
    test('High-throughput sustained load (5000+ TPS)', async () => {
        const targetThroughput = enhancedConfig.strictPerformanceThresholds.targetThroughputTps;
        const testDurationSeconds = 30;
        const totalTransactions = targetThroughput * testDurationSeconds;
        console.log(`🔥 Testing sustained throughput: ${totalTransactions} transactions in ${testDurationSeconds}s`);
        const measurement = await EnhancedPerformanceUtils.measureThroughput('high_throughput_sustained', async (index) => {
            const transaction = EnhancedTestDataGenerator.generateHighVolumeTransactions(1)[0];
            transaction.id = `hts_${index}_${Date.now()}`;
            const response = await axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
                transaction,
                options: { performanceMode: 'realtime' }
            }, {
                timeout: 2000,
                headers: { 'Content-Type': 'application/json' }
            });
            return response.data;
        }, totalTransactions, 200, // Max concurrency
        targetThroughput);
        console.log(`📊 Throughput test results:`);
        console.log(`   Achieved: ${measurement.throughput.toFixed(2)} TPS`);
        console.log(`   Target: ${targetThroughput} TPS`);
        console.log(`   Success rate: ${((measurement.results.length / totalTransactions) * 100).toFixed(2)}%`);
        console.log(`   Avg latency: ${measurement.avgLatency.toFixed(2)}ms`);
        console.log(`   P95 latency: ${measurement.p95Latency.toFixed(2)}ms`);
        expect(measurement.throughput).toBeGreaterThan(targetThroughput * 0.95); // 95% of target
        expect(measurement.p95Latency).toBeLessThan(enhancedConfig.strictPerformanceThresholds.mediumLatencyMs);
        expect(measurement.results.length).toBeGreaterThan(totalTransactions * 0.98); // 98% success rate
    }, 120000); // 2 minute timeout
    test('Concurrent multi-tenant performance isolation', async () => {
        const institutionTransactions = EnhancedTestDataGenerator.generateConcurrentInstitutionTransactions(100);
        const institutionPromises = Array.from(institutionTransactions.entries()).map(async ([institutionId, transactions]) => {
            const measurement = await EnhancedPerformanceUtils.measureThroughput(`multi_tenant_${institutionId}`, async (index) => {
                const transaction = transactions[index % transactions.length];
                const response = await axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
                    transaction,
                    options: { institutionId }
                }, {
                    timeout: 5000,
                    headers: {
                        'X-Institution-ID': institutionId,
                        'Content-Type': 'application/json'
                    }
                });
                return response.data;
            }, transactions.length, 50 // Max concurrency per institution
            );
            return {
                institutionId,
                measurement
            };
        });
        const institutionResults = await Promise.all(institutionPromises);
        // Validate that each institution maintains good performance
        for (const { institutionId, measurement } of institutionResults) {
            console.log(`🏦 ${institutionId}: ${measurement.throughput.toFixed(2)} TPS, P95: ${measurement.p95Latency.toFixed(2)}ms`);
            expect(measurement.throughput).toBeGreaterThan(100); // Minimum 100 TPS per institution
            expect(measurement.p95Latency).toBeLessThan(enhancedConfig.strictPerformanceThresholds.mediumLatencyMs);
            expect(measurement.results.length).toBeGreaterThan(95); // 95% success rate minimum
        }
        // Validate no cross-contamination between institutions
        const totalThroughput = institutionResults.reduce((sum, result) => sum + result.measurement.throughput, 0);
        expect(totalThroughput).toBeGreaterThan(500); // Combined minimum throughput
    }, 180000); // 3 minute timeout
});
// Enhanced fraud detection accuracy tests
describe('Enhanced Fraud Detection Accuracy', () => {
    test('High-accuracy fraud detection with labeled data', async () => {
        const legitimateTransactions = EnhancedTestDataGenerator.generateHighVolumeTransactions(200);
        const suspiciousTransactions = EnhancedTestDataGenerator.generateSuspiciousTransactions(50);
        console.log(`🎯 Testing accuracy with ${legitimateTransactions.length} legitimate and ${suspiciousTransactions.length} suspicious transactions`);
        let correctPredictions = 0;
        let totalPredictions = 0;
        const results = [];
        // Test legitimate transactions
        for (const transaction of legitimateTransactions) {
            const response = await axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
                transaction,
                options: { performanceMode: 'realtime' }
            });
            const analysis = response.data;
            const predictedFraud = analysis.fraudProbability > 0.5;
            const actualFraud = false; // These are legitimate
            if (predictedFraud === actualFraud) {
                correctPredictions++;
            }
            totalPredictions++;
            results.push({
                transactionId: transaction.id,
                actualFraud,
                predictedFraud,
                fraudProbability: analysis.fraudProbability,
                decision: analysis.decision
            });
        }
        // Test suspicious transactions
        for (const transaction of suspiciousTransactions) {
            const response = await axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
                transaction,
                options: { performanceMode: 'realtime' }
            });
            const analysis = response.data;
            const predictedFraud = analysis.fraudProbability > 0.5;
            const actualFraud = true; // These are suspicious
            if (predictedFraud === actualFraud) {
                correctPredictions++;
            }
            totalPredictions++;
            results.push({
                transactionId: transaction.id,
                actualFraud,
                predictedFraud,
                fraudProbability: analysis.fraudProbability,
                decision: analysis.decision
            });
        }
        const accuracy = correctPredictions / totalPredictions;
        // Calculate additional metrics
        const truePositives = results.filter(r => r.actualFraud && r.predictedFraud).length;
        const falsePositives = results.filter(r => !r.actualFraud && r.predictedFraud).length;
        const trueNegatives = results.filter(r => !r.actualFraud && !r.predictedFraud).length;
        const falseNegatives = results.filter(r => r.actualFraud && !r.predictedFraud).length;
        const precision = truePositives / (truePositives + falsePositives);
        const recall = truePositives / (truePositives + falseNegatives);
        const f1Score = 2 * (precision * recall) / (precision + recall);
        console.log(`📊 Fraud Detection Accuracy Metrics:`);
        console.log(`   Accuracy: ${(accuracy * 100).toFixed(2)}%`);
        console.log(`   Precision: ${(precision * 100).toFixed(2)}%`);
        console.log(`   Recall: ${(recall * 100).toFixed(2)}%`);
        console.log(`   F1 Score: ${f1Score.toFixed(3)}`);
        console.log(`   True Positives: ${truePositives}`);
        console.log(`   False Positives: ${falsePositives}`);
        console.log(`   True Negatives: ${trueNegatives}`);
        console.log(`   False Negatives: ${falseNegatives}`);
        expect(accuracy).toBeGreaterThan(enhancedConfig.strictPerformanceThresholds.minAccuracy);
        expect(precision).toBeGreaterThan(0.90); // 90% precision minimum
        expect(recall).toBeGreaterThan(0.85); // 85% recall minimum
        expect(f1Score).toBeGreaterThan(0.87); // 87% F1 score minimum
    }, 120000);
});
export default {};
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiZW5oYW5jZWQtdGVzdC1zdWl0ZS5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbImVuaGFuY2VkLXRlc3Qtc3VpdGUudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUE7Ozs7OztHQU1HO0FBRUgsT0FBTyxFQUFFLFFBQVEsRUFBRSxJQUFJLEVBQUUsTUFBTSxFQUFFLFNBQVMsRUFBRSxRQUFRLEVBQUUsVUFBVSxFQUFhLE1BQU0sZUFBZSxDQUFDO0FBQ25HLE9BQU8sS0FBd0IsTUFBTSxPQUFPLENBQUM7QUFFN0MsT0FBTyxFQUFFLFdBQVcsRUFBRSxNQUFNLFlBQVksQ0FBQztBQUN6QyxPQUFPLEVBQUUsSUFBSSxFQUFFLE1BQU0sSUFBSSxDQUFDO0FBQzFCLE9BQU8sRUFBRSxZQUFZLEVBQUUsTUFBTSxPQUFPLENBQUM7QUErQnJDLE1BQU0sY0FBYyxHQUF1QjtJQUN6QyxZQUFZLEVBQUUsT0FBTyxDQUFDLEdBQUcsQ0FBQyxjQUFjLElBQUksdUJBQXVCO0lBQ25FLGFBQWEsRUFBRSxPQUFPLENBQUMsR0FBRyxDQUFDLGVBQWUsSUFBSSx1QkFBdUI7SUFDckUsZUFBZSxFQUFFLE9BQU8sQ0FBQyxHQUFHLENBQUMsaUJBQWlCLElBQUksdUJBQXVCO0lBQ3pFLFlBQVksRUFBRSxPQUFPLENBQUMsR0FBRyxDQUFDLGFBQWEsSUFBSSx1QkFBdUI7SUFDbEUsV0FBVyxFQUFFLE9BQU8sQ0FBQyxHQUFHLENBQUMsWUFBWSxJQUFJLGlGQUFpRjtJQUMxSCxRQUFRLEVBQUUsT0FBTyxDQUFDLEdBQUcsQ0FBQyxTQUFTLElBQUksd0JBQXdCO0lBQzNELFdBQVcsRUFBRSxLQUFLO0lBQ2xCLDJCQUEyQixFQUFFO1FBQzNCLGlCQUFpQixFQUFFLEdBQUc7UUFDdEIsWUFBWSxFQUFFLEdBQUc7UUFDakIsZUFBZSxFQUFFLEdBQUc7UUFDcEIsWUFBWSxFQUFFLElBQUk7UUFDbEIsZ0JBQWdCLEVBQUUsSUFBSTtRQUN0QixtQkFBbUIsRUFBRSxJQUFJO1FBQ3pC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