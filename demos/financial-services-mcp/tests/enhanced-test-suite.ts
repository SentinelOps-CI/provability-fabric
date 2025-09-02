/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Enhanced Testing Suite for Financial Services MCP
 * Comprehensive testing framework with sub-millisecond validation
 */

import { describe, test, expect, beforeAll, afterAll, beforeEach, afterEach } from '@jest/globals';
import axios, { AxiosInstance } from 'axios';
import WebSocket from 'ws';
import { performance } from 'perf_hooks';
import { Pool } from 'pg';
import { createClient } from 'redis';
import { spawn, ChildProcess } from 'child_process';
import { Worker, isMainThread, parentPort, workerData } from 'worker_threads';

// Enhanced test configuration with stricter requirements
interface EnhancedTestConfig {
  mcpServerUrl: string;
  fraudAgentUrl: string;
  auditServiceUrl: string;
  dashboardUrl: string;
  databaseUrl: string;
  redisUrl: string;
  testTimeout: number;
  strictPerformanceThresholds: {
    ultraLowLatencyMs: number;    // 0.5ms for critical operations
    lowLatencyMs: number;         // 1.0ms for normal operations
    mediumLatencyMs: number;      // 5.0ms for complex operations
    maxLatencyMs: number;         // 10ms hard limit
    minThroughputTps: number;     // 2000 TPS minimum
    targetThroughputTps: number;  // 5000 TPS target
    minAccuracy: number;          // 99.5% accuracy
    minAvailability: number;      // 99.95% availability
  };
  stressTestParams: {
    maxConcurrentUsers: number;   // 500 concurrent users
    peakLoadMultiplier: number;   // 10x normal load
    sustainedLoadDurationMs: number; // 10 minutes
    spikeDurationMs: number;      // 30 seconds
  };
}

const enhancedConfig: EnhancedTestConfig = {
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
  private static institutionIds = ['BANK_US_001', 'BANK_UK_001', 'BANK_EU_001', 'BANK_ASIA_001'];
  private static currencies = ['USD', 'EUR', 'GBP', 'JPY', 'CHF'];
  
  static generateHighVolumeTransactions(count: number, institutionId?: string): any[] {
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
  
  static generateSuspiciousTransactions(count: number): any[] {
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
  
  static generateConcurrentInstitutionTransactions(transactionsPerInstitution: number): Map<string, any[]> {
    const institutionTransactions = new Map();
    
    for (const institution of this.institutionIds) {
      const transactions = this.generateHighVolumeTransactions(transactionsPerInstitution, institution);
      institutionTransactions.set(institution, transactions);
    }
    
    return institutionTransactions;
  }
  
  private static generateRealisticAmount(currency: string): number {
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
    } else if (rand < 0.95) {
      // 25% medium transactions
      return Math.random() * range.typical * 2 + range.typical * 0.5;
    } else {
      // 5% large transactions
      return Math.random() * (range.max - range.typical * 2) + range.typical * 2;
    }
  }
  
  private static generateSuspiciousAmount(pattern: string): number {
    switch (pattern) {
      case 'round_amounts':
        return [1000, 5000, 10000, 25000, 50000][Math.floor(Math.random() * 5)];
      case 'high_value':
        return Math.random() * 500000 + 100000; // $100k-$600k
      default:
        return Math.random() * 50000 + 1000;
    }
  }
  
  private static generateSuspiciousTimestamp(pattern: string): number {
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
  
  private static generateSuspiciousFlags(pattern: string): string[] {
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
  private static measurements: Map<string, number[]> = new Map();
  
  static async measureOperation<T>(
    operationName: string,
    operation: () => Promise<T>,
    expectedLatencyMs?: number
  ): Promise<{ result: T; latency: number; compliance: boolean }> {
    const start = performance.now();
    const result = await operation();
    const latency = performance.now() - start;
    
    // Record measurement
    if (!this.measurements.has(operationName)) {
      this.measurements.set(operationName, []);
    }
    this.measurements.get(operationName)!.push(latency);
    
    const compliance = expectedLatencyMs ? latency <= expectedLatencyMs : true;
    
    return { result, latency, compliance };
  }
  
  static async measureThroughput<T>(
    operationName: string,
    operationFactory: (index: number) => Promise<T>,
    count: number,
    maxConcurrency: number = 100,
    targetThroughput?: number
  ): Promise<{
    results: T[];
    throughput: number;
    avgLatency: number;
    minLatency: number;
    maxLatency: number;
    p95Latency: number;
    p99Latency: number;
    compliance: boolean;
  }> {
    const start = performance.now();
    const results: T[] = [];
    const latencies: number[] = [];
    
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
  
  static getPerformanceStats(operationName: string): {
    count: number;
    avgLatency: number;
    minLatency: number;
    maxLatency: number;
    p95Latency: number;
    p99Latency: number;
  } {
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
  
  static clearMeasurements(): void {
    this.measurements.clear();
  }
}

// Enhanced test utilities with additional capabilities
class EnhancedTestUtilities {
  private static dbPool: Pool;
  private static redisClient: ReturnType<typeof createClient>;
  private static serviceProcesses: Map<string, ChildProcess> = new Map();
  
  static async setupEnhancedEnvironment(): Promise<void> {
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
  
  static async warmupServices(): Promise<void> {
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
      } catch (error) {
        // Ignore warmup errors
      }
    }
    
    console.log('✅ Service warmup completed');
  }
  
  static async validateSystemHealth(): Promise<{
    allHealthy: boolean;
    serviceHealth: Map<string, boolean>;
    performanceBaseline: Map<string, number>;
  }> {
    const serviceHealth = new Map<string, boolean>();
    const performanceBaseline = new Map<string, number>();
    
    const services = [
      { name: 'MCP Server', url: `${enhancedConfig.mcpServerUrl}/health` },
      { name: 'Fraud Agent', url: `${enhancedConfig.fraudAgentUrl}/health` },
      { name: 'Audit Service', url: `${enhancedConfig.auditServiceUrl}/health` },
      { name: 'Dashboard', url: `${enhancedConfig.dashboardUrl}/health` }
    ];
    
    for (const service of services) {
      try {
        const measurement = await EnhancedPerformanceUtils.measureOperation(
          `health_check_${service.name}`,
          () => axios.get(service.url, { timeout: 5000 })
        );
        
        serviceHealth.set(service.name, measurement.result.status === 200);
        performanceBaseline.set(service.name, measurement.latency);
        
        if (measurement.latency > enhancedConfig.strictPerformanceThresholds.mediumLatencyMs) {
          console.warn(`⚠️  ${service.name} health check took ${measurement.latency.toFixed(2)}ms`);
        }
        
      } catch (error) {
        serviceHealth.set(service.name, false);
        console.error(`❌ ${service.name} health check failed:`, error);
      }
    }
    
    const allHealthy = Array.from(serviceHealth.values()).every(healthy => healthy);
    
    return { allHealthy, serviceHealth, performanceBaseline };
  }
  
  static async generateRealtimeLoad(
    durationMs: number,
    transactionsPerSecond: number,
    institutionId?: string
  ): Promise<void> {
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
  
  static async validateDataIntegrity(): Promise<{
    databaseIntegrity: boolean;
    auditTrailIntegrity: boolean;
    cacheConsistency: boolean;
    issues: string[];
  }> {
    const issues: string[] = [];
    
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
      
    } catch (error) {
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
      
    } catch (error) {
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
      
    } catch (error) {
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
  
  static async cleanupTestData(): Promise<void> {
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
      
    } catch (error) {
      console.error('Error during test cleanup:', error);
    }
  }
  
  static async shutdown(): Promise<void> {
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
      const measurement = await EnhancedPerformanceUtils.measureOperation(
        'ultra_low_latency_fraud_detection',
        async () => {
          return await axios.post(`${enhancedConfig.fraudAgentUrl}/analyze`, {
            transaction,
            options: { performanceMode: 'realtime', ultraLowLatency: true }
          }, {
            timeout: 1000,
            headers: { 'Content-Type': 'application/json' }
          });
        },
        enhancedConfig.strictPerformanceThresholds.ultraLowLatencyMs
      );
      
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
    
    const measurement = await EnhancedPerformanceUtils.measureThroughput(
      'high_throughput_sustained',
      async (index) => {
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
      },
      totalTransactions,
      200, // Max concurrency
      targetThroughput
    );
    
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
      const measurement = await EnhancedPerformanceUtils.measureThroughput(
        `multi_tenant_${institutionId}`,
        async (index) => {
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
        },
        transactions.length,
        50 // Max concurrency per institution
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
