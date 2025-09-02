/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * End-to-End Integration Testing Suite
 * Comprehensive testing for Financial Services MCP implementation
 */

import { describe, test, expect, beforeAll, afterAll, beforeEach } from '@jest/globals';
import axios, { AxiosInstance } from 'axios';
import WebSocket from 'ws';
import { performance } from 'perf_hooks';
import { Pool } from 'pg';
import { createClient } from 'redis';

// Test configuration
interface TestConfig {
  mcpServerUrl: string;
  fraudAgentUrl: string;
  auditServiceUrl: string;
  dashboardUrl: string;
  databaseUrl: string;
  redisUrl: string;
  testTimeout: number;
  performanceThresholds: {
    maxLatencyMs: number;
    minThroughputTps: number;
    minAccuracy: number;
    minAvailability: number;
  };
}

const config: TestConfig = {
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
  static generateTransaction(institutionId: string = 'BANK_US_001'): any {
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

  static generateFraudulentTransaction(institutionId: string = 'BANK_US_001'): any {
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

  static generateAuditEvent(transactionId: string, institutionId: string): any {
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

  static generateBatchTransactions(count: number, institutionId: string = 'BANK_US_001'): any[] {
    const transactions = [];
    for (let i = 0; i < count; i++) {
      transactions.push(this.generateTransaction(institutionId));
    }
    return transactions;
  }
}

// Test utilities
class TestUtilities {
  private static dbPool: Pool;
  private static redisClient: ReturnType<typeof createClient>;

  static async setupDatabase(): Promise<void> {
    this.dbPool = new Pool({
      connectionString: config.databaseUrl,
      max: 5
    });

    // Test database connectivity
    await this.dbPool.query('SELECT 1');
  }

  static async setupRedis(): Promise<void> {
    this.redisClient = createClient({ url: config.redisUrl });
    await this.redisClient.connect();
  }

  static async cleanup(): Promise<void> {
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

  static async waitForServices(): Promise<void> {
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
        } catch (error) {
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

  static async measureLatency<T>(operation: () => Promise<T>): Promise<{ result: T; latency: number }> {
    const start = performance.now();
    const result = await operation();
    const latency = performance.now() - start;
    return { result, latency };
  }

  static async measureThroughput<T>(
    operationFactory: (index: number) => Promise<T>,
    count: number,
    maxConcurrency: number = 50
  ): Promise<{ results: T[]; throughput: number; avgLatency: number }> {
    const start = performance.now();
    const results: T[] = [];
    
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
        .map(r => (r as PromiseFulfilledResult<T>).value)
      );
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
  let mcpClient: AxiosInstance;

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

    const toolNames = response.data.result.tools.map((tool: any) => tool.name);
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

    const resourceUris = response.data.result.resources.map((resource: any) => resource.uri);
    expect(resourceUris).toContain('financial://transactions/realtime');
    expect(resourceUris).toContain('financial://audit/blockchain');
  });
});

// Fraud Detection Agent integration tests
describe('Fraud Detection Agent Integration', () => {
  let fraudClient: AxiosInstance;

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
      const sampleMetric = Object.values(metrics)[0] as any;
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
  let auditClient: AxiosInstance;

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
    const analysisPromises = transactions.map(transaction =>
      axios.post(`${config.fraudAgentUrl}/analyze`, {
        transaction,
        options: { institutionId: transaction.institutionId }
      }, {
        headers: { 'X-Institution-ID': transaction.institutionId }
      })
    );

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
      events.forEach((event: any) => {
        expect(event.institutionId).toBe(institution);
      });
    }
  }, 45000);

  test('High-volume concurrent processing', async () => {
    const transactionCount = 100;
    const maxConcurrency = 20;

    console.log(`Testing high-volume processing: ${transactionCount} transactions`);

    const { results, throughput, avgLatency } = await TestUtilities.measureThroughput(
      async (index) => {
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
      },
      transactionCount,
      maxConcurrency
    );

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
    const validAnalyses = fraudAnalyses.filter(r => 
      r.fraudProbability >= 0 && r.fraudProbability <= 1
    );
    const qualityRate = (validAnalyses.length / fraudAnalyses.length) * 100;
    expect(qualityRate).toBeGreaterThan(config.performanceThresholds.minAccuracy * 100);
  }, 120000); // 2 minute timeout for high-volume test
});

// Performance and stress tests
describe('Performance Validation', () => {
  test('Latency requirements compliance', async () => {
    const testCount = 50;
    const latencies: number[] = [];

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

    console.log(`Testing system stability: ${targetTps} TPS for ${duration/1000} seconds`);

    const startTime = Date.now();
    const results: Array<{ success: boolean; latency: number; timestamp: number }> = [];

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

      } catch (error) {
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
    return new Promise<void>((resolve, reject) => {
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
        } catch (error) {
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
    const allTransactions: any[] = [];

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

      } catch (error) {
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
      } catch (error) {
        auditVerifications.push({
          institutionId,
          success: false,
          error: error instanceof Error ? error.message : 'Unknown error'
        });
      }
    }

    // Calculate overall success metrics
    const totalTransactions = pipelineResults.length;
    const successfulPipelines = pipelineResults.filter(r => 
      r.fraudAnalysisSuccess && r.auditEventSuccess && r.mcpQuerySuccess
    ).length;
    const successRate = (successfulPipelines / totalTransactions) * 100;

    const validFraudAnalyses = pipelineResults.filter(r => 
      r.fraudAnalysisSuccess && 
      r.fraudProbability >= 0 && 
      r.fraudProbability <= 1 &&
      ['approve', 'reject', 'review'].includes(r.decision)
    ).length;
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
      const institutionSuccessRate = (institutionResults.filter(r => 
        r.fraudAnalysisSuccess && r.auditEventSuccess && r.mcpQuerySuccess
      ).length / institutionResults.length) * 100;

      expect(institutionSuccessRate).toBeGreaterThan(config.performanceThresholds.minAvailability);
    });

    console.log('✅ Complete system integration verification PASSED');
  }, 180000); // 3 minute timeout for comprehensive test
});

export default {};
