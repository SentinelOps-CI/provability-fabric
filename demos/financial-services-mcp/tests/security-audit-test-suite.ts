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
import { createHash, randomBytes } from 'crypto';

interface SecurityTestConfig {
  mcpServerUrl: string;
  fraudAgentUrl: string;
  auditServiceUrl: string;
  databaseUrl: string;
  redisUrl: string;
  securityTests: {
    maxSqlInjectionAttempts: number;
    maxXssAttempts: number;
    maxAuthBypassAttempts: number;
    maxDataLeakageTests: number;
  };
  auditRequirements: {
    mandatoryFields: string[];
    hashAlgorithm: string;
    maxChainVerificationTime: number;
    retentionRequirements: {
      minRetentionDays: number;
      maxQueryTimeMs: number;
    };
  };
}

const securityConfig: SecurityTestConfig = {
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
  private static dbPool: Pool;
  private static redisClient: ReturnType<typeof createClient>;
  
  static async setupSecurityEnvironment(): Promise<void> {
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
  
  static async cleanup(): Promise<void> {
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
  
  static generateSqlInjectionPayloads(): string[] {
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
  
  static generateXssPayloads(): string[] {
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
  
  static generateMaliciousTransactionData(): any[] {
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
  
  static async testDatabaseDirectAccess(): Promise<{
    canAccessOtherInstitutions: boolean;
    canModifyAuditTrail: boolean;
    canEscalatePrivileges: boolean;
    vulnerabilities: string[];
  }> {
    const vulnerabilities: string[] = [];
    
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
    } catch (error) {
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
    } catch (error) {
      // Error is expected - audit trail should be immutable
    }
    
    // Test 3: Try to escalate privileges
    let canEscalatePrivileges = false;
    try {
      await this.dbPool.query('CREATE USER malicious_user WITH SUPERUSER');
      canEscalatePrivileges = true;
      vulnerabilities.push('Can escalate database privileges');
    } catch (error) {
      // Error is expected - should not be able to create users
    }
    
    return {
      canAccessOtherInstitutions,
      canModifyAuditTrail,
      canEscalatePrivileges,
      vulnerabilities
    };
  }
  
  static calculateExpectedHash(event: any): string {
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
  private dbPool: Pool;
  
  constructor(dbPool: Pool) {
    this.dbPool = dbPool;
  }
  
  async validateAuditChainIntegrity(institutionId: string): Promise<{
    isValid: boolean;
    totalEvents: number;
    brokenChains: number;
    invalidHashes: number;
    missingFields: number;
    performanceMs: number;
  }> {
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
  
  async validateAuditRetention(): Promise<{
    meetsRetentionRequirements: boolean;
    oldestEventDays: number;
    totalEventCount: number;
    queryPerformanceMs: number;
  }> {
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
  
  async validateAuditImmutability(): Promise<{
    isImmutable: boolean;
    attemptedModifications: number;
    successfulModifications: number;
    auditTrailCompromised: boolean;
  }> {
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
    } catch (error) {
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
    } catch (error) {
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
    } catch (error) {
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
        } else {
          successfulInjections++;
          results.push({
            payload: transaction.fromAccount,
            blocked: false,
            response: response.data
          });
        }
        
      } catch (error) {
        // Error responses might indicate injection was blocked or caused system issues
        if (error.response?.status === 400) {
          blockedAttempts++;
          results.push({
            payload: transaction.fromAccount,
            blocked: true,
            response: 'Bad request - likely blocked'
          });
        } else {
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
        } else {
          sanitizedResponses++;
        }
        
      } catch (error) {
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
        const foreignEvents = events.filter((event: any) => event.institutionId !== institutionId);
        
        isolationResults.push({
          institutionId,
          ownEvents: events.filter((event: any) => event.institutionId === institutionId).length,
          foreignEvents: foreignEvents.length,
          isolated: foreignEvents.length === 0
        });
        
      } catch (error) {
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
  let auditValidator: AuditTrailValidator;
  
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
      } else {
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
