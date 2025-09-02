/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Comprehensive Audit Trail Service with Immutable Logging
 * Blockchain-inspired audit system for financial regulatory compliance
 */

import { createHash } from 'crypto';
import { Pool } from 'pg';
import { createClient } from 'redis';
import express from 'express';
import winston from 'winston';
import { performance } from 'perf_hooks';
import { EventEmitter } from 'events';

interface AuditTrailConfig {
  databaseUrl: string;
  redisUrl: string;
  port: number;
  blockchainEnabled: boolean;
  verificationIntervalMs: number;
  retentionDays: number;
  encryptionEnabled: boolean;
}

interface AuditEvent {
  id: string;
  timestamp: number;
  eventType: string;
  actorId: string;
  resourceId: string;
  action: string;
  details: Record<string, any>;
  institutionId: string;
  ipAddress?: string;
  userAgent?: string;
  sessionId?: string;
  correlationId?: string;
}

interface AuditBlock {
  id: string;
  timestamp: number;
  previousHash: string;
  merkleRoot: string;
  events: AuditEvent[];
  hash: string;
  signature?: string;
  validator: string;
}

interface VerificationResult {
  isValid: boolean;
  blockId: string;
  eventCount: number;
  errors: string[];
  verifiedAt: number;
  verificationTimeMs: number;
}

interface ComplianceReport {
  reportId: string;
  institutionId: string;
  reportType: string;
  periodStart: number;
  periodEnd: number;
  eventCount: number;
  complianceStatus: 'COMPLIANT' | 'WARNING' | 'VIOLATION';
  violations: ComplianceViolation[];
  generatedAt: number;
  hash: string;
}

interface ComplianceViolation {
  violationType: string;
  severity: 'LOW' | 'MEDIUM' | 'HIGH' | 'CRITICAL';
  description: string;
  eventIds: string[];
  detectedAt: number;
}

export class AuditTrailService extends EventEmitter {
  private config: AuditTrailConfig;
  private logger!: winston.Logger;
  private dbPool!: Pool;
  private redisClient!: ReturnType<typeof createClient>;
  private app!: express.Application;
  private auditChain: Map<string, string> = new Map(); // Institution -> Latest block hash
  private pendingEvents: Map<string, AuditEvent[]> = new Map(); // Institution -> Events
  private verificationQueue: Set<string> = new Set(); // Block IDs pending verification
  private performanceMetrics: Map<string, number[]> = new Map();

  constructor(config: AuditTrailConfig) {
    super();
    this.config = config;
    this.setupLogger();
    this.setupDatabase();
    this.setupRedis();
    this.setupExpress();
    this.startBackgroundProcesses();
  }

  private setupLogger(): void {
    this.logger = winston.createLogger({
      level: process.env.LOG_LEVEL || 'info',
      format: winston.format.combine(
        winston.format.timestamp(),
        winston.format.errors({ stack: true }),
        winston.format.json()
      ),
      transports: [
        new winston.transports.Console(),
        new winston.transports.File({ filename: 'audit-trail-service.log' }),
        new winston.transports.File({ 
          filename: 'audit-compliance.log', 
          level: 'warn' // Compliance violations and warnings
        })
      ]
    });
  }

  private setupDatabase(): void {
    this.dbPool = new Pool({
      connectionString: this.config.databaseUrl,
      max: 50,
      idleTimeoutMillis: 30000,
      connectionTimeoutMillis: 2000,
    });
  }

  private async setupRedis(): Promise<void> {
    this.redisClient = createClient({
      url: this.config.redisUrl,
      socket: {
        connectTimeout: 1000,
      }
    });

    this.redisClient.on('error', (err) => {
      this.logger.error('Redis Client Error', { error: err.message });
    });

    await this.redisClient.connect();
  }

  private setupExpress(): void {
    this.app = express();
    this.app.use(express.json({ limit: '10mb' }));

    // Request timing middleware
    this.app.use((req, res, next) => {
      const startTime = performance.now();
      res.on('finish', () => {
        const duration = performance.now() - startTime;
        this.recordMetric('http_request_duration', duration);
      });
      next();
    });

    // Create audit event endpoint
    this.app.post('/events', async (req, res) => {
      try {
        const auditEvent = await this.createAuditEvent(req.body);
        return res.status(201).json({
          eventId: auditEvent.id,
          hash: await this.calculateEventHash(auditEvent),
          timestamp: auditEvent.timestamp,
          status: 'created'
        });
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('Failed to create audit event', { error: errorMessage });
        return res.status(500).json({ error: 'Failed to create audit event', message: errorMessage });
      }
    });

    // Batch create audit events endpoint
    this.app.post('/events/batch', async (req, res) => {
      try {
        const { events } = req.body;
        
        if (!Array.isArray(events) || events.length === 0) {
          return res.status(400).json({ error: 'Events array is required and must not be empty' });
        }

        if (events.length > 1000) {
          return res.status(400).json({ error: 'Batch size too large: maximum 1000 events per batch' });
        }

        const results = await this.createAuditEventsBatch(events);
        
        return res.status(201).json({
          batchId: `batch_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
          eventsCreated: results.length,
          results
        });
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('Failed to create audit events batch', { error: errorMessage });
        return res.status(500).json({ error: 'Failed to create audit events batch', message: errorMessage });
      }
    });

    // Query audit events endpoint
    this.app.get('/events', async (req, res) => {
      try {
        const {
          institutionId,
          eventType,
          actorId,
          resourceId,
          startTime,
          endTime,
          limit = 100,
          offset = 0
        } = req.query;

        const events = await this.queryAuditEvents({
          institutionId: institutionId as string,
          eventType: eventType as string,
          actorId: actorId as string,
          resourceId: resourceId as string,
          startTime: startTime ? parseInt(startTime as string) : undefined,
          endTime: endTime ? parseInt(endTime as string) : undefined,
          limit: parseInt(limit as string),
          offset: parseInt(offset as string)
        });

        return res.json({
          events,
          count: events.length,
          hasMore: events.length === parseInt(limit as string),
          queryTime: Date.now()
        });
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('Failed to query audit events', { error: errorMessage });
        return res.status(500).json({ error: 'Failed to query audit events', message: errorMessage });
      }
    });

    // Verify audit trail integrity endpoint
    this.app.post('/verify', async (req, res) => {
      try {
        const { institutionId, blockId, startTime, endTime } = req.body;
        
        const result = await this.verifyAuditTrailIntegrity({
          institutionId,
          blockId,
          startTime,
          endTime
        });

        return res.json(result);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('Failed to verify audit trail', { error: errorMessage });
        return res.status(500).json({ error: 'Failed to verify audit trail', message: errorMessage });
      }
    });

    // Generate compliance report endpoint
    this.app.post('/compliance/report', async (req, res) => {
      try {
        const { institutionId, reportType, periodStart, periodEnd } = req.body;
        
        const report = await this.generateComplianceReport({
          institutionId,
          reportType,
          periodStart,
          periodEnd
        });

        return res.json(report);
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('Failed to generate compliance report', { error: errorMessage });
        return res.status(500).json({ error: 'Failed to generate compliance report', message: errorMessage });
      }
    });

    // Get audit blocks endpoint
    this.app.get('/blocks', async (req, res) => {
      try {
        const { institutionId, limit = 50, offset = 0 } = req.query;
        
        const blocks = await this.getAuditBlocks({
          institutionId: institutionId as string,
          limit: parseInt(limit as string),
          offset: parseInt(offset as string)
        });

        return res.json({
          blocks,
          count: blocks.length,
          hasMore: blocks.length === parseInt(limit as string)
        });
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : 'Unknown error';
        this.logger.error('Failed to get audit blocks', { error: errorMessage });
        return res.status(500).json({ error: 'Failed to get audit blocks', message: errorMessage });
      }
    });

    // Get service statistics endpoint
    this.app.get('/stats', (req, res) => {
      const stats = this.getServiceStatistics();
      res.json(stats);
    });

    // Performance metrics endpoint
    this.app.get('/metrics', (req, res) => {
      const metrics: Record<string, any> = {};
      
      for (const [key, values] of this.performanceMetrics.entries()) {
        const sortedValues = values.sort((a, b) => a - b);
        const len = sortedValues.length;
        
        metrics[key] = {
          count: len,
          min: len > 0 ? sortedValues[0] : 0,
          max: len > 0 ? sortedValues[len - 1] : 0,
          p50: len > 0 ? sortedValues[Math.floor(len * 0.5)] : 0,
          p95: len > 0 ? sortedValues[Math.floor(len * 0.95)] : 0,
          p99: len > 0 ? sortedValues[Math.floor(len * 0.99)] : 0,
          avg: len > 0 ? values.reduce((a, b) => a + b, 0) / len : 0
        };
      }
      
      return res.json({
        performance: metrics,
        timestamp: Date.now()
      });
    });

    // Health check endpoint
    this.app.get('/health', async (req, res) => {
      try {
        // Check database connectivity
        await this.dbPool.query('SELECT 1');
        
        // Check Redis connectivity
        await this.redisClient.ping();

        return res.json({
          status: 'healthy',
          database: 'connected',
          redis: 'connected',
          blockchainEnabled: this.config.blockchainEnabled,
          uptime: process.uptime(),
          timestamp: Date.now()
        });
      } catch (error) {
        return res.status(503).json({
          status: 'unhealthy',
          error: error instanceof Error ? error.message : 'Unknown error',
          timestamp: Date.now()
        });
      }
    });
  }

  private startBackgroundProcesses(): void {
    // Block creation process
    if (this.config.blockchainEnabled) {
      setInterval(() => {
        this.createPendingBlocks().catch(error => {
          this.logger.error('Failed to create pending blocks', { error: error.message });
        });
      }, 10000); // Every 10 seconds
    }

    // Verification process
    setInterval(() => {
      this.runPeriodicVerification().catch(error => {
        this.logger.error('Failed to run periodic verification', { error: error.message });
      });
    }, this.config.verificationIntervalMs);

    // Cleanup process
    setInterval(() => {
      this.cleanupOldData().catch(error => {
        this.logger.error('Failed to cleanup old data', { error: error.message });
      });
    }, 60 * 60 * 1000); // Every hour
  }

  // Core audit event creation
  async createAuditEvent(eventData: Partial<AuditEvent>): Promise<AuditEvent> {
    const startTime = performance.now();

    try {
      const auditEvent: AuditEvent = {
        id: `audit_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        timestamp: Date.now(),
        eventType: eventData.eventType || 'unknown',
        actorId: eventData.actorId || 'system',
        resourceId: eventData.resourceId || '',
        action: eventData.action || 'unknown',
        details: eventData.details || {},
        institutionId: eventData.institutionId || 'default',
        ipAddress: eventData.ipAddress,
        userAgent: eventData.userAgent,
        sessionId: eventData.sessionId,
        correlationId: eventData.correlationId
      };

      // Store in database immediately for durability
      await this.storeAuditEvent(auditEvent);

      // Add to pending events for blockchain processing
      if (this.config.blockchainEnabled) {
        await this.addToPendingEvents(auditEvent);
      }

      // Cache recent events in Redis for fast access
      await this.cacheAuditEvent(auditEvent);

      // Emit event for real-time processing
      this.emit('auditEventCreated', auditEvent);

      const processingTime = performance.now() - startTime;
      this.recordMetric('audit_event_creation_duration', processingTime);

      this.logger.info('Audit event created', {
        eventId: auditEvent.id,
        eventType: auditEvent.eventType,
        institutionId: auditEvent.institutionId,
        processingTime: `${processingTime.toFixed(2)}ms`
      });

      return auditEvent;

    } catch (error) {
      this.logger.error('Failed to create audit event', {
        error: error instanceof Error ? error.message : 'Unknown error',
        eventData
      });
      throw error;
    }
  }

  async createAuditEventsBatch(eventsData: Partial<AuditEvent>[]): Promise<AuditEvent[]> {
    const startTime = performance.now();

    try {
      const auditEvents: AuditEvent[] = eventsData.map(eventData => ({
        id: `audit_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        timestamp: Date.now(),
        eventType: eventData.eventType || 'unknown',
        actorId: eventData.actorId || 'system',
        resourceId: eventData.resourceId || '',
        action: eventData.action || 'unknown',
        details: eventData.details || {},
        institutionId: eventData.institutionId || 'default',
        ipAddress: eventData.ipAddress,
        userAgent: eventData.userAgent,
        sessionId: eventData.sessionId,
        correlationId: eventData.correlationId
      }));

      // Batch insert into database
      await this.storeAuditEventsBatch(auditEvents);

      // Add to pending events for blockchain processing
      if (this.config.blockchainEnabled) {
        for (const event of auditEvents) {
          await this.addToPendingEvents(event);
        }
      }

      // Cache events in Redis
      for (const event of auditEvents) {
        await this.cacheAuditEvent(event);
      }

      // Emit batch event
      this.emit('auditEventsBatchCreated', auditEvents);

      const processingTime = performance.now() - startTime;
      this.recordMetric('audit_batch_creation_duration', processingTime);

      this.logger.info('Audit events batch created', {
        batchSize: auditEvents.length,
        processingTime: `${processingTime.toFixed(2)}ms`
      });

      return auditEvents;

    } catch (error) {
      this.logger.error('Failed to create audit events batch', {
        error: error instanceof Error ? error.message : 'Unknown error',
        batchSize: eventsData.length
      });
      throw error;
    }
  }

  // Database operations
  private async storeAuditEvent(event: AuditEvent): Promise<void> {
    const query = `
      INSERT INTO audit_events (
        id, timestamp, event_type, actor_id, resource_id, action, details, 
        institution_id, ip_address, user_agent, session_id, correlation_id, hash
      ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13)
    `;

    const hash = await this.calculateEventHash(event);

    await this.dbPool.query(query, [
      event.id,
      event.timestamp,
      event.eventType,
      event.actorId,
      event.resourceId,
      event.action,
      JSON.stringify(event.details),
      event.institutionId,
      event.ipAddress,
      event.userAgent,
      event.sessionId,
      event.correlationId,
      hash
    ]);
  }

  private async storeAuditEventsBatch(events: AuditEvent[]): Promise<void> {
    if (events.length === 0) return;

    const values = [];
    const placeholders = [];
    let paramIndex = 1;

    for (const event of events) {
      const hash = await this.calculateEventHash(event);
      
      values.push(
        event.id,
        event.timestamp,
        event.eventType,
        event.actorId,
        event.resourceId,
        event.action,
        JSON.stringify(event.details),
        event.institutionId,
        event.ipAddress,
        event.userAgent,
        event.sessionId,
        event.correlationId,
        hash
      );

      placeholders.push(
        `($${paramIndex}, $${paramIndex + 1}, $${paramIndex + 2}, $${paramIndex + 3}, ` +
        `$${paramIndex + 4}, $${paramIndex + 5}, $${paramIndex + 6}, $${paramIndex + 7}, ` +
        `$${paramIndex + 8}, $${paramIndex + 9}, $${paramIndex + 10}, $${paramIndex + 11}, $${paramIndex + 12})`
      );

      paramIndex += 13;
    }

    const query = `
      INSERT INTO audit_events (
        id, timestamp, event_type, actor_id, resource_id, action, details, 
        institution_id, ip_address, user_agent, session_id, correlation_id, hash
      ) VALUES ${placeholders.join(', ')}
    `;

    await this.dbPool.query(query, values);
  }

  async queryAuditEvents(filters: {
    institutionId?: string;
    eventType?: string;
    actorId?: string;
    resourceId?: string;
    startTime?: number;
    endTime?: number;
    limit: number;
    offset: number;
  }): Promise<AuditEvent[]> {
    const conditions = [];
    const params = [];
    let paramIndex = 1;

    if (filters.institutionId) {
      conditions.push(`institution_id = $${paramIndex++}`);
      params.push(filters.institutionId);
    }

    if (filters.eventType) {
      conditions.push(`event_type = $${paramIndex++}`);
      params.push(filters.eventType);
    }

    if (filters.actorId) {
      conditions.push(`actor_id = $${paramIndex++}`);
      params.push(filters.actorId);
    }

    if (filters.resourceId) {
      conditions.push(`resource_id = $${paramIndex++}`);
      params.push(filters.resourceId);
    }

    if (filters.startTime) {
      conditions.push(`timestamp >= $${paramIndex++}`);
      params.push(filters.startTime);
    }

    if (filters.endTime) {
      conditions.push(`timestamp <= $${paramIndex++}`);
      params.push(filters.endTime);
    }

    const whereClause = conditions.length > 0 ? `WHERE ${conditions.join(' AND ')}` : '';

    const query = `
      SELECT id, timestamp, event_type, actor_id, resource_id, action, details,
             institution_id, ip_address, user_agent, session_id, correlation_id
      FROM audit_events
      ${whereClause}
      ORDER BY timestamp DESC
      LIMIT $${paramIndex++} OFFSET $${paramIndex++}
    `;

    params.push(filters.limit, filters.offset);

    const result = await this.dbPool.query(query, params);

    return result.rows.map(row => ({
      id: row.id,
      timestamp: row.timestamp,
      eventType: row.event_type,
      actorId: row.actor_id,
      resourceId: row.resource_id,
      action: row.action,
      details: typeof row.details === 'string' ? JSON.parse(row.details) : row.details,
      institutionId: row.institution_id,
      ipAddress: row.ip_address,
      userAgent: row.user_agent,
      sessionId: row.session_id,
      correlationId: row.correlation_id
    }));
  }

  // Blockchain-inspired audit trail operations
  private async addToPendingEvents(event: AuditEvent): Promise<void> {
    const institutionEvents = this.pendingEvents.get(event.institutionId) || [];
    institutionEvents.push(event);
    this.pendingEvents.set(event.institutionId, institutionEvents);

    // Create block when we have enough events (or after timeout)
    if (institutionEvents.length >= 100) {
      await this.createAuditBlock(event.institutionId);
    }
  }

  private async createPendingBlocks(): Promise<void> {
    for (const [institutionId, events] of this.pendingEvents.entries()) {
      if (events.length > 0) {
        await this.createAuditBlock(institutionId);
      }
    }
  }

  private async createAuditBlock(institutionId: string): Promise<AuditBlock> {
    const startTime = performance.now();

    try {
      const events = this.pendingEvents.get(institutionId) || [];
      if (events.length === 0) {
        throw new Error('No pending events for institution');
      }

      const previousHash = this.auditChain.get(institutionId) || '0';
      const merkleRoot = await this.calculateMerkleRoot(events);

      const block: AuditBlock = {
        id: `block_${institutionId}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        timestamp: Date.now(),
        previousHash,
        merkleRoot,
        events: [...events], // Copy events
        hash: '', // Will be calculated
        validator: 'audit-trail-service',
        signature: undefined
      };

      // Calculate block hash
      block.hash = await this.calculateBlockHash(block);

      // Store block in database
      await this.storeAuditBlock(block);

      // Update audit chain
      this.auditChain.set(institutionId, block.hash);

      // Clear pending events
      this.pendingEvents.set(institutionId, []);

      // Add to verification queue
      this.verificationQueue.add(block.id);

      const processingTime = performance.now() - startTime;
      this.recordMetric('block_creation_duration', processingTime);

      this.logger.info('Audit block created', {
        blockId: block.id,
        institutionId,
        eventCount: events.length,
        previousHash,
        hash: block.hash,
        processingTime: `${processingTime.toFixed(2)}ms`
      });

      this.emit('auditBlockCreated', block);

      return block;

    } catch (error) {
      this.logger.error('Failed to create audit block', {
        institutionId,
        error: error instanceof Error ? error.message : 'Unknown error'
      });
      throw error;
    }
  }

  private async storeAuditBlock(block: AuditBlock): Promise<void> {
    const query = `
      INSERT INTO audit_blocks (
        id, timestamp, previous_hash, merkle_root, events, hash, signature, validator, institution_id
      ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
    `;

    await this.dbPool.query(query, [
      block.id,
      block.timestamp,
      block.previousHash,
      block.merkleRoot,
      JSON.stringify(block.events),
      block.hash,
      block.signature,
      block.validator,
      block.events[0]?.institutionId || 'unknown'
    ]);
  }

  private async getAuditBlocks(filters: {
    institutionId?: string;
    limit: number;
    offset: number;
  }): Promise<AuditBlock[]> {
    const conditions = [];
    const params = [];
    let paramIndex = 1;

    if (filters.institutionId) {
      conditions.push(`institution_id = $${paramIndex++}`);
      params.push(filters.institutionId);
    }

    const whereClause = conditions.length > 0 ? `WHERE ${conditions.join(' AND ')}` : '';

    const query = `
      SELECT id, timestamp, previous_hash, merkle_root, events, hash, signature, validator
      FROM audit_blocks
      ${whereClause}
      ORDER BY timestamp DESC
      LIMIT $${paramIndex++} OFFSET $${paramIndex++}
    `;

    params.push(filters.limit, filters.offset);

    const result = await this.dbPool.query(query, params);

    return result.rows.map(row => ({
      id: row.id,
      timestamp: row.timestamp,
      previousHash: row.previous_hash,
      merkleRoot: row.merkle_root,
      events: typeof row.events === 'string' ? JSON.parse(row.events) : row.events,
      hash: row.hash,
      signature: row.signature,
      validator: row.validator
    }));
  }

  // Verification and integrity checking
  async verifyAuditTrailIntegrity(params: {
    institutionId?: string;
    blockId?: string;
    startTime?: number;
    endTime?: number;
  }): Promise<VerificationResult> {
    const startTime = performance.now();

    try {
      let blocks: AuditBlock[];

      if (params.blockId) {
        // Verify specific block
        const result = await this.dbPool.query(
          'SELECT * FROM audit_blocks WHERE id = $1',
          [params.blockId]
        );
        
        if (result.rows.length === 0) {
          throw new Error(`Block not found: ${params.blockId}`);
        }

        blocks = [result.rows[0]];
      } else {
        // Verify blocks by institution and time range
        blocks = await this.getAuditBlocks({
          institutionId: params.institutionId,
          limit: 1000,
          offset: 0
        });
      }

      const errors: string[] = [];
      let totalEvents = 0;

      for (const block of blocks) {
        totalEvents += block.events.length;

        // Verify block hash
        const expectedHash = await this.calculateBlockHash(block);
        if (block.hash !== expectedHash) {
          errors.push(`Block ${block.id}: Hash mismatch (expected: ${expectedHash}, actual: ${block.hash})`);
        }

        // Verify merkle root
        const expectedMerkleRoot = await this.calculateMerkleRoot(block.events);
        if (block.merkleRoot !== expectedMerkleRoot) {
          errors.push(`Block ${block.id}: Merkle root mismatch`);
        }

        // Verify event hashes
        for (const event of block.events) {
          const expectedEventHash = await this.calculateEventHash(event);
          // Check against stored hash if available
          const storedEvent = await this.dbPool.query(
            'SELECT hash FROM audit_events WHERE id = $1',
            [event.id]
          );
          
          if (storedEvent.rows.length > 0 && storedEvent.rows[0].hash !== expectedEventHash) {
            errors.push(`Event ${event.id}: Hash mismatch`);
          }
        }
      }

      const verificationTime = performance.now() - startTime;
      this.recordMetric('verification_duration', verificationTime);

      const result: VerificationResult = {
        isValid: errors.length === 0,
        blockId: params.blockId || `${blocks.length} blocks`,
        eventCount: totalEvents,
        errors,
        verifiedAt: Date.now(),
        verificationTimeMs: verificationTime
      };

      this.logger.info('Audit trail verification completed', {
        isValid: result.isValid,
        blocksVerified: blocks.length,
        eventsVerified: totalEvents,
        errorsFound: errors.length,
        verificationTime: `${verificationTime.toFixed(2)}ms`
      });

      return result;

    } catch (error) {
      this.logger.error('Audit trail verification failed', {
        error: error instanceof Error ? error.message : 'Unknown error',
        params
      });
      throw error;
    }
  }

  private async runPeriodicVerification(): Promise<void> {
    try {
      // Verify recent blocks
      const oneDayAgo = Date.now() - (24 * 60 * 60 * 1000);
      
      const result = await this.verifyAuditTrailIntegrity({
        startTime: oneDayAgo,
        endTime: Date.now()
      });

      if (!result.isValid) {
        this.logger.error('Periodic verification failed', {
          errors: result.errors,
          eventCount: result.eventCount
        });
        
        this.emit('verificationFailed', result);
      } else {
        this.logger.info('Periodic verification passed', {
          eventCount: result.eventCount,
          verificationTime: `${result.verificationTimeMs.toFixed(2)}ms`
        });
      }

    } catch (error) {
      this.logger.error('Periodic verification error', {
        error: error instanceof Error ? error.message : 'Unknown error'
      });
    }
  }

  // Compliance reporting
  async generateComplianceReport(params: {
    institutionId: string;
    reportType: string;
    periodStart: number;
    periodEnd: number;
  }): Promise<ComplianceReport> {
    const startTime = performance.now();

    try {
      // Query events for the period
      const events = await this.queryAuditEvents({
        institutionId: params.institutionId,
        startTime: params.periodStart,
        endTime: params.periodEnd,
        limit: 10000,
        offset: 0
      });

      // Analyze events for compliance violations
      const violations = await this.analyzeComplianceViolations(events, params.reportType);

      const complianceStatus: 'COMPLIANT' | 'WARNING' | 'VIOLATION' = 
        violations.filter(v => v.severity === 'CRITICAL').length > 0 ? 'VIOLATION' :
        violations.filter(v => v.severity === 'HIGH').length > 0 ? 'WARNING' : 'COMPLIANT';

      const report: ComplianceReport = {
        reportId: `compliance_${params.institutionId}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        institutionId: params.institutionId,
        reportType: params.reportType,
        periodStart: params.periodStart,
        periodEnd: params.periodEnd,
        eventCount: events.length,
        complianceStatus,
        violations,
        generatedAt: Date.now(),
        hash: '' // Will be calculated
      };

      // Calculate report hash for integrity
      report.hash = await this.calculateReportHash(report);

      // Store compliance report
      await this.storeComplianceReport(report);

      const processingTime = performance.now() - startTime;
      this.recordMetric('compliance_report_generation_duration', processingTime);

      this.logger.info('Compliance report generated', {
        reportId: report.reportId,
        institutionId: params.institutionId,
        reportType: params.reportType,
        eventCount: events.length,
        violationsFound: violations.length,
        complianceStatus,
        processingTime: `${processingTime.toFixed(2)}ms`
      });

      if (complianceStatus !== 'COMPLIANT') {
        this.emit('complianceViolation', report);
      }

      return report;

    } catch (error) {
      this.logger.error('Compliance report generation failed', {
        error: error instanceof Error ? error.message : 'Unknown error',
        params
      });
      throw error;
    }
  }

  private async analyzeComplianceViolations(events: AuditEvent[], reportType: string): Promise<ComplianceViolation[]> {
    const violations: ComplianceViolation[] = [];

    switch (reportType) {
      case 'SOX_COMPLIANCE':
        violations.push(...await this.analyzeSoxCompliance(events));
        break;
        
      case 'PCI_DSS':
        violations.push(...await this.analyzePciDssCompliance(events));
        break;
        
      case 'BASEL_III':
        violations.push(...await this.analyzeBaselIiiCompliance(events));
        break;
        
      default:
        violations.push(...await this.analyzeGeneralCompliance(events));
    }

    return violations;
  }

  private async analyzeSoxCompliance(events: AuditEvent[]): Promise<ComplianceViolation[]> {
    const violations: ComplianceViolation[] = [];

    // Check for missing audit trails on financial operations
    const financialEvents = events.filter(e => 
      e.eventType.includes('financial') || 
      e.eventType.includes('transaction') ||
      e.action.includes('transfer')
    );

    if (financialEvents.length === 0) {
      violations.push({
        violationType: 'MISSING_FINANCIAL_AUDIT_TRAIL',
        severity: 'HIGH',
        description: 'No financial operations found in audit trail - potential SOX compliance issue',
        eventIds: [],
        detectedAt: Date.now()
      });
    }

    // Check for unauthorized system access
    const systemEvents = events.filter(e => 
      e.eventType === 'system_access' && 
      e.details.authorized === false
    );

    if (systemEvents.length > 0) {
      violations.push({
        violationType: 'UNAUTHORIZED_SYSTEM_ACCESS',
        severity: 'CRITICAL',
        description: `${systemEvents.length} unauthorized system access attempts detected`,
        eventIds: systemEvents.map(e => e.id),
        detectedAt: Date.now()
      });
    }

    return violations;
  }

  private async analyzePciDssCompliance(events: AuditEvent[]): Promise<ComplianceViolation[]> {
    const violations: ComplianceViolation[] = [];

    // Check for payment card data access
    const cardDataEvents = events.filter(e => 
      e.details.cardNumber || 
      e.details.cardData ||
      e.resourceId.includes('card')
    );

    for (const event of cardDataEvents) {
      if (!event.details.encrypted) {
        violations.push({
          violationType: 'UNENCRYPTED_CARD_DATA_ACCESS',
          severity: 'CRITICAL',
          description: 'Payment card data accessed without encryption',
          eventIds: [event.id],
          detectedAt: Date.now()
        });
      }
    }

    return violations;
  }

  private async analyzeBaselIiiCompliance(events: AuditEvent[]): Promise<ComplianceViolation[]> {
    const violations: ComplianceViolation[] = [];

    // Check for capital adequacy ratio violations
    const capitalEvents = events.filter(e => 
      e.eventType === 'capital_calculation' ||
      e.details.capitalRatio
    );

    for (const event of capitalEvents) {
      if (event.details.capitalRatio && event.details.capitalRatio < 0.08) {
        violations.push({
          violationType: 'CAPITAL_ADEQUACY_VIOLATION',
          severity: 'HIGH',
          description: `Capital adequacy ratio below Basel III requirement: ${event.details.capitalRatio}`,
          eventIds: [event.id],
          detectedAt: Date.now()
        });
      }
    }

    return violations;
  }

  private async analyzeGeneralCompliance(events: AuditEvent[]): Promise<ComplianceViolation[]> {
    const violations: ComplianceViolation[] = [];

    // Check for failed operations without proper logging
    const failedEvents = events.filter(e => 
      e.details.status === 'failed' &&
      (!e.details.reason || !e.details.errorCode)
    );

    if (failedEvents.length > 0) {
      violations.push({
        violationType: 'INCOMPLETE_ERROR_LOGGING',
        severity: 'MEDIUM',
        description: `${failedEvents.length} failed operations without complete error information`,
        eventIds: failedEvents.map(e => e.id),
        detectedAt: Date.now()
      });
    }

    return violations;
  }

  private async storeComplianceReport(report: ComplianceReport): Promise<void> {
    const query = `
      INSERT INTO compliance_reports (
        id, institution_id, report_type, period_start, period_end, event_count,
        compliance_status, violations, generated_at, hash
      ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
    `;

    await this.dbPool.query(query, [
      report.reportId,
      report.institutionId,
      report.reportType,
      report.periodStart,
      report.periodEnd,
      report.eventCount,
      report.complianceStatus,
      JSON.stringify(report.violations),
      report.generatedAt,
      report.hash
    ]);
  }

  // Caching operations
  private async cacheAuditEvent(event: AuditEvent): Promise<void> {
    const key = `audit_event:${event.id}`;
    await this.redisClient.setEx(key, 3600, JSON.stringify(event)); // Cache for 1 hour
  }

  // Hash calculation methods
  private async calculateEventHash(event: AuditEvent): Promise<string> {
    const data = JSON.stringify({
      id: event.id,
      timestamp: event.timestamp,
      eventType: event.eventType,
      actorId: event.actorId,
      resourceId: event.resourceId,
      action: event.action,
      details: event.details,
      institutionId: event.institutionId
    });
    
    return createHash('sha256').update(data).digest('hex');
  }

  private async calculateBlockHash(block: Omit<AuditBlock, 'hash'>): Promise<string> {
    const data = JSON.stringify({
      id: block.id,
      timestamp: block.timestamp,
      previousHash: block.previousHash,
      merkleRoot: block.merkleRoot,
      validator: block.validator
    });
    
    return createHash('sha256').update(data).digest('hex');
  }

  private async calculateMerkleRoot(events: AuditEvent[]): Promise<string> {
    if (events.length === 0) {
      return createHash('sha256').update('').digest('hex');
    }

    let hashes = await Promise.all(events.map(event => this.calculateEventHash(event)));

    while (hashes.length > 1) {
      const newHashes: string[] = [];
      
      for (let i = 0; i < hashes.length; i += 2) {
        const left = hashes[i];
        const right = i + 1 < hashes.length ? hashes[i + 1] : left;
        const combined = createHash('sha256').update(left + right).digest('hex');
        newHashes.push(combined);
      }
      
      hashes = newHashes;
    }

    return hashes[0];
  }

  private async calculateReportHash(report: Omit<ComplianceReport, 'hash'>): Promise<string> {
    const data = JSON.stringify({
      reportId: report.reportId,
      institutionId: report.institutionId,
      reportType: report.reportType,
      periodStart: report.periodStart,
      periodEnd: report.periodEnd,
      eventCount: report.eventCount,
      complianceStatus: report.complianceStatus,
      violations: report.violations,
      generatedAt: report.generatedAt
    });
    
    return createHash('sha256').update(data).digest('hex');
  }

  // Cleanup and maintenance
  private async cleanupOldData(): Promise<void> {
    try {
      const cutoffTime = Date.now() - (this.config.retentionDays * 24 * 60 * 60 * 1000);

      // Clean up old audit events
      const eventsResult = await this.dbPool.query(
        'DELETE FROM audit_events WHERE timestamp < $1',
        [cutoffTime]
      );

      // Clean up old blocks
      const blocksResult = await this.dbPool.query(
        'DELETE FROM audit_blocks WHERE timestamp < $1',
        [cutoffTime]
      );

      this.logger.info('Old data cleanup completed', {
        eventsDeleted: eventsResult.rowCount,
        blocksDeleted: blocksResult.rowCount,
        cutoffTime: new Date(cutoffTime).toISOString()
      });

    } catch (error) {
      this.logger.error('Data cleanup failed', {
        error: error instanceof Error ? error.message : 'Unknown error'
      });
    }
  }

  // Utility methods
  private getServiceStatistics(): any {
    return {
      pendingEventsCount: Array.from(this.pendingEvents.values()).reduce((sum, events) => sum + events.length, 0),
      verificationQueueSize: this.verificationQueue.size,
      auditChainLength: this.auditChain.size,
      uptime: process.uptime(),
      memoryUsage: process.memoryUsage(),
      timestamp: Date.now()
    };
  }

  private recordMetric(metricName: string, value: number): void {
    if (!this.performanceMetrics.has(metricName)) {
      this.performanceMetrics.set(metricName, []);
    }
    
    const metrics = this.performanceMetrics.get(metricName)!;
    metrics.push(value);
    
    // Keep only last 1000 measurements
    if (metrics.length > 1000) {
      metrics.splice(0, metrics.length - 1000);
    }
  }

  // Server lifecycle methods
  async start(): Promise<void> {
    this.app.listen(this.config.port, () => {
      this.logger.info(`Audit Trail Service started on port ${this.config.port}`, {
        blockchainEnabled: this.config.blockchainEnabled,
        encryptionEnabled: this.config.encryptionEnabled,
        retentionDays: this.config.retentionDays
      });
    });
  }

  async stop(): Promise<void> {
    await this.redisClient.quit();
    await this.dbPool.end();
    
    this.logger.info('Audit Trail Service stopped');
  }
}

// Service configuration and startup
const config: AuditTrailConfig = {
  databaseUrl: process.env.DATABASE_URL || 'postgresql://fintech_user:secure_fintech_2025@localhost:5433/financial_services',
  redisUrl: process.env.REDIS_URL || 'redis://localhost:6380',
  port: parseInt(process.env.PORT || '8083'),
  blockchainEnabled: process.env.BLOCKCHAIN_ENABLED !== 'false',
  verificationIntervalMs: parseInt(process.env.VERIFICATION_INTERVAL_MS || '60000'),
  retentionDays: parseInt(process.env.RETENTION_DAYS || '2555'), // 7 years default
  encryptionEnabled: process.env.ENCRYPTION_ENABLED === 'true'
};

// Start the service
if (require.main === module) {
  const service = new AuditTrailService(config);
  
  service.start().catch((error) => {
    console.error('Failed to start Audit Trail Service:', error);
    process.exit(1);
  });

  // Graceful shutdown
  process.on('SIGINT', async () => {
    console.log('Shutting down Audit Trail Service...');
    await service.stop();
    process.exit(0);
  });
}
