// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Request, Response, NextFunction } from 'express';
import axios from 'axios';

/**
 * Cache invalidation configuration
 */
interface CacheConfig {
  webhookUrl: string;
  regions: string[];
  timeout: number;
}

/**
 * Cache invalidation service
 */
export class CacheInvalidationService {
  private config: CacheConfig;
  private axiosInstance: any;

  constructor(config: CacheConfig) {
    this.config = config;
    this.axiosInstance = axios.create({
      timeout: config.timeout || 5000,
      headers: {
        'Content-Type': 'application/json',
        'User-Agent': 'Provability-Fabric-Ledger/1.0'
      }
    });
  }

  /**
   * Invalidate cache for specific keys across all regions
   */
  async invalidateCache(keys: string[]): Promise<void> {
    const invalidationPromises = this.config.regions.map(region => 
      this.invalidateRegion(region, keys)
    );

    try {
      await Promise.allSettled(invalidationPromises);
    } catch (error) {
      console.error('Cache invalidation failed:', error);
      // Don't throw - cache invalidation should not block the main operation
    }
  }

  /**
   * Invalidate cache for a specific region
   */
  private async invalidateRegion(region: string, keys: string[]): Promise<void> {
    const webhookUrl = `${this.config.webhookUrl}/${region}/webhook/cache-invalidate`;
    
    try {
      const response = await this.axiosInstance.post(webhookUrl, { keys });
      
      if (response.status === 200) {
        console.log(`Cache invalidated for region ${region}:`, response.data);
      } else {
        console.warn(`Cache invalidation failed for region ${region}:`, response.status);
      }
    } catch (error) {
      console.error(`Cache invalidation error for region ${region}:`, error);
    }
  }

  /**
   * Invalidate quote cache
   */
  async invalidateQuoteCache(capsuleHash: string): Promise<void> {
    const keys = [`quote:?capsule_hash=${capsuleHash}`];
    await this.invalidateCache(keys);
  }

  /**
   * Invalidate capsule cache
   */
  async invalidateCapsuleCache(capsuleHash: string): Promise<void> {
    const keys = [`capsule:/capsule/${capsuleHash}`];
    await this.invalidateCache(keys);
  }
}

/**
 * Express middleware for cache invalidation
 */
export function cacheInvalidationMiddleware(cacheService: CacheInvalidationService) {
  return async (req: Request, res: Response, next: NextFunction) => {
    // Store original send method
    const originalSend = res.send;
    
    // Override send method to trigger cache invalidation
    res.send = function(body: any) {
      // Call original send
      const result = originalSend.call(this, body);
      
      // Trigger cache invalidation based on the endpoint
      if (req.method === 'POST' || req.method === 'PUT' || req.method === 'DELETE') {
        const capsuleHash = req.params.capsuleHash || req.body?.capsule_hash;
        
        if (capsuleHash) {
          // Invalidate cache asynchronously
          cacheService.invalidateCapsuleCache(capsuleHash).catch(error => {
            console.error('Cache invalidation failed:', error);
          });
        }
      }
      
      return result;
    };
    
    next();
  };
}

/**
 * Cache invalidation for specific events
 */
export class CacheEventInvalidator {
  private cacheService: CacheInvalidationService;

  constructor(cacheService: CacheInvalidationService) {
    this.cacheService = cacheService;
  }

  /**
   * Handle capsule creation event
   */
  async onCapsuleCreated(capsuleHash: string): Promise<void> {
    await this.cacheService.invalidateCapsuleCache(capsuleHash);
  }

  /**
   * Handle capsule update event
   */
  async onCapsuleUpdated(capsuleHash: string): Promise<void> {
    await this.cacheService.invalidateCapsuleCache(capsuleHash);
    await this.cacheService.invalidateQuoteCache(capsuleHash);
  }

  /**
   * Handle quote creation event
   */
  async onQuoteCreated(capsuleHash: string): Promise<void> {
    await this.cacheService.invalidateQuoteCache(capsuleHash);
  }

  /**
   * Handle bulk cache invalidation
   */
  async invalidateBulk(keys: string[]): Promise<void> {
    await this.cacheService.invalidateCache(keys);
  }
}

/**
 * Default cache configuration
 */
export const defaultCacheConfig: CacheConfig = {
  webhookUrl: process.env.CACHE_WEBHOOK_URL || 'https://api.provability-fabric.org',
  regions: [
    'us-west',
    'us-east', 
    'eu-west'
  ],
  timeout: 5000
};

/**
 * Create cache service instance
 */
export function createCacheService(config?: Partial<CacheConfig>): CacheInvalidationService {
  const finalConfig = { ...defaultCacheConfig, ...config };
  return new CacheInvalidationService(finalConfig);
}

/**
 * Create cache event invalidator
 */
export function createCacheEventInvalidator(cacheService?: CacheInvalidationService): CacheEventInvalidator {
  const service = cacheService || createCacheService();
  return new CacheEventInvalidator(service);
}