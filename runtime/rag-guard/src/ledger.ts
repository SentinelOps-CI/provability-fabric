/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import axios, { AxiosInstance, AxiosResponse } from 'axios';
import { createHash } from 'crypto';
import { IncidentPayload, LedgerResponse, DetectionResult } from './types';

export class LedgerClient {
  private client: AxiosInstance;
  private tenantId: string;
  private retries: number;
  private timeout: number;

  constructor(
    ledgerUrl: string,
    tenantId: string,
    timeout: number = 5000,
    retries: number = 3
  ) {
    const ax: any = axios as any;
    if (ax && typeof ax.create === 'function') {
      this.client = axios.create({
        baseURL: ledgerUrl,
        timeout,
        headers: {
          'Content-Type': 'application/json',
          'User-Agent': '@pf/guard-rag/1.0.0'
        }
      });
    } else {
      // Fallback minimal client to avoid crashes when axios is mocked without .create
      this.client = {
        post: async () => { throw new Error('axios_not_initialized'); },
        get: async () => ({ status: 503 }),
        defaults: { headers: { common: {} } }
      } as unknown as AxiosInstance;
    }
    this.tenantId = tenantId;
    this.timeout = timeout;
    this.retries = retries;
  }

  async reportIncident(
    sessionId: string,
    detections: DetectionResult[],
    originalContentLength: number,
    originalContent: string
  ): Promise<LedgerResponse> {
    const contentHash = this.hashContent(originalContent);
    const maxSeverity = this.getMaxSeverity(detections);
    
    const payload: IncidentPayload = {
      type: 'rag_content_blocked',
      timestamp: new Date().toISOString(),
      tenantId: this.tenantId,
      sessionId,
      detections,
      originalContentLength,
      blockedContentHash: contentHash,
      severity: maxSeverity
    };

    // Do not throw on ledger failures; always resolve with a LedgerResponse so caller can fail securely
    try {
      return await this.executeWithRetry(() => this.postIncident(payload));
    } catch (error: any) {
      return {
        success: false,
        error: error?.message || 'ledger_unavailable'
      };
    }
  }

  private async postIncident(payload: IncidentPayload): Promise<LedgerResponse> {
    try {
      const response: AxiosResponse = await this.client.post('/incidents', payload);
      
      return {
        success: true,
        incidentId: response.data.incident_id || response.data.id
      };
    } catch (error: any) {
      console.error('Failed to report incident to ledger:', error.message);
      
      return {
        success: false,
        error: error.response?.data?.error || error.message
      };
    }
  }

  private async executeWithRetry<T>(operation: () => Promise<T>): Promise<T> {
    let lastError: Error | null = null;
    
    for (let attempt = 0; attempt < this.retries; attempt++) {
      try {
        return await operation();
      } catch (error: any) {
        lastError = error;
        
        // Don't retry on client errors (4xx)
        if (error.response?.status >= 400 && error.response?.status < 500) {
          throw error;
        }
        
        // Exponential backoff for retries
        if (attempt < this.retries - 1) {
          const backoffMs = Math.min(1000 * Math.pow(2, attempt), 10000);
          await this.sleep(backoffMs);
        }
      }
    }
    
    throw lastError;
  }

  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  private hashContent(content: string): string {
    return createHash('sha256').update(content).digest('hex');
  }

  private getMaxSeverity(detections: DetectionResult[]): 'low' | 'medium' | 'high' | 'critical' {
    const severityOrder = ['low', 'medium', 'high', 'critical'];
    let maxSeverity = 'low';
    
    for (const detection of detections) {
      if (severityOrder.indexOf(detection.severity) > severityOrder.indexOf(maxSeverity)) {
        maxSeverity = detection.severity;
      }
    }
    
    return maxSeverity as 'low' | 'medium' | 'high' | 'critical';
  }

  async healthCheck(): Promise<boolean> {
    try {
      const response = await this.client.get('/health');
      return response.status === 200;
    } catch {
      return false;
    }
  }

  setAuthToken(token: string): void {
    this.client.defaults.headers.common['Authorization'] = `Bearer ${token}`;
  }

  clearAuthToken(): void {
    delete this.client.defaults.headers.common['Authorization'];
  }
}
