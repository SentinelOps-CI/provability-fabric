/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import { PIIDetector } from './detectors/pii';
import { SecretDetector } from './detectors/secrets';
import { LedgerClient } from './ledger';
import { GuardConfig, GuardResponse, DetectionResult } from './types';

export class RAGGuard {
  private piiDetector: PIIDetector;
  private secretDetector: SecretDetector;
  private ledgerClient: LedgerClient;
  private config: GuardConfig;
  private ledgerUrlValid: boolean;

  constructor(config: GuardConfig) {
    this.config = config;
    this.piiDetector = new PIIDetector(config.customPatterns?.pii);
    this.secretDetector = new SecretDetector(config.customPatterns?.secrets);
    this.ledgerUrlValid = /^https?:\/\//i.test(config.ledgerUrl);
    this.ledgerClient = new LedgerClient(
      config.ledgerUrl,
      config.tenantId,
      config.timeout,
      config.retries
    );
  }

  async filter(content: string): Promise<GuardResponse> {
    try {
      const detections = this.detectViolations(content);
      
      if (!this.ledgerUrlValid) {
        throw new Error('invalid_ledger_url');
      }

      if (detections.length === 0) {
        return {
          allowed: true,
          safeContent: content
        };
      }

      // Report incident to ledger
      const ledgerResponse = await this.ledgerClient.reportIncident(
        this.config.sessionId,
        detections,
        content.length,
        content
      );

      // If ledger could not record the incident, continue with redaction (fail-open on reporting)

      // Generate safe content by redacting detected patterns
      const safeContent = this.generateSafeContent(content, detections);

      return {
        allowed: false,
        safeContent,
        blockedDetections: detections,
        incidentId: ledgerResponse.success ? ledgerResponse.incidentId : undefined
      };
    } catch (error: any) {
      console.error('Error in RAG guard filter:', error.message);
      
      // Fail securely - block content if we can't process it properly
      return {
        allowed: false,
        safeContent: 'Content blocked due to processing error. Please try again.',
        blockedDetections: [],
        incidentId: undefined
      };
    }
  }

  private detectViolations(content: string): DetectionResult[] {
    const detections: DetectionResult[] = [];

    if (this.config.enablePII) {
      detections.push(...this.piiDetector.detect(content));
    }

    if (this.config.enableSecrets) {
      detections.push(...this.secretDetector.detect(content));
    }

    // Sort by position to handle overlapping detections
    return detections.sort((a, b) => a.position.start - b.position.start);
  }

  private generateSafeContent(content: string, detections: DetectionResult[]): string {
    if (detections.length === 0) {
      return content;
    }

    let safeContent = content;
    let offset = 0;

    // Process detections in reverse order to maintain position accuracy
    const sortedDetections = [...detections].sort((a, b) => b.position.start - a.position.start);

    for (const detection of sortedDetections) {
      const redaction = this.getRedactionText(detection);
      const startPos = detection.position.start;
      const endPos = detection.position.end;
      
      safeContent = 
        safeContent.substring(0, startPos) + 
        redaction + 
        safeContent.substring(endPos);
    }

    return safeContent;
  }

  private getRedactionText(detection: DetectionResult): string {
    const redactionMap: Record<string, string> = {
      ssn: '[SSN-REDACTED]',
      credit_card: '[CREDIT-CARD-REDACTED]',
      email: '[EMAIL-REDACTED]',
      phone_us: '[PHONE-REDACTED]',
      ip_address: '[IP-REDACTED]',
      passport: '[PASSPORT-REDACTED]',
      drivers_license: '[LICENSE-REDACTED]',
      aws_access_key: '[AWS-KEY-REDACTED]',
      aws_secret_key: '[AWS-SECRET-REDACTED]',
      github_token: '[GITHUB-TOKEN-REDACTED]',
      slack_token: '[SLACK-TOKEN-REDACTED]',
      stripe_key: '[STRIPE-KEY-REDACTED]',
      generic_api_key: '[API-KEY-REDACTED]',
      jwt_token: '[JWT-TOKEN-REDACTED]',
      private_key: '[PRIVATE-KEY-REDACTED]'
    };

    return redactionMap[detection.name] || `[${detection.type.toUpperCase()}-REDACTED]`;
  }

  async healthCheck(): Promise<boolean> {
    return this.ledgerClient.healthCheck();
  }

  setAuthToken(token: string): void {
    this.ledgerClient.setAuthToken(token);
  }

  clearAuthToken(): void {
    this.ledgerClient.clearAuthToken();
  }

  getConfig(): GuardConfig {
    return { ...this.config };
  }

  updateConfig(updates: Partial<GuardConfig>): void {
    this.config = { ...this.config, ...updates };
    
    // Update detectors if custom patterns changed
    if (updates.customPatterns?.pii) {
      this.piiDetector = new PIIDetector(updates.customPatterns.pii);
    }
    
    if (updates.customPatterns?.secrets) {
      this.secretDetector = new SecretDetector(updates.customPatterns.secrets);
    }
  }
}
