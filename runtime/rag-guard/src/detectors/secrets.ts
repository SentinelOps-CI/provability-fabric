/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import { SecretPattern, DetectionResult } from '../types';

export class SecretDetector {
  private patterns: SecretPattern[];

  constructor(customPatterns?: SecretPattern[]) {
    this.patterns = [
      ...this.getDefaultPatterns(),
      ...(customPatterns || [])
    ];
  }

  private getDefaultPatterns(): SecretPattern[] {
    return [
      {
        name: 'aws_access_key',
        pattern: /AKIA[0-9A-Z]{16}/g,
        severity: 'critical',
        description: 'AWS Access Key ID'
      },
      {
        name: 'aws_secret_key',
        pattern: /[A-Za-z0-9/+=]{40}/g,
        entropyThreshold: 4.5,
        severity: 'critical',
        description: 'AWS Secret Access Key'
      },
      {
        name: 'github_token',
        pattern: /gh[pousr]_[A-Za-z0-9_]{36}/g,
        severity: 'critical',
        description: 'GitHub Personal Access Token'
      },
      {
        name: 'slack_token',
        pattern: /xox[baprs]-([0-9a-zA-Z]{10,48})/g,
        severity: 'high',
        description: 'Slack Token'
      },
      {
        name: 'stripe_key',
        pattern: /sk_live_[0-9a-zA-Z]{24}/g,
        severity: 'critical',
        description: 'Stripe Live Secret Key'
      },
      {
        name: 'generic_api_key',
        pattern: /(?:api[_-]?key|apikey|secret|token)[\s=:'"]*([a-zA-Z0-9_-]{20,})/gi,
        entropyThreshold: 4.0,
        severity: 'medium',
        description: 'Generic API Key'
      },
      {
        name: 'jwt_token',
        pattern: /eyJ[A-Za-z0-9_=-]{10,}\.eyJ[A-Za-z0-9_=-]{10,}\.[A-Za-z0-9_=-]{10,}/g,
        severity: 'high',
        description: 'JWT Token'
      },
      {
        name: 'private_key',
        pattern: /-----BEGIN [A-Z ]+PRIVATE KEY-----[\s\S]*?-----END [A-Z ]+PRIVATE KEY-----/g,
        severity: 'critical',
        description: 'Private Key'
      }
    ];
  }

  detect(content: string): DetectionResult[] {
    const results: DetectionResult[] = [];

    for (const pattern of this.patterns) {
      let match;
      // Reset regex lastIndex to ensure proper matching
      pattern.pattern.lastIndex = 0;
      
      while ((match = pattern.pattern.exec(content)) !== null) {
        // Extract the actual matched content (group 1 if available, otherwise full match)
        const matchedText = match[1] || match[0];
        const startPos = match.index + (match[0].indexOf(matchedText));
        
        // Check entropy threshold if specified
        if (pattern.entropyThreshold && !this.meetsEntropyThreshold(matchedText, pattern.entropyThreshold)) {
          continue;
        }

        results.push({
          type: 'secret',
          name: pattern.name,
          severity: pattern.severity,
          match: matchedText,
          position: {
            start: startPos,
            end: startPos + matchedText.length
          },
          description: pattern.description
        });

        // Prevent infinite loops on zero-length matches
        if (match.index === pattern.pattern.lastIndex) {
          pattern.pattern.lastIndex++;
        }
      }
    }

    return results;
  }

  private meetsEntropyThreshold(text: string, threshold: number): boolean {
    if (text.length < 8) return false; // Too short to be meaningful
    
    const entropy = this.calculateEntropy(text);
    return entropy >= threshold;
  }

  private calculateEntropy(text: string): number {
    const charCounts = new Map<string, number>();
    
    // Count character frequencies
    for (const char of text) {
      charCounts.set(char, (charCounts.get(char) || 0) + 1);
    }
    
    // Calculate Shannon entropy
    let entropy = 0;
    const textLength = text.length;
    
    for (const count of charCounts.values()) {
      const probability = count / textLength;
      entropy -= probability * Math.log2(probability);
    }
    
    return entropy;
  }

  addCustomPattern(pattern: SecretPattern): void {
    this.patterns.push(pattern);
  }

  removePattern(name: string): void {
    this.patterns = this.patterns.filter(p => p.name !== name);
  }

  getPatterns(): SecretPattern[] {
    return [...this.patterns];
  }
}
