/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import { PIIPattern, DetectionResult } from '../types';

export class PIIDetector {
  private patterns: PIIPattern[];

  constructor(customPatterns?: PIIPattern[]) {
    this.patterns = [
      ...this.getDefaultPatterns(),
      ...(customPatterns || [])
    ];
  }

  private getDefaultPatterns(): PIIPattern[] {
    return [
      {
        name: 'ssn',
        pattern: /(?:^|[^\d])(\d{3}-?\d{2}-?\d{4})(?:[^\d]|$)/g,
        severity: 'critical',
        description: 'Social Security Number'
      },
      {
        name: 'credit_card',
        pattern: /(?:^|[^\d])([4-6]\d{3}[\s-]?\d{4}[\s-]?\d{4}[\s-]?\d{4})(?:[^\d]|$)/g,
        severity: 'critical',
        description: 'Credit Card Number'
      },
      {
        name: 'email',
        // Support IDN/unicode domains and labels (Node >= 12 supports Unicode property escapes)
        pattern: /\b[\p{L}0-9._%+-]+@[\p{L}0-9.-]+\.[\p{L}A-Za-z]{2,}\b/gu,
        severity: 'medium',
        description: 'Email Address'
      },
      {
        name: 'phone_us',
        pattern: /(?:^|[^\d])(\(?[0-9]{3}\)?[-.\s]?[0-9]{3}[-.\s]?[0-9]{4})(?:[^\d]|$)/g,
        severity: 'medium',
        description: 'US Phone Number'
      },
      {
        name: 'ip_address',
        // Match IPv4 then validate octets are 0-255 to avoid false positives like 999.999.999.999
        pattern: /\b(?:[0-9]{1,3}\.){3}[0-9]{1,3}\b/g,
        severity: 'low',
        description: 'IP Address'
      },
      {
        name: 'passport',
        pattern: /(?:^|[^\w])([A-Z]{1,2}\d{6,9})(?:[^\w]|$)/g,
        severity: 'high',
        description: 'Passport Number'
      },
      {
        name: 'drivers_license',
        pattern: /(?:^|[^\w])([A-Z]{1,2}\d{6,8})(?:[^\w]|$)/g,
        severity: 'high',
        description: 'Driver License Number'
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
        let matchedText = match[1] || match[0];
        const startPos = match.index + (match[0].indexOf(matchedText));
        
        // Additional validation for IP addresses
        if (pattern.name === 'ip_address') {
          const octets = matchedText.split('.')
            .map(v => (v || '').trim())
            .filter(v => v.length > 0);
          if (octets.length !== 4 || octets.some(v => isNaN(Number(v)) || Number(v) < 0 || Number(v) > 255)) {
            continue;
          }
        }

        // Tighten US phone matching to avoid nine/ten digit random numbers without separators in normal text
        if (pattern.name === 'phone_us') {
          if (!/[().\-\s]/.test(matchedText)) {
            // require some formatting char to reduce false positives like 1234567890 in text
            continue;
          }
        }

        // Unicode/IDN email support: normalize visually similar dot
        if (pattern.name === 'email') {
          // Accept unicode domain labels with IDNA-like dots
          // Already matched by broad regex; no-op here, kept for future extensions
        }

        results.push({
          type: 'pii',
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

  addCustomPattern(pattern: PIIPattern): void {
    this.patterns.push(pattern);
  }

  removePattern(name: string): void {
    this.patterns = this.patterns.filter(p => p.name !== name);
  }

  getPatterns(): PIIPattern[] {
    return [...this.patterns];
  }
}
