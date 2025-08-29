/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import { PIIDetector } from '../src/detectors/pii';

describe('PIIDetector', () => {
  let detector: PIIDetector;

  beforeEach(() => {
    detector = new PIIDetector();
  });

  describe('SSN Detection', () => {
    it('should detect SSN with dashes', () => {
      const content = 'My SSN is 123-45-6789 for verification.';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('ssn');
      expect(results[0].match).toBe('123-45-6789');
      expect(results[0].severity).toBe('critical');
    });

    it('should detect SSN without dashes', () => {
      const content = 'SSN: 123456789';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].match).toBe('123456789');
    });

    it('should not detect invalid SSN patterns', () => {
      const content = 'Not an SSN: 12345678 or 1234567890';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(0);
    });
  });

  describe('Email Detection', () => {
    it('should detect valid email addresses', () => {
      const content = 'Contact us at support@example.com or admin@test.org';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(2);
      expect(results[0].match).toBe('support@example.com');
      expect(results[1].match).toBe('admin@test.org');
    });

    it('should handle complex email formats', () => {
      const content = 'Email: user.name+tag@subdomain.example.com';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].match).toBe('user.name+tag@subdomain.example.com');
    });
  });

  describe('Credit Card Detection', () => {
    it('should detect Visa card numbers', () => {
      const content = 'Card: 4532-1234-5678-9012';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('credit_card');
      expect(results[0].severity).toBe('critical');
    });

    it('should detect MasterCard numbers', () => {
      const content = 'Payment: 5555 5555 5555 4444';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].match).toBe('5555 5555 5555 4444');
    });
  });

  describe('Phone Number Detection', () => {
    it('should detect US phone numbers with various formats', () => {
      const content = 'Call (555) 123-4567 or 555.123.4567 or 5551234567';
      const results = detector.detect(content);
      
      expect(results.length).toBeGreaterThanOrEqual(2);
      expect(results.some(r => r.match.includes('(555) 123-4567'))).toBe(true);
    });
  });

  describe('IP Address Detection', () => {
    it('should detect IPv4 addresses', () => {
      const content = 'Server IP: 192.168.1.1 and backup: 10.0.0.1';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(2);
      expect(results[0].match).toBe('192.168.1.1');
      expect(results[1].match).toBe('10.0.0.1');
    });

    it('should not detect invalid IP addresses', () => {
      const content = 'Not an IP: 999.999.999.999 or 192.168.1';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(0);
    });
  });

  describe('Custom Patterns', () => {
    it('should support custom PII patterns', () => {
      const customDetector = new PIIDetector([
        {
          name: 'employee_id',
          pattern: /EMP\d{6}/g,
          severity: 'medium',
          description: 'Employee ID'
        }
      ]);

      const content = 'Employee EMP123456 accessed the system.';
      const results = customDetector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('employee_id');
      expect(results[0].match).toBe('EMP123456');
    });
  });

  describe('Pattern Management', () => {
    it('should add custom patterns', () => {
      const initialCount = detector.getPatterns().length;
      
      detector.addCustomPattern({
        name: 'test_pattern',
        pattern: /TEST\d+/g,
        severity: 'low',
        description: 'Test Pattern'
      });

      expect(detector.getPatterns()).toHaveLength(initialCount + 1);
    });

    it('should remove patterns by name', () => {
      const initialCount = detector.getPatterns().length;
      detector.removePattern('email');
      
      expect(detector.getPatterns()).toHaveLength(initialCount - 1);
      expect(detector.getPatterns().find(p => p.name === 'email')).toBeUndefined();
    });
  });
});
