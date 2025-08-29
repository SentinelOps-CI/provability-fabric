/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import { RAGGuard } from '../src/guard';
import { GuardConfig } from '../src/types';

// Mock axios for testing
jest.mock('axios');

describe('RAGGuard', () => {
  let guard: RAGGuard;
  let mockConfig: GuardConfig;

  beforeEach(() => {
    mockConfig = {
      ledgerUrl: 'http://localhost:3000',
      tenantId: 'test-tenant',
      sessionId: 'test-session',
      enablePII: true,
      enableSecrets: true,
      timeout: 5000,
      retries: 3
    };
    
    guard = new RAGGuard(mockConfig);
  });

  describe('Safe Content', () => {
    it('should allow safe content', async () => {
      const content = 'This is safe content about weather and general topics.';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(true);
      expect(result.safeContent).toBe(content);
      expect(result.blockedDetections).toBeUndefined();
    });

    it('should allow content with no sensitive data', async () => {
      const content = 'The weather today is sunny with a temperature of 75°F.';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(true);
      expect(result.safeContent).toBe(content);
    });
  });

  describe('PII Content Blocking', () => {
    it('should block content with SSN', async () => {
      const content = 'User SSN is 123-45-6789 for verification.';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('[SSN-REDACTED]');
      expect(result.blockedDetections).toBeDefined();
      expect(result.blockedDetections!.length).toBeGreaterThan(0);
      expect(result.blockedDetections![0].name).toBe('ssn');
    });

    it('should block content with email addresses', async () => {
      const content = 'Contact support at admin@example.com for help.';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('[EMAIL-REDACTED]');
      expect(result.blockedDetections![0].name).toBe('email');
    });

    it('should block content with credit card numbers', async () => {
      const content = 'Payment card: 4532-1234-5678-9012';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('[CREDIT-CARD-REDACTED]');
      expect(result.blockedDetections![0].name).toBe('credit_card');
    });
  });

  describe('Secret Content Blocking', () => {
    it('should block content with AWS keys', async () => {
      const content = 'Use AWS key: AKIA_FAKE_EXAMPLE_KEY';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('[AWS-KEY-REDACTED]');
      expect(result.blockedDetections![0].name).toBe('aws_access_key');
    });

    it('should block content with GitHub tokens', async () => {
      const content = 'Deploy with: ghp_fake_token_example_not_real';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('[GITHUB-TOKEN-REDACTED]');
      expect(result.blockedDetections![0].name).toBe('github_token');
    });

    it('should block content with JWT tokens', async () => {
      const content = 'Token: eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('[JWT-TOKEN-REDACTED]');
      expect(result.blockedDetections![0].name).toBe('jwt_token');
    });
  });

  describe('Mixed Content', () => {
    it('should handle multiple detections correctly', async () => {
      const content = 'User email: admin@company.com has SSN 123-45-6789 and API key: sk_fake_example_key_not_real';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.blockedDetections!.length).toBeGreaterThanOrEqual(3);
      
      // Check that all sensitive data is redacted
      expect(result.safeContent).toContain('[EMAIL-REDACTED]');
      expect(result.safeContent).toContain('[SSN-REDACTED]');
      expect(result.safeContent).toContain('[STRIPE-KEY-REDACTED]');
    });

    it('should maintain text structure while redacting', async () => {
      const content = 'Please contact john@example.com or call (555) 123-4567.';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('Please contact');
      expect(result.safeContent).toContain('or call');
      expect(result.safeContent).toContain('[EMAIL-REDACTED]');
      expect(result.safeContent).toContain('[PHONE-REDACTED]');
    });
  });

  describe('Configuration', () => {
    it('should respect PII detection toggle', async () => {
      const configNoPII: GuardConfig = {
        ...mockConfig,
        enablePII: false
      };
      const guardNoPII = new RAGGuard(configNoPII);
      
      const content = 'Email: admin@example.com';
      const result = await guardNoPII.filter(content);
      
      expect(result.allowed).toBe(true);
      expect(result.safeContent).toBe(content);
    });

    it('should respect secrets detection toggle', async () => {
      const configNoSecrets: GuardConfig = {
        ...mockConfig,
        enableSecrets: false
      };
      const guardNoSecrets = new RAGGuard(configNoSecrets);
      
      const content = 'API key: AKIA_FAKE_EXAMPLE_KEY';
      const result = await guardNoSecrets.filter(content);
      
      expect(result.allowed).toBe(true);
      expect(result.safeContent).toBe(content);
    });

    it('should support config updates', () => {
      const originalConfig = guard.getConfig();
      expect(originalConfig.enablePII).toBe(true);
      
      guard.updateConfig({ enablePII: false });
      
      const updatedConfig = guard.getConfig();
      expect(updatedConfig.enablePII).toBe(false);
    });
  });

  describe('Error Handling', () => {
    it('should fail securely on processing errors', async () => {
      // Create a guard with invalid config to trigger errors
      const invalidConfig = {
        ...mockConfig,
        ledgerUrl: 'invalid-url'
      };
      const errorGuard = new RAGGuard(invalidConfig);
      
      const content = 'Some content with email: test@example.com';
      const result = await errorGuard.filter(content);
      
      // Should fail securely - block content
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('Content blocked due to processing error');
    });

    it('should handle empty content gracefully', async () => {
      const result = await guard.filter('');
      
      expect(result.allowed).toBe(true);
      expect(result.safeContent).toBe('');
    });

    it('should handle very long content', async () => {
      const longContent = 'Safe content '.repeat(10000);
      const result = await guard.filter(longContent);
      
      expect(result.allowed).toBe(true);
      expect(result.safeContent).toBe(longContent);
    });
  });

  describe('Edge Cases', () => {
    it('should handle overlapping detections', async () => {
      // Content with potential overlapping patterns
      const content = 'API key api_key=123-45-6789 embedded in SSN-like format';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.blockedDetections!.length).toBeGreaterThan(0);
    });

    it('should handle regex edge cases', async () => {
      const content = 'String with special regex chars: ^$.*+?()[]{}|\\';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(true);
      expect(result.safeContent).toBe(content);
    });

    it('should handle unicode characters', async () => {
      const content = 'Unicode content: 测试 with email: test@例え.com';
      const result = await guard.filter(content);
      
      expect(result.allowed).toBe(false);
      expect(result.safeContent).toContain('Unicode content: 测试');
      expect(result.safeContent).toContain('[EMAIL-REDACTED]');
    });
  });
});
