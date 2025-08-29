/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

import { SecretDetector } from '../src/detectors/secrets';

describe('SecretDetector', () => {
  let detector: SecretDetector;

  beforeEach(() => {
    detector = new SecretDetector();
  });

  describe('AWS Key Detection', () => {
    it('should detect AWS access keys', () => {
      const content = 'AWS_ACCESS_KEY_ID=AKIA_FAKE_EXAMPLE_KEY';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('aws_access_key');
      expect(results[0].match).toBe('AKIA_FAKE_EXAMPLE_KEY');
      expect(results[0].severity).toBe('critical');
    });

    it('should detect AWS secret keys with entropy check', () => {
      const content = 'AWS_SECRET_ACCESS_KEY=wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('aws_secret_key');
      expect(results[0].severity).toBe('critical');
    });

    it('should not detect low-entropy strings as secrets', () => {
      const content = 'password=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa';
      const results = detector.detect(content);
      
      // Should not detect the low-entropy string
      const awsSecrets = results.filter(r => r.name === 'aws_secret_key');
      expect(awsSecrets).toHaveLength(0);
    });
  });

  describe('GitHub Token Detection', () => {
    it('should detect GitHub personal access tokens', () => {
      const content = 'GITHUB_TOKEN=ghp_fake_token_example_not_real';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('github_token');
      expect(results[0].severity).toBe('critical');
    });

    it('should detect GitHub app tokens', () => {
      const content = 'TOKEN=gho_1234567890abcdefghijklmnopqrstuvwxyz';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('github_token');
    });
  });

  describe('Slack Token Detection', () => {
    it('should detect Slack bot tokens', () => {
      const content = 'SLACK_BOT_TOKEN=xoxb_fake_token_example_not_real';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('slack_token');
      expect(results[0].severity).toBe('high');
    });

    it('should detect Slack user tokens', () => {
      const content = 'token: xoxp_fake_token_example_not_real';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('slack_token');
    });
  });

  describe('Stripe Key Detection', () => {
    it('should detect Stripe live secret keys', () => {
      const content = 'STRIPE_SECRET_KEY=sk_fake_example_key_not_real';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('stripe_key');
      expect(results[0].severity).toBe('critical');
    });
  });

  describe('JWT Token Detection', () => {
    it('should detect JWT tokens', () => {
      const content = 'Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c';
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('jwt_token');
      expect(results[0].severity).toBe('high');
    });
  });

  describe('Private Key Detection', () => {
    it('should detect RSA private keys', () => {
      const content = `-----BEGIN RSA PRIVATE KEY-----
MIIEpAIBAAKCAQEA7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z7Z
...key content...
-----END RSA PRIVATE KEY-----`;
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('private_key');
      expect(results[0].severity).toBe('critical');
    });

    it('should detect EC private keys', () => {
      const content = `-----BEGIN EC PRIVATE KEY-----
MHcCAQEEIGcZzA...
-----END EC PRIVATE KEY-----`;
      const results = detector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('private_key');
    });
  });

  describe('Generic API Key Detection', () => {
    it('should detect generic API keys with high entropy', () => {
      const content = 'api_key=9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08';
      const results = detector.detect(content);
      
      const apiKeyResults = results.filter(r => r.name === 'generic_api_key');
      expect(apiKeyResults.length).toBeGreaterThanOrEqual(1);
    });

    it('should not detect low-entropy strings as API keys', () => {
      const content = 'api_key=password123';
      const results = detector.detect(content);
      
      const apiKeyResults = results.filter(r => r.name === 'generic_api_key');
      expect(apiKeyResults).toHaveLength(0);
    });
  });

  describe('Entropy Calculation', () => {
    it('should handle entropy thresholds correctly', () => {
      // Test with known high-entropy string
      const highEntropyContent = 'secret=9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08';
      const results1 = detector.detect(highEntropyContent);
      const genericKeys1 = results1.filter(r => r.name === 'generic_api_key');
      expect(genericKeys1.length).toBeGreaterThanOrEqual(1);

      // Test with known low-entropy string
      const lowEntropyContent = 'secret=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa';
      const results2 = detector.detect(lowEntropyContent);
      const genericKeys2 = results2.filter(r => r.name === 'generic_api_key');
      expect(genericKeys2).toHaveLength(0);
    });
  });

  describe('Custom Patterns', () => {
    it('should support custom secret patterns', () => {
      const customDetector = new SecretDetector([
        {
          name: 'custom_token',
          pattern: /CTK_[A-Za-z0-9]{32}/g,
          severity: 'medium',
          description: 'Custom Token'
        }
      ]);

      const content = 'Use token: CTK_abcdef1234567890abcdef1234567890';
      const results = customDetector.detect(content);
      
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('custom_token');
      expect(results[0].match).toBe('CTK_abcdef1234567890abcdef1234567890');
    });

    it('should support entropy thresholds in custom patterns', () => {
      const customDetector = new SecretDetector([
        {
          name: 'high_entropy_key',
          pattern: /KEY_([A-Za-z0-9]{20,})/g,
          entropyThreshold: 4.5,
          severity: 'high',
          description: 'High Entropy Key'
        }
      ]);

      const highEntropyContent = 'KEY_9f86d081884c7d659a2feaa0c55ad015';
      const lowEntropyContent = 'KEY_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa';
      
      const results1 = customDetector.detect(highEntropyContent);
      expect(results1).toHaveLength(1);
      
      const results2 = customDetector.detect(lowEntropyContent);
      expect(results2).toHaveLength(0);
    });
  });

  describe('Pattern Management', () => {
    it('should add custom patterns', () => {
      const initialCount = detector.getPatterns().length;
      
      detector.addCustomPattern({
        name: 'test_secret',
        pattern: /SECRET\d+/g,
        severity: 'low',
        description: 'Test Secret'
      });

      expect(detector.getPatterns()).toHaveLength(initialCount + 1);
    });

    it('should remove patterns by name', () => {
      const initialCount = detector.getPatterns().length;
      detector.removePattern('github_token');
      
      expect(detector.getPatterns()).toHaveLength(initialCount - 1);
      expect(detector.getPatterns().find(p => p.name === 'github_token')).toBeUndefined();
    });
  });
});
