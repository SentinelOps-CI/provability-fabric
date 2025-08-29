#!/usr/bin/env ts-node
/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Demo script showing @pf/guard-rag usage
 */

import { RAGGuard, GuardConfig } from '../src';

async function runDemo() {
  console.log('🔒 Provability Fabric RAG Guard Demo\n');

  const config: GuardConfig = {
    ledgerUrl: 'http://localhost:3000',
    tenantId: 'demo-tenant',
    sessionId: 'demo-session-001',
    enablePII: true,
    enableSecrets: true,
    timeout: 5000,
    retries: 3
  };

  const guard = new RAGGuard(config);

  // Test cases
  const testCases = [
    {
      name: 'Safe Content',
      content: 'This is a safe response about weather and general topics.'
    },
    {
      name: 'PII - Social Security Number',
      content: 'The user with SSN 123-45-6789 requested information about benefits.'
    },
    {
      name: 'PII - Email and Phone',
      content: 'Contact John Doe at john.doe@example.com or call (555) 123-4567.'
    },
    {
      name: 'Secrets - AWS Keys',
      content: 'Use this AWS access key: AKIAIOSFODNN7EXAMPLE and secret: wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY'
    },
    {
      name: 'Secrets - GitHub Token',
      content: 'Deploy with token ghp_1234567890abcdefghijklmnopqrstuvwxyz'
    },
    {
      name: 'Mixed PII and Secrets',
      content: 'User email: admin@company.com has API key: sk_live_1234567890abcdefghijklmn for credit card 4532-1234-5678-9012'
    }
  ];

  for (const testCase of testCases) {
    console.log(`\n📝 Testing: ${testCase.name}`);
    console.log(`Original: ${testCase.content}`);
    
    try {
      const result = await guard.filter(testCase.content);
      
      if (result.allowed) {
        console.log('✅ Content allowed');
        console.log(`Safe content: ${result.safeContent}`);
      } else {
        console.log('🚫 Content blocked');
        console.log(`Safe content: ${result.safeContent}`);
        
        if (result.blockedDetections) {
          console.log('🔍 Detections:');
          for (const detection of result.blockedDetections) {
            console.log(`  - ${detection.name} (${detection.severity}): ${detection.description}`);
          }
        }
        
        if (result.incidentId) {
          console.log(`📊 Incident ID: ${result.incidentId}`);
        }
      }
    } catch (error: any) {
      console.error(`❌ Error: ${error.message}`);
    }
    
    console.log('─'.repeat(80));
  }

  // Health check demo
  console.log('\n🔍 Health Check:');
  try {
    const isHealthy = await guard.healthCheck();
    console.log(`Ledger connection: ${isHealthy ? '✅ Healthy' : '❌ Unhealthy'}`);
  } catch (error: any) {
    console.log(`❌ Health check failed: ${error.message}`);
  }

  console.log('\n✨ Demo completed!');
}

if (require.main === module) {
  runDemo().catch(console.error);
}
