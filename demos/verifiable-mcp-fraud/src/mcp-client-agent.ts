// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
import { CallToolResultSchema } from '@modelcontextprotocol/sdk/types.js';
import { SentinelOpsClient } from '@provability-fabric/core-sdk-typescript';

interface AgentConfig {
  tenant_id: string;
  session_id: string;
  policy_enforcement: boolean;
  sidecar_url?: string;
}

export class MCPClientAgent {
  private client: Client;
  private sentinelOps: SentinelOpsClient;
  private config: AgentConfig;
  private sessionId: string;

  constructor(config: AgentConfig) {
    this.config = config;
    this.sessionId = config.session_id || `session_${Date.now()}`;
    
    // Initialize SentinelOps client for platform integration
    this.sentinelOps = new SentinelOpsClient(
      process.env.SENTINELOPS_API_URL || 'http://localhost:8000',
      process.env.SENTINELOPS_API_KEY
    );

    this.client = new Client(
      {
        name: 'fraud-detection-agent',
        version: '1.0.0',
      },
      {
        capabilities: {},
      }
    );
  }

  async connect(): Promise<void> {
    // Configure MCP server transport
    const transport = new StdioClientTransport({
      command: 'node',
      args: ['dist/fraud-mcp-server.js'],
    });

    await this.client.connect(transport);
    console.log('Connected to Fraud Detection MCP Server');
  }

  async runFraudDetectionWorkflow(transactions: any[]): Promise<void> {
    console.log(`Starting fraud detection workflow for ${transactions.length} transactions`);
    
    for (const txn of transactions) {
      try {
        // 1. Ingest transaction
        console.log(`Processing transaction: ${txn.id}`);
        
        await this.client.request(
          {
            method: 'tools/call',
            params: {
              name: 'ingest_transaction',
              arguments: {
                transaction_id: txn.id,
                amount: txn.amount,
                merchant: txn.merchant,
                user_id: txn.user_id,
                tenant_id: this.config.tenant_id,
                location: txn.location,
              },
            },
          },
          CallToolResultSchema
        );

        // 2. Score fraud (this should be restricted by platform policy)
        const scoreResult = await this.client.request(
          {
            method: 'tools/call',
            params: {
              name: 'score_fraud',
              arguments: {
                transaction_id: txn.id,
                tenant_id: this.config.tenant_id,
              },
            },
          },
          CallToolResultSchema
        );

        const scoreText = scoreResult.content.find(
          (block): block is { type: 'text'; text: string } => block.type === 'text'
        )?.text;
        if (!scoreText) {
          throw new Error('score_fraud returned no text content');
        }
        const scoreData = JSON.parse(scoreText);
        console.log(`Fraud score for ${txn.id}: ${scoreData.fraud_score} (${scoreData.risk_level})`);

        // 3. Handle high-risk transactions
        if (scoreData.should_block) {
          console.log(`🚨 BLOCKING transaction ${txn.id} - fraud score: ${scoreData.fraud_score}`);
          
          // This should trigger platform policy enforcement
          // and generate CERT-V1 certificate
        }

        // Small delay between transactions
        await new Promise(resolve => setTimeout(resolve, 100));

      } catch (error) {
        console.error(`Error processing transaction ${txn.id}:`, error.message);
        
        // Platform should capture this error in evidence
      }
    }
  }

  async demonstratePolicyEnforcement(): Promise<void> {
    console.log('🔍 Demonstrating policy enforcement...');

    // This should be ALLOWED by policy: "Only FraudService may call /score"
    try {
      await this.client.request(
        {
          method: 'tools/call',
          params: {
            name: 'score_fraud',
            arguments: {
              transaction_id: 'test_txn_001',
              tenant_id: this.config.tenant_id,
            },
          },
        },
        CallToolResultSchema
      );
      console.log('✅ Fraud scoring allowed (expected)');
    } catch (error) {
      console.log('❌ Fraud scoring denied (check policy configuration)');
    }

    // Demonstrate rate limiting: "Rate limit alerts to 5 per 10 seconds per tenant"
    console.log('🔄 Testing rate limiting...');
    for (let i = 0; i < 7; i++) {
      try {
        await this.client.request(
          {
            method: 'tools/call',
            params: {
              name: 'score_fraud',
              arguments: {
                transaction_id: `rate_test_${i}`,
                tenant_id: this.config.tenant_id,
              },
            },
          },
          CallToolResultSchema
        );
        console.log(`Rate limit test ${i + 1}/7: Success`);
      } catch (error) {
        console.log(`Rate limit test ${i + 1}/7: ${error.message}`);
      }
      
      await new Promise(resolve => setTimeout(resolve, 200));
    }
  }

  async demonstrateEpochRotation(): Promise<void> {
    console.log('🔄 Demonstrating epoch rotation...');
    
    try {
      // Get current epoch
      await this.sentinelOps.getSLO();
      console.log('Current epoch: 42'); // Mock for demo
      
      // Rotate epoch and lower threshold to 0.90 for tenant ACME
      await this.sentinelOps.rotateEpoch(42, 43, 'Demo: Lower fraud threshold for ACME tenant');
      console.log('✅ Epoch rotated successfully');
      
      // Test with new policy
      await this.client.request(
        {
          method: 'tools/call',
          params: {
            name: 'score_fraud',
            arguments: {
              transaction_id: 'epoch_test_001',
              tenant_id: 'acme-corp',
            },
          },
        },
        CallToolResultSchema
      );
      
      console.log('✅ Policy enforcement with new epoch successful');
      
    } catch (error) {
      console.error('❌ Epoch rotation demo failed:', error.message);
    }
  }

  async demonstrateComplianceExport(): Promise<void> {
    console.log('📊 Demonstrating compliance export...');
    
    try {
      // Download compliance packet
      const packetData = await this.sentinelOps.downloadPacket(this.sessionId);
      console.log(`✅ Downloaded compliance packet: ${packetData.size} bytes`);
      
      // In a real demo, this would save the packet to disk
      console.log('📁 Compliance packet ready for GRC system import');
      
    } catch (error) {
      console.error('❌ Compliance export failed:', error.message);
    }
  }

  async runFullDemo(): Promise<void> {
    console.log('🚀 Starting Verifiable MCP Fraud Demo');
    console.log('📋 This demo showcases SentinelOps Platform capabilities');
    console.log('');

    // Sample transactions for demo
    const sampleTransactions = [
      {
        id: 'txn_001',
        amount: 150.00,
        merchant: 'Coffee Shop',
        user_id: 'user_alice',
        location: 'New York, NY',
      },
      {
        id: 'txn_002', 
        amount: 15000.00,
        merchant: 'Luxury Store',
        user_id: 'user_bob',
        location: 'Unknown',
      },
      {
        id: 'txn_003',
        amount: 50.00,
        merchant: 'Gas Station',
        user_id: 'user_charlie',
        location: 'Chicago, IL',
      },
    ];

    // 1. Run fraud detection workflow
    await this.runFraudDetectionWorkflow(sampleTransactions);
    
    // 2. Demonstrate policy enforcement
    await this.demonstratePolicyEnforcement();
    
    // 3. Demonstrate epoch rotation
    await this.demonstrateEpochRotation();
    
    // 4. Demonstrate compliance export
    await this.demonstrateComplianceExport();

    console.log('');
    console.log('✅ Demo completed successfully');
    console.log('🔍 Check the Console UI for:');
    console.log('  - Live Runtime metrics');
    console.log('  - CERT-V1 certificates in Evidence');
    console.log('  - Replay results with 99.9%+ low-view equality');
    console.log('  - Compliance packets for export');
  }
}

// CLI entry point
async function main() {
  const config: AgentConfig = {
    tenant_id: process.env.TENANT_ID || 'acme-corp',
    session_id: `demo_session_${Date.now()}`,
    policy_enforcement: true,
    sidecar_url: process.env.SIDECAR_URL || 'http://localhost:9090',
  };

  const agent = new MCPClientAgent(config);
  
  try {
    await agent.connect();
    await agent.runFullDemo();
  } catch (error) {
    console.error('Demo failed:', error);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(console.error);
}