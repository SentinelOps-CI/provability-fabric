// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

import { v4 as uuidv4 } from 'uuid';
import { MCPClientAgent } from './mcp-client-agent.js';

interface Transaction {
  id: string;
  amount: number;
  merchant: string;
  user_id: string;
  location: string;
  timestamp: string;
  tenant_id: string;
}

class TransactionSimulator {
  private tenants: string[] = ['acme-corp', 'beta-inc', 'gamma-ltd'];
  private merchants: string[] = [
    'Coffee Shop', 'Gas Station', 'Grocery Store', 'Restaurant', 'Pharmacy',
    'Luxury Store', 'Electronics Store', 'Bookstore', 'Casino', 'Unknown Merchant'
  ];
  private locations: string[] = [
    'New York, NY', 'Los Angeles, CA', 'Chicago, IL', 'Houston, TX', 'Phoenix, AZ',
    'Philadelphia, PA', 'San Antonio, TX', 'San Diego, CA', 'Dallas, TX', 'Unknown'
  ];
  private users: string[] = [
    'user_alice', 'user_bob', 'user_charlie', 'user_diana', 'user_eve',
    'user_frank', 'user_grace', 'user_henry', 'user_iris', 'user_jack'
  ];

  generateTransaction(tenant?: string): Transaction {
    const amount = this.generateAmount();
    const merchant = this.randomChoice(this.merchants);
    const location = this.randomChoice(this.locations);
    const user = this.randomChoice(this.users);
    const tenantId = tenant || this.randomChoice(this.tenants);

    return {
      id: `txn_${uuidv4().substring(0, 8)}`,
      amount,
      merchant,
      user_id: user,
      location,
      timestamp: new Date().toISOString(),
      tenant_id: tenantId,
    };
  }

  generateBatch(count: number, tenant?: string): Transaction[] {
    const transactions: Transaction[] = [];
    
    for (let i = 0; i < count; i++) {
      transactions.push(this.generateTransaction(tenant));
    }
    
    return transactions;
  }

  generateSyntheticPatterns(patternType: 'normal' | 'suspicious' | 'mixed' = 'mixed'): Transaction[] {
    const transactions: Transaction[] = [];
    
    switch (patternType) {
      case 'normal':
        // Generate normal transaction patterns
        for (let i = 0; i < 20; i++) {
          transactions.push({
            id: `normal_${i}`,
            amount: Math.random() * 500 + 10, // $10-$510
            merchant: this.randomChoice(['Coffee Shop', 'Gas Station', 'Grocery Store']),
            user_id: this.randomChoice(this.users),
            location: this.randomChoice(['New York, NY', 'Los Angeles, CA', 'Chicago, IL']),
            timestamp: new Date().toISOString(),
            tenant_id: 'acme-corp',
          });
        }
        break;
        
      case 'suspicious':
        // Generate suspicious transaction patterns
        for (let i = 0; i < 10; i++) {
          transactions.push({
            id: `suspicious_${i}`,
            amount: Math.random() * 15000 + 5000, // $5,000-$20,000
            merchant: this.randomChoice(['Casino', 'Unknown Merchant', 'Crypto Exchange']),
            user_id: this.randomChoice(this.users),
            location: this.randomChoice(['Unknown', 'Offshore', 'Foreign']),
            timestamp: new Date(Date.now() - Math.random() * 86400000).toISOString(), // Random time in last 24h
            tenant_id: 'acme-corp',
          });
        }
        break;
        
      case 'mixed':
        // Generate mixed patterns
        transactions.push(...this.generateSyntheticPatterns('normal'));
        transactions.push(...this.generateSyntheticPatterns('suspicious'));
        break;
    }
    
    return transactions;
  }

  streamTransactions(callback: (transaction: Transaction) => void, intervalMs: number = 1000): () => void {
    const interval = setInterval(() => {
      const transaction = this.generateTransaction();
      callback(transaction);
    }, intervalMs);

    return () => clearInterval(interval);
  }

  generateMultiTenantStream(tenantCount: number = 3, transactionsPerMinute: number = 60): () => void {
    const intervalMs = (60 * 1000) / transactionsPerMinute;
    
    const interval = setInterval(() => {
      for (let i = 0; i < tenantCount; i++) {
        const tenant = this.tenants[i % this.tenants.length];
        const transaction = this.generateTransaction(tenant);
        
        console.log(`[${tenant}] Generated transaction: ${transaction.id} - $${transaction.amount}`);
        
        // In a real implementation, this would send to the MCP agent
      }
    }, intervalMs);

    return () => clearInterval(interval);
  }

  private generateAmount(): number {
    // Generate realistic transaction amounts with some high-value outliers
    const random = Math.random();
    
    if (random < 0.7) {
      // 70% normal transactions ($1-$500)
      return Math.random() * 499 + 1;
    } else if (random < 0.9) {
      // 20% medium transactions ($500-$2000)
      return Math.random() * 1500 + 500;
    } else {
      // 10% high-value transactions ($2000-$20000)
      return Math.random() * 18000 + 2000;
    }
  }

  private randomChoice<T>(array: T[]): T {
    return array[Math.floor(Math.random() * array.length)];
  }

  // Demo-specific methods
  async runPolicyDemo(): Promise<void> {
    console.log('🎯 Policy Enforcement Demo');
    console.log('Policy: Only FraudService may call /score; alerts emitted only after L_txn → L_ops via Δ_Risk; rate-limit alerts ≤ 5 per 10s/tenant; block score ≥ 0.93');
    console.log('');

    // Generate test transactions that will trigger different policy behaviors
    const testTransactions = [
      {
        id: 'demo_normal_001',
        amount: 50.00,
        merchant: 'Coffee Shop',
        user_id: 'user_alice',
        location: 'New York, NY',
      },
      {
        id: 'demo_high_risk_001',
        amount: 15000.00,
        merchant: 'Casino',
        user_id: 'user_bob',
        location: 'Unknown',
      },
      {
        id: 'demo_block_001',
        amount: 25000.00,
        merchant: 'Crypto Exchange',
        user_id: 'user_charlie',
        location: 'Offshore',
      },
    ];

    // Simulate fraud detection workflow
    console.log('🔍 Running fraud detection workflow...');
    for (const txn of testTransactions) {
      console.log(`Processing transaction ${txn.id}: ${txn.amount} ${txn.currency} at ${txn.merchant}`);
      // In a real implementation, this would call the fraud detection service
    }
    console.log('✅ Fraud detection workflow completed');
  }
}

// CLI entry point
async function main() {
  const agent = new MCPClientAgent({
    tenant_id: process.env.TENANT_ID || 'acme-corp',
    session_id: `demo_${Date.now()}`,
    policy_enforcement: true,
  });

  try {
    await agent.connect();
    await agent.runPolicyDemo();
  } catch (error) {
    console.error('Agent failed:', error);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(console.error);
}