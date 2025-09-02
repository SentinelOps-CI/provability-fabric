// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

import { SentinelOpsClient } from '@sentinelops/platform-sdk';

const FRAUD_POLICY_ENGLISH = `
Only FraudService may call the score endpoint.

Alerts are emitted only after L_txn flows to L_ops via Δ_Risk declassification.

Rate limit alerts to 5 per 10 seconds per tenant.

Block transactions with fraud score greater than or equal to 0.93.

Allow read access to transaction data for users with reader role when tenant is verified.

Forbid write access to fraud scores for users without admin role.

Budget limit 1000 USD per day for fraud scoring operations.
`;

async function setupDemo() {
  console.log('🚀 Setting up Verifiable MCP Fraud Demo');
  console.log('');

  const client = new SentinelOpsClient(
    process.env.SENTINELOPS_API_URL || 'http://localhost:8000',
    process.env.SENTINELOPS_API_KEY
  );

  try {
    console.log('1️⃣ Compiling fraud detection policy...');
    
    // Execute full policy workflow using platform SDK
    const result = await client.fullPolicyWorkflow(
      FRAUD_POLICY_ENGLISH,
      'fraud-detection-v1'
    );
    
    console.log('✅ Policy workflow completed:');
    console.log(`   Policy Hash: ${result.policy_hash}`);
    console.log(`   Proof Hash: ${result.proof_hash}`);
    console.log(`   Automata Hash: ${result.automata_hash}`);
    console.log(`   Epoch: ${result.epoch}`);
    console.log(`   Status: ${result.status}`);
    console.log('');

    console.log('2️⃣ Verifying platform health...');
    const health = await client.getHealth();
    console.log(`✅ Platform status: ${health.status}`);
    
    // Check service health
    for (const [service, status] of Object.entries(health.services)) {
      const serviceStatus = (status as any).status || 'unknown';
      const emoji = serviceStatus === 'healthy' ? '✅' : '❌';
      console.log(`   ${emoji} ${service}: ${serviceStatus}`);
    }
    console.log('');

    console.log('3️⃣ Checking runtime SLO...');
    const slo = await client.getSLO();
    console.log(`✅ Latency P95: ${slo.latency.p95.toFixed(1)}ms`);
    console.log(`✅ TPS: ${slo.tps}`);
    console.log(`✅ Error Rate: ${(slo.error_rate * 100).toFixed(2)}%`);
    console.log('');

    console.log('4️⃣ Demo setup completed successfully!');
    console.log('');
    console.log('🎯 Next steps:');
    console.log('   1. Run: npm run dev:agent');
    console.log('   2. Open Console UI: http://localhost:3000');
    console.log('   3. Monitor Runtime tab for live metrics');
    console.log('   4. Check Evidence tab for CERT-V1 certificates');
    console.log('   5. Run replays to verify 99.9%+ low-view equality');
    console.log('   6. Download compliance packets');
    console.log('');

    // Save demo configuration
    const demoConfig = {
      policy_id: 'fraud-detection-v1',
      policy_hash: result.policy_hash,
      automata_hash: result.automata_hash,
      epoch: result.epoch,
      setup_timestamp: new Date().toISOString(),
      platform_health: health,
      slo_baseline: slo,
    };

    // Write config file
    await import('fs/promises').then(fs => 
      fs.writeFile('demo-config.json', JSON.stringify(demoConfig, null, 2))
    );
    
    console.log('📁 Demo configuration saved to demo-config.json');

  } catch (error) {
    console.error('❌ Demo setup failed:', error.message);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(console.error);
}