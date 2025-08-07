import { test, expect } from '@playwright/test';
import axios from 'axios';

interface ComponentBudget {
  name: string;
  budget: number; // milliseconds
  endpoint: string;
  method: 'GET' | 'POST' | 'PUT' | 'DELETE';
  payload?: any;
}

interface PerformanceResult {
  component: string;
  p50: number;
  p95: number;
  p99: number;
  avg: number;
  max: number;
  samples: number;
  budgetExceeded: boolean;
}

class ComponentBudgetTester {
  private baseUrl: string;
  private results: PerformanceResult[] = [];

  constructor(baseUrl: string = 'http://localhost:8080') {
    this.baseUrl = baseUrl;
  }

  // Component budget definitions
  private budgets: ComponentBudget[] = [
    {
      name: 'Plan Generation',
      budget: 150,
      endpoint: '/validate',
      method: 'POST',
      payload: {
        plan_id: 'test_plan_budget',
        tenant: 'test-tenant',
        subject: {
          id: 'test-subject',
          caps: ['read_docs']
        },
        input_channels: {
          system: {
            hash: 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456',
            policy_hash: 'policy_hash_1'
          },
          user: {
            content_hash: 'user_input_hash_budget',
            quoted: true
          },
          retrieved: [],
          file: []
        },
        steps: [
          {
            tool: 'test_tool',
            args: { param: 'value' },
            caps_required: ['read_docs'],
            labels_in: ['public'],
            labels_out: ['processed']
          }
        ],
        constraints: {
          budget: 1.0,
          pii: false,
          dp_epsilon: 0.1,
          dp_delta: 1e-6,
          latency_max: 30.0
        },
        system_prompt_hash: 'a1b2c4d5e6f6789012345678901234567890abcdef1234567890abcdef123456',
        created_at: Math.floor(Date.now() / 1000),
        expires_at: Math.floor(Date.now() / 1000) + 3600
      }
    },
    {
      name: 'Retrieval Gateway',
      budget: 600,
      endpoint: '/retrieve',
      method: 'POST',
      payload: {
        query: 'test query for budget testing',
        tenant: 'test-tenant',
        subject_id: 'test-subject',
        labels: ['public']
      }
    },
    {
      name: 'Policy Kernel',
      budget: 120,
      endpoint: '/kernel/validate',
      method: 'POST',
      payload: {
        plan_id: 'test_plan_kernel',
        tenant: 'test-tenant',
        subject: {
          id: 'test-subject',
          caps: ['read_docs']
        },
        capabilities: ['read_docs'],
        receipts: []
      }
    },
    {
      name: 'Egress Firewall',
      budget: 400,
      endpoint: '/egress/scan',
      method: 'POST',
      payload: {
        content: 'test content for egress scanning',
        tenant: 'test-tenant',
        labels: ['public'],
        destination: 'https://api.example.com'
      }
    }
  ];

  async measureComponentPerformance(budget: ComponentBudget, samples: number = 100): Promise<PerformanceResult> {
    const latencies: number[] = [];
    
    console.log(`Testing ${budget.name} with ${samples} samples...`);
    
    for (let i = 0; i < samples; i++) {
      const start = Date.now();
      
      try {
        const response = await axios({
          method: budget.method,
          url: `${this.baseUrl}${budget.endpoint}`,
          data: budget.payload,
          headers: {
            'Content-Type': 'application/json',
            'X-Test-ID': `budget_test_${budget.name}_${i}`
          },
          timeout: 10000 // 10 second timeout
        });
        
        const latency = Date.now() - start;
        latencies.push(latency);
        
        // Add small delay between requests
        await new Promise(resolve => setTimeout(resolve, 10));
        
      } catch (error) {
        console.error(`Error testing ${budget.name}:`, error);
        latencies.push(10000); // Count timeout as max latency
      }
    }
    
    // Calculate statistics
    latencies.sort((a, b) => a - b);
    const avg = latencies.reduce((sum, val) => sum + val, 0) / latencies.length;
    const p50 = latencies[Math.floor(latencies.length * 0.5)];
    const p95 = latencies[Math.floor(latencies.length * 0.95)];
    const p99 = latencies[Math.floor(latencies.length * 0.99)];
    const max = Math.max(...latencies);
    
    const budgetExceeded = p95 > budget.budget;
    
    const result: PerformanceResult = {
      component: budget.name,
      p50,
      p95,
      p99,
      avg,
      max,
      samples: latencies.length,
      budgetExceeded
    };
    
    console.log(`${budget.name} Results:`);
    console.log(`  p50: ${p50}ms`);
    console.log(`  p95: ${p95}ms (budget: ${budget.budget}ms)`);
    console.log(`  p99: ${p99}ms`);
    console.log(`  avg: ${avg.toFixed(2)}ms`);
    console.log(`  max: ${max}ms`);
    console.log(`  Budget exceeded: ${budgetExceeded ? 'YES' : 'NO'}`);
    
    return result;
  }

  async runAllBudgetTests(): Promise<PerformanceResult[]> {
    console.log('Starting component budget tests...');
    console.log(`Base URL: ${this.baseUrl}`);
    
    const results: PerformanceResult[] = [];
    
    for (const budget of this.budgets) {
      const result = await this.measureComponentPerformance(budget);
      results.push(result);
      this.results.push(result);
    }
    
    return results;
  }

  generateReport(): any {
    const totalTests = this.results.length;
    const budgetViolations = this.results.filter(r => r.budgetExceeded);
    const violationRate = (budgetViolations.length / totalTests) * 100;
    
    const report = {
      summary: {
        totalComponents: totalTests,
        budgetViolations: budgetViolations.length,
        violationRate: `${violationRate.toFixed(1)}%`,
        allComponentsWithinBudget: budgetViolations.length === 0
      },
      components: this.results.map(r => ({
        name: r.component,
        p95: r.p95,
        budget: this.budgets.find(b => b.name === r.component)?.budget || 0,
        budgetExceeded: r.budgetExceeded,
        margin: this.budgets.find(b => b.name === r.component)?.budget || 0 - r.p95
      })),
      details: this.results
    };
    
    console.log('\n=== Component Budget Test Report ===');
    console.log(`Total Components: ${report.summary.totalComponents}`);
    console.log(`Budget Violations: ${report.summary.budgetViolations}`);
    console.log(`Violation Rate: ${report.summary.violationRate}`);
    console.log(`All Within Budget: ${report.summary.allComponentsWithinBudget ? 'YES' : 'NO'}`);
    
    if (budgetViolations.length > 0) {
      console.log('\nViolations:');
      budgetViolations.forEach(v => {
        const budget = this.budgets.find(b => b.name === v.component);
        console.log(`  ${v.component}: p95=${v.p95}ms (budget=${budget?.budget}ms)`);
      });
    }
    
    return report;
  }
}

// Playwright test
test.describe('Component Budget Tests', () => {
  test('all components should stay within budget', async ({ request }) => {
    const baseUrl = process.env.BASE_URL || 'http://localhost:8080';
    const tester = new ComponentBudgetTester(baseUrl);
    
    const results = await tester.runAllBudgetTests();
    const report = tester.generateReport();
    
    // Assertions
    expect(report.summary.allComponentsWithinBudget).toBe(true);
    expect(report.summary.budgetViolations).toBe(0);
    
    // Individual component assertions
    for (const result of results) {
      const budget = tester['budgets'].find(b => b.name === result.component);
      expect(result.p95).toBeLessThanOrEqual(budget?.budget || Infinity);
    }
  });

  test('component performance should be consistent', async ({ request }) => {
    const baseUrl = process.env.BASE_URL || 'http://localhost:8080';
    const tester = new ComponentBudgetTester(baseUrl);
    
    // Run multiple test iterations
    const iterations = 3;
    const allResults: PerformanceResult[][] = [];
    
    for (let i = 0; i < iterations; i++) {
      console.log(`\nIteration ${i + 1}/${iterations}`);
      const results = await tester.runAllBudgetTests();
      allResults.push(results);
      
      // Small delay between iterations
      await new Promise(resolve => setTimeout(resolve, 1000));
    }
    
    // Check consistency across iterations
    for (let componentIndex = 0; componentIndex < allResults[0].length; componentIndex++) {
      const componentName = allResults[0][componentIndex].component;
      const p95Values = allResults.map(iteration => iteration[componentIndex].p95);
      
      const avg = p95Values.reduce((sum, val) => sum + val, 0) / p95Values.length;
      const variance = p95Values.reduce((sum, val) => sum + Math.pow(val - avg, 2), 0) / p95Values.length;
      const stdDev = Math.sqrt(variance);
      const coefficientOfVariation = (stdDev / avg) * 100;
      
      console.log(`${componentName} consistency:`);
      console.log(`  p95 values: ${p95Values.map(v => v.toFixed(1)).join(', ')}`);
      console.log(`  CV: ${coefficientOfVariation.toFixed(1)}%`);
      
      // Assert reasonable consistency (CV < 20%)
      expect(coefficientOfVariation).toBeLessThan(20);
    }
  });
});

// Standalone execution
if (require.main === module) {
  async function main() {
    const baseUrl = process.env.BASE_URL || 'http://localhost:8080';
    const tester = new ComponentBudgetTester(baseUrl);
    
    try {
      const results = await tester.runAllBudgetTests();
      const report = tester.generateReport();
      
      if (!report.summary.allComponentsWithinBudget) {
        console.error('❌ Component budget test FAILED');
        process.exit(1);
      } else {
        console.log('✅ Component budget test PASSED');
      }
    } catch (error) {
      console.error('Test execution failed:', error);
      process.exit(1);
    }
  }
  
  main();
} 