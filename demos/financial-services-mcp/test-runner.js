#!/usr/bin/env node

/**
 * Comprehensive Test Runner for Financial Services MCP Demo
 * 
 * This script orchestrates the execution of all test suites with proper
 * initialization, teardown, and comprehensive reporting.
 */

const { spawn, exec } = require('child_process');
const fs = require('fs').promises;
const path = require('path');
const { promisify } = require('util');

const execAsync = promisify(exec);

class TestRunner {
  constructor() {
    this.results = {
      startTime: new Date(),
      endTime: null,
      suites: {},
      summary: {
        total: 0,
        passed: 0,
        failed: 0,
        skipped: 0
      },
      performance: {
        duration: 0,
        memoryUsage: {
          heapUsed: 0,
          heapTotal: 0,
          external: 0
        }
      }
    };
    
    this.testSuites = [
      {
        name: 'integration',
        file: 'tests/integration-test-suite.ts',
        timeout: 300000, // 5 minutes
        critical: true,
        description: 'Core integration tests for all components'
      },
      {
        name: 'enhanced',
        file: 'tests/enhanced-test-suite.ts',
        timeout: 480000, // 8 minutes
        critical: true,
        description: 'Enhanced performance and accuracy tests'
      },
      {
        name: 'security',
        file: 'tests/security-audit-test-suite.ts',
        timeout: 360000, // 6 minutes
        critical: true,
        description: 'Security and audit trail validation'
      },
      {
        name: 'stress',
        file: 'tests/stress-test-suite.ts',
        timeout: 720000, // 12 minutes
        critical: false,
        description: 'Extreme load and stress testing'
      }
    ];
  }

  async checkPrerequisites() {
    console.log('🔍 Checking prerequisites...');
    
    const checks = [
      { cmd: 'node --version', name: 'Node.js', minVersion: '20.0.0' },
      { cmd: 'npm --version', name: 'npm', minVersion: '10.0.0' },
      { cmd: 'docker --version', name: 'Docker' },
      { cmd: 'docker-compose --version', name: 'Docker Compose' }
    ];

    for (const check of checks) {
      try {
        const { stdout } = await execAsync(check.cmd);
        console.log(`  ✅ ${check.name}: ${stdout.trim()}`);
      } catch (error) {
        console.error(`  ❌ ${check.name}: Not available`);
        throw new Error(`Missing prerequisite: ${check.name}`);
      }
    }
  }

  async checkServices() {
    console.log('🏥 Checking service health...');
    
    const services = [
      { name: 'PostgreSQL', url: 'postgresql://fintech_user:secure_fintech_2025@localhost:5433/financial_services' },
      { name: 'Redis', url: 'redis://localhost:6380' },
      { name: 'MCP Server', url: 'http://localhost:8080/health' },
      { name: 'Fraud Agent', url: 'http://localhost:8082/health' },
      { name: 'Audit Service', url: 'http://localhost:8083/health' }
    ];

    for (const service of services) {
      try {
        if (service.name === 'PostgreSQL') {
          await execAsync(`pg_isready -h localhost -p 5433 -U fintech_user`);
        } else if (service.name === 'Redis') {
          await execAsync(`redis-cli -h localhost -p 6380 ping`);
        } else {
          const { stdout } = await execAsync(`curl -s ${service.url}`);
          if (!stdout.includes('healthy') && !stdout.includes('ok')) {
            throw new Error('Service not healthy');
          }
        }
        console.log(`  ✅ ${service.name}: Healthy`);
      } catch (error) {
        console.error(`  ❌ ${service.name}: ${error.message}`);
        throw new Error(`Service check failed: ${service.name}`);
      }
    }
  }

  async setupEnvironment() {
    console.log('🛠️  Setting up test environment...');
    
    try {
      // Install dependencies if needed
      await execAsync('npm ci --silent');
      console.log('  ✅ Dependencies installed');

      // Create reports directory
      await fs.mkdir('reports', { recursive: true });
      console.log('  ✅ Reports directory created');

      // Set environment variables
      process.env.NODE_ENV = 'test';
      process.env.TEST_MODE = 'comprehensive';
      process.env.JEST_TIMEOUT = '600000'; // 10 minutes max per test file
      
      console.log('  ✅ Environment configured');
    } catch (error) {
      throw new Error(`Environment setup failed: ${error.message}`);
    }
  }

  async runTestSuite(suite) {
    console.log(`\n🧪 Running ${suite.name} test suite...`);
    console.log(`   📄 ${suite.description}`);
    console.log(`   ⏱️  Timeout: ${suite.timeout / 1000}s`);
    
    const startTime = Date.now();
    
    return new Promise((resolve) => {
      const jestProcess = spawn('npx', [
        'jest',
        suite.file,
        '--verbose',
        '--json',
        '--outputFile', `reports/jest-${suite.name}-results.json`,
        '--testTimeout', suite.timeout.toString()
      ], {
        stdio: ['pipe', 'pipe', 'pipe'],
        env: { ...process.env }
      });

      let stdout = '';
      let stderr = '';

      jestProcess.stdout.on('data', (data) => {
        stdout += data.toString();
        process.stdout.write(data);
      });

      jestProcess.stderr.on('data', (data) => {
        stderr += data.toString();
        process.stderr.write(data);
      });

      jestProcess.on('close', async (code) => {
        const endTime = Date.now();
        const duration = endTime - startTime;

        try {
          // Try to read Jest JSON output
          const resultsPath = `reports/jest-${suite.name}-results.json`;
          let jestResults = null;
          
          try {
            const resultsContent = await fs.readFile(resultsPath, 'utf8');
            jestResults = JSON.parse(resultsContent);
          } catch (error) {
            console.warn(`  ⚠️  Could not parse Jest results for ${suite.name}`);
          }

          const result = {
            name: suite.name,
            critical: suite.critical,
            passed: code === 0,
            duration,
            exitCode: code,
            stdout,
            stderr,
            jestResults,
            tests: jestResults ? {
              total: jestResults.numTotalTests || 0,
              passed: jestResults.numPassedTests || 0,
              failed: jestResults.numFailedTests || 0,
              skipped: jestResults.numPendingTests || 0
            } : null
          };

          this.results.suites[suite.name] = result;

          if (result.tests) {
            this.results.summary.total += result.tests.total;
            this.results.summary.passed += result.tests.passed;
            this.results.summary.failed += result.tests.failed;
            this.results.summary.skipped += result.tests.skipped;
          }

          const status = code === 0 ? '✅ PASSED' : '❌ FAILED';
          console.log(`\n   ${status} ${suite.name} (${duration}ms)`);
          
          if (result.tests) {
            console.log(`   📊 Tests: ${result.tests.passed}/${result.tests.total} passed`);
          }

          resolve(result);
        } catch (error) {
          console.error(`Error processing results for ${suite.name}:`, error);
          resolve({
            name: suite.name,
            critical: suite.critical,
            passed: false,
            duration,
            exitCode: code,
            error: error.message
          });
        }
      });

      // Handle timeout
      setTimeout(() => {
        if (!jestProcess.killed) {
          console.log(`\n   ⏰ Test suite ${suite.name} timed out, killing process...`);
          jestProcess.kill('SIGKILL');
        }
      }, suite.timeout + 30000); // 30s grace period
    });
  }

  async runAllTests(options = {}) {
    const { criticalOnly = false, parallel = false } = options;
    
    console.log('🚀 Starting comprehensive test execution...');
    
    try {
      await this.checkPrerequisites();
      await this.checkServices();
      await this.setupEnvironment();

      const suitesToRun = this.testSuites.filter(suite => 
        !criticalOnly || suite.critical
      );

      console.log(`\n📋 Test plan: ${suitesToRun.length} suites`);
      suitesToRun.forEach(suite => {
        console.log(`   ${suite.critical ? '🔴' : '🟡'} ${suite.name}: ${suite.description}`);
      });

      if (parallel) {
        console.log('\n⚡ Running tests in parallel...');
        const promises = suitesToRun.map(suite => this.runTestSuite(suite));
        await Promise.all(promises);
      } else {
        console.log('\n🔄 Running tests sequentially...');
        for (const suite of suitesToRun) {
          await this.runTestSuite(suite);
        }
      }

      this.results.endTime = new Date();
      this.results.performance.duration = this.results.endTime - this.results.startTime;
      this.results.performance.memoryUsage = process.memoryUsage();

      await this.generateReports();
      this.printSummary();

      return this.results;
    } catch (error) {
      console.error('\n💥 Test execution failed:', error.message);
      process.exit(1);
    }
  }

  async generateReports() {
    console.log('\n📊 Generating test reports...');

    const timestamp = new Date().toISOString().split('T')[0];
    
    // JSON report
    const jsonReportPath = `reports/comprehensive-test-report-${timestamp}.json`;
    await fs.writeFile(jsonReportPath, JSON.stringify(this.results, null, 2));
    console.log(`   📄 JSON report: ${jsonReportPath}`);

    // Markdown report
    const markdownReport = this.generateMarkdownReport();
    const mdReportPath = `reports/comprehensive-test-report-${timestamp}.md`;
    await fs.writeFile(mdReportPath, markdownReport);
    console.log(`   📄 Markdown report: ${mdReportPath}`);

    // JUnit XML report (for CI/CD)
    const junitReport = this.generateJUnitReport();
    const junitReportPath = `reports/junit-test-results-${timestamp}.xml`;
    await fs.writeFile(junitReportPath, junitReport);
    console.log(`   📄 JUnit report: ${junitReportPath}`);
  }

  generateMarkdownReport() {
    const { startTime, endTime, summary, performance, suites } = this.results;
    
    let report = `# Financial Services MCP - Test Report

**Execution Time:** ${startTime.toISOString()} - ${endTime.toISOString()}  
**Duration:** ${Math.round(performance.duration / 1000)}s  
**Total Tests:** ${summary.total}  
**Passed:** ${summary.passed} ✅  
**Failed:** ${summary.failed} ${summary.failed > 0 ? '❌' : ''}  
**Skipped:** ${summary.skipped} ${summary.skipped > 0 ? '⏭️' : ''}  

## Executive Summary

Overall Status: ${summary.failed === 0 ? '✅ ALL TESTS PASSED' : '❌ TESTS FAILED'}

Success Rate: ${summary.total > 0 ? Math.round((summary.passed / summary.total) * 100) : 0}%

## Test Suite Results

| Suite | Status | Duration | Tests | Pass Rate |
|-------|--------|----------|-------|-----------|
`;

    Object.values(suites).forEach(suite => {
      const status = suite.passed ? '✅ PASSED' : '❌ FAILED';
      const duration = Math.round(suite.duration / 1000);
      const tests = suite.tests ? `${suite.tests.passed}/${suite.tests.total}` : 'N/A';
      const passRate = suite.tests && suite.tests.total > 0 
        ? Math.round((suite.tests.passed / suite.tests.total) * 100) 
        : 0;
      
      report += `| ${suite.name} | ${status} | ${duration}s | ${tests} | ${passRate}% |\n`;
    });

    report += `\n## Performance Metrics

**Memory Usage:**
- Heap Used: ${Math.round(performance.memoryUsage.heapUsed / 1024 / 1024)}MB
- Heap Total: ${Math.round(performance.memoryUsage.heapTotal / 1024 / 1024)}MB
- External: ${Math.round(performance.memoryUsage.external / 1024 / 1024)}MB

## Detailed Results

`;

    Object.values(suites).forEach(suite => {
      report += `### ${suite.name.toUpperCase()} Test Suite

**Status:** ${suite.passed ? '✅ PASSED' : '❌ FAILED'}  
**Duration:** ${Math.round(suite.duration / 1000)}s  
**Critical:** ${suite.critical ? 'Yes' : 'No'}  

`;

      if (suite.tests) {
        report += `**Test Results:**
- Total Tests: ${suite.tests.total}
- Passed: ${suite.tests.passed}
- Failed: ${suite.tests.failed}
- Skipped: ${suite.tests.skipped}

`;
      }

      if (!suite.passed && suite.stderr) {
        report += `**Error Output:**
\`\`\`
${suite.stderr.slice(0, 1000)}${suite.stderr.length > 1000 ? '...' : ''}
\`\`\`

`;
      }
    });

    report += `## Recommendations

`;

    const failedSuites = Object.values(suites).filter(s => !s.passed);
    if (failedSuites.length === 0) {
      report += `✅ All tests passed successfully. System is ready for production deployment.

`;
    } else {
      report += `❌ ${failedSuites.length} test suite(s) failed. Address the following issues:

`;
      failedSuites.forEach(suite => {
        report += `- **${suite.name}**: ${suite.critical ? 'CRITICAL - ' : ''}Review test failures and fix underlying issues\n`;
      });
    }

    report += `
---
*Report generated on ${new Date().toISOString()}*
`;

    return report;
  }

  generateJUnitReport() {
    let xml = `<?xml version="1.0" encoding="UTF-8"?>
<testsuites 
  name="Financial Services MCP Tests" 
  tests="${this.results.summary.total}" 
  failures="${this.results.summary.failed}" 
  skipped="${this.results.summary.skipped}" 
  time="${this.results.performance.duration / 1000}">
`;

    Object.values(this.results.suites).forEach(suite => {
      const testCount = suite.tests ? suite.tests.total : 1;
      const failures = suite.tests ? suite.tests.failed : (suite.passed ? 0 : 1);
      const skipped = suite.tests ? suite.tests.skipped : 0;
      
      xml += `  <testsuite 
    name="${suite.name}" 
    tests="${testCount}" 
    failures="${failures}" 
    skipped="${skipped}" 
    time="${suite.duration / 1000}">
`;

      if (suite.jestResults && suite.jestResults.testResults) {
        suite.jestResults.testResults.forEach(testFile => {
          testFile.assertionResults.forEach(test => {
            xml += `    <testcase name="${test.title}" classname="${suite.name}" time="${test.duration || 0}">`;
            
            if (test.status === 'failed') {
              xml += `
      <failure message="${test.failureMessages ? test.failureMessages[0] : 'Test failed'}">
        ${test.failureMessages ? test.failureMessages.join('\n') : ''}
      </failure>`;
            } else if (test.status === 'pending') {
              xml += `
      <skipped/>`;
            }
            
            xml += `
    </testcase>
`;
          });
        });
      } else {
        // Fallback for suites without detailed Jest results
        xml += `    <testcase name="${suite.name}" classname="${suite.name}" time="${suite.duration / 1000}">`;
        if (!suite.passed) {
          xml += `
      <failure message="Test suite failed">
        ${suite.stderr || suite.error || 'Unknown error'}
      </failure>`;
        }
        xml += `
    </testcase>
`;
      }

      xml += `  </testsuite>
`;
    });

    xml += `</testsuites>`;
    return xml;
  }

  printSummary() {
    console.log('\n' + '='.repeat(60));
    console.log('📊 COMPREHENSIVE TEST SUMMARY');
    console.log('='.repeat(60));
    
    const { summary, performance } = this.results;
    const successRate = summary.total > 0 ? Math.round((summary.passed / summary.total) * 100) : 0;
    
    console.log(`\n🎯 Overall Result: ${summary.failed === 0 ? '✅ SUCCESS' : '❌ FAILURE'}`);
    console.log(`📈 Success Rate: ${successRate}%`);
    console.log(`⏱️  Total Duration: ${Math.round(performance.duration / 1000)}s`);
    console.log(`🧪 Total Tests: ${summary.total}`);
    console.log(`   ✅ Passed: ${summary.passed}`);
    console.log(`   ❌ Failed: ${summary.failed}`);
    console.log(`   ⏭️  Skipped: ${summary.skipped}`);
    
    console.log('\n📋 Test Suite Breakdown:');
    Object.values(this.results.suites).forEach(suite => {
      const status = suite.passed ? '✅' : '❌';
      const critical = suite.critical ? '🔴' : '🟡';
      const duration = Math.round(suite.duration / 1000);
      console.log(`   ${status} ${critical} ${suite.name}: ${duration}s`);
    });
    
    console.log('\n💾 Memory Usage:');
    console.log(`   Heap Used: ${Math.round(performance.memoryUsage.heapUsed / 1024 / 1024)}MB`);
    console.log(`   Heap Total: ${Math.round(performance.memoryUsage.heapTotal / 1024 / 1024)}MB`);
    
    const failedCritical = Object.values(this.results.suites)
      .filter(s => !s.passed && s.critical).length;
      
    if (failedCritical > 0) {
      console.log(`\n🚨 CRITICAL: ${failedCritical} critical test suite(s) failed!`);
      console.log('   System is NOT ready for production deployment.');
    } else if (summary.failed > 0) {
      console.log('\n⚠️  Some non-critical tests failed. Review recommended.');
    } else {
      console.log('\n🎉 All tests passed! System ready for production.');
    }
    
    console.log('\n📄 Detailed reports available in ./reports/ directory');
    console.log('='.repeat(60));
  }
}

// CLI Interface
async function main() {
  const args = process.argv.slice(2);
  const options = {
    criticalOnly: args.includes('--critical-only'),
    parallel: args.includes('--parallel'),
    help: args.includes('--help') || args.includes('-h')
  };

  if (options.help) {
    console.log(`
Financial Services MCP - Comprehensive Test Runner

Usage: node test-runner.js [options]

Options:
  --critical-only    Run only critical test suites
  --parallel         Run test suites in parallel (experimental)
  --help, -h         Show this help message

Examples:
  node test-runner.js                    # Run all tests sequentially
  node test-runner.js --critical-only    # Run only critical tests
  node test-runner.js --parallel         # Run tests in parallel
`);
    process.exit(0);
  }

  const runner = new TestRunner();
  
  try {
    const results = await runner.runAllTests(options);
    
    // Exit with appropriate code
    const hasFailedCritical = Object.values(results.suites)
      .some(s => !s.passed && s.critical);
    
    process.exit(hasFailedCritical ? 1 : 0);
  } catch (error) {
    console.error('💥 Test runner failed:', error);
    process.exit(1);
  }
}

// Run if called directly
if (require.main === module) {
  main().catch(error => {
    console.error('💥 Unhandled error:', error);
    process.exit(1);
  });
}

module.exports = TestRunner;
