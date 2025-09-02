/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Comprehensive MCP Integration Test Suite
 * Validates all aspects of MCP integration including security, performance, and functionality
 */

const axios = require('axios');
const WebSocket = require('ws');
const fs = require('fs');
const path = require('path');

// Load test configuration
const testConfigPath = path.join(__dirname, 'test-mcp-config.json');
const testConfig = JSON.parse(fs.readFileSync(testConfigPath, 'utf8'));

class ComprehensiveMcpTest {
  constructor() {
    this.passedTests = 0;
    this.failedTests = 0;
    this.skippedTests = 0;
    this.testResults = [];
    this.config = testConfig.testConfig;
    this.mockData = testConfig.mockData;
    
    // Mock JWT token for testing (in production, use real authentication)
    this.mockJWT = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ0ZXN0LXVzZXItaWQiLCJ0ZW5hbnRfaWQiOiJ0ZXN0LXRlbmFudCIsImlhdCI6MTcwOTU1NjAwMCwiZXhwIjoxNzA5NjQyNDAwfQ.test';
  }

  log(level, message, data = {}) {
    const timestamp = new Date().toISOString();
    const logEntry = {
      timestamp,
      level,
      message,
      ...data
    };
    
    const colors = {
      info: '\x1b[36m',    // Cyan
      success: '\x1b[32m', // Green
      warning: '\x1b[33m', // Yellow
      error: '\x1b[31m',   // Red
      reset: '\x1b[0m'     // Reset
    };
    
    const color = colors[level] || colors.reset;
    console.log(`${color}[${level.toUpperCase()}] ${message}${colors.reset}`, 
      Object.keys(data).length > 0 ? JSON.stringify(data, null, 2) : '');
  }

  async runTest(testName, testFunction, category = 'general') {
    this.log('info', `Running test: ${testName}`, { category });
    
    try {
      const startTime = Date.now();
      await testFunction();
      const duration = Date.now() - startTime;
      
      this.passedTests++;
      this.testResults.push({ 
        name: testName, 
        status: 'PASS', 
        category,
        duration
      });
      this.log('success', `${testName} - PASSED`, { duration: `${duration}ms` });
    } catch (error) {
      this.failedTests++;
      this.testResults.push({ 
        name: testName, 
        status: 'FAIL', 
        category,
        error: error.message 
      });
      this.log('error', `${testName} - FAILED`, { error: error.message });
    }
  }

  async skipTest(testName, reason, category = 'general') {
    this.skippedTests++;
    this.testResults.push({ 
      name: testName, 
      status: 'SKIP', 
      category,
      reason 
    });
    this.log('warning', `${testName} - SKIPPED`, { reason });
  }

  async makeRequest(endpoint, options = {}) {
    const {
      method = 'GET',
      data = null,
      headers = {},
      requiresAuth = false,
      expectedStatus = 200,
      timeout = this.config.timeout
    } = options;

    const requestHeaders = {
      'Content-Type': 'application/json',
      ...headers
    };

    if (requiresAuth) {
      requestHeaders['Authorization'] = `Bearer ${this.mockJWT}`;
    }

    const config = {
      method,
      url: `${this.config.baseUrl}${endpoint}`,
      headers: requestHeaders,
      timeout,
      validateStatus: () => true // Don't throw on any status code
    };

    if (data && (method === 'POST' || method === 'PUT' || method === 'PATCH')) {
      config.data = data;
    }

    const response = await axios(config);
    
    // Validate expected status
    if (Array.isArray(expectedStatus)) {
      if (!expectedStatus.includes(response.status)) {
        throw new Error(`Expected status ${expectedStatus.join(' or ')}, got ${response.status}`);
      }
    } else if (response.status !== expectedStatus) {
      throw new Error(`Expected status ${expectedStatus}, got ${response.status}`);
    }

    return response;
  }

  async testHealthChecks() {
    this.log('info', 'Starting health check tests...');
    
    for (const testCase of testConfig.testCases.healthChecks) {
      await this.runTest(testCase.name, async () => {
        const response = await this.makeRequest(testCase.endpoint, {
          method: testCase.method,
          expectedStatus: testCase.expectedStatus
        });

        if (!response.data || typeof response.data !== 'object') {
          throw new Error('Health check should return JSON object');
        }

        for (const field of testCase.expectedFields) {
          if (!(field in response.data)) {
            throw new Error(`Missing required field: ${field}`);
          }
        }

        this.log('info', `Health check response: ${testCase.endpoint}`, {
          status: response.data.status,
          fields: testCase.expectedFields.filter(f => response.data[f] !== undefined)
        });
      }, 'health');
    }
  }

  async testMcpEndpoints() {
    this.log('info', 'Starting MCP endpoint tests...');
    
    for (const testCase of testConfig.testCases.mcpEndpoints) {
      await this.runTest(testCase.name, async () => {
        const response = await this.makeRequest(testCase.endpoint, {
          method: testCase.method,
          data: testCase.body,
          requiresAuth: testCase.requiresAuth,
          expectedStatus: testCase.expectedStatus
        });

        // Validate expected fields if specified
        if (testCase.expectedFields && response.data) {
          for (const field of testCase.expectedFields) {
            if (!(field in response.data)) {
              throw new Error(`Missing required field: ${field}`);
            }
          }
        }

        // Log response for JSON-RPC endpoints
        if (testCase.endpoint.includes('jsonrpc') && response.data) {
          this.log('info', `MCP JSON-RPC response for ${testCase.name}`, {
            method: testCase.body?.method,
            hasResult: !!response.data.result,
            hasError: !!response.data.error,
            status: response.status
          });
        }
      }, 'mcp-endpoints');
    }
  }

  async testErrorHandling() {
    this.log('info', 'Starting error handling tests...');
    
    for (const testCase of testConfig.testCases.errorHandling) {
      await this.runTest(testCase.name, async () => {
        const response = await this.makeRequest(testCase.endpoint, {
          method: testCase.method,
          data: testCase.body,
          requiresAuth: testCase.requiresAuth,
          expectedStatus: testCase.expectedStatus
        });

        // Verify error response format for JSON-RPC endpoints
        if (testCase.endpoint.includes('jsonrpc') && response.status >= 400) {
          if (response.data && response.data.error) {
            this.log('info', `Error response format validated for ${testCase.name}`, {
              errorCode: response.data.error.code,
              errorMessage: response.data.error.message
            });
          }
        }
      }, 'error-handling');
    }
  }

  async testPolicyEnforcement() {
    this.log('info', 'Starting policy enforcement tests...');
    
    for (const testCase of testConfig.testCases.policyEnforcement) {
      await this.runTest(testCase.name, async () => {
        const response = await this.makeRequest(testCase.endpoint, {
          method: testCase.method,
          data: testCase.body,
          requiresAuth: testCase.requiresAuth,
          expectedStatus: testCase.expectedStatus
        });

        // Policy enforcement should return appropriate error codes
        if (response.status === 403) {
          this.log('info', `Policy correctly enforced for ${testCase.name}`, {
            description: testCase.description,
            status: response.status
          });
        } else if (response.status >= 400) {
          this.log('info', `Request blocked as expected for ${testCase.name}`, {
            status: response.status,
            description: testCase.description
          });
        }
      }, 'policy-enforcement');
    }
  }

  async testWebSocketConnection() {
    this.log('info', 'Starting WebSocket tests...');
    
    return new Promise((resolve, reject) => {
      const ws = new WebSocket(this.config.wsUrl);
      let testsPassed = 0;
      const totalTests = testConfig.webSocketTests.length;
      let currentTestIndex = 0;

      const runNextWebSocketTest = () => {
        if (currentTestIndex >= testConfig.webSocketTests.length) {
          ws.close();
          resolve();
          return;
        }

        const testCase = testConfig.webSocketTests[currentTestIndex];
        this.log('info', `Running WebSocket test: ${testCase.name}`);

        switch (testCase.action) {
          case 'connect':
            // Connection test is automatic
            testsPassed++;
            this.log('success', `WebSocket test passed: ${testCase.name}`);
            currentTestIndex++;
            setTimeout(runNextWebSocketTest, 1000);
            break;

          case 'send':
            ws.send(JSON.stringify(testCase.message));
            break;
        }
      };

      ws.on('open', () => {
        this.log('success', 'WebSocket connection established');
        runNextWebSocketTest();
      });

      ws.on('message', (data) => {
        try {
          const message = JSON.parse(data.toString());
          const currentTest = testConfig.webSocketTests[currentTestIndex];
          
          if (currentTest && currentTest.expectedResponse) {
            if (message.type === currentTest.expectedResponse.type) {
              testsPassed++;
              this.log('success', `WebSocket test passed: ${currentTest.name}`, {
                messageType: message.type
              });
            } else {
              this.log('warning', `Unexpected WebSocket message type`, {
                expected: currentTest.expectedResponse.type,
                received: message.type
              });
            }
          }

          currentTestIndex++;
          setTimeout(runNextWebSocketTest, 1000);
        } catch (error) {
          this.log('error', 'Failed to parse WebSocket message', { error: error.message });
        }
      });

      ws.on('error', (error) => {
        this.log('error', 'WebSocket error', { error: error.message });
        reject(new Error(`WebSocket error: ${error.message}`));
      });

      ws.on('close', () => {
        this.log('info', `WebSocket tests completed`, {
          passed: testsPassed,
          total: totalTests
        });
      });

      // Timeout for WebSocket tests
      setTimeout(() => {
        if (ws.readyState === WebSocket.OPEN) {
          ws.close();
        }
        reject(new Error('WebSocket tests timed out'));
      }, this.config.timeout * 2);
    });
  }

  async testPerformanceMetrics() {
    this.log('info', 'Starting performance tests...');
    
    await this.runTest('Response Time Check', async () => {
      const startTime = Date.now();
      const response = await this.makeRequest('/api/mcp/health');
      const responseTime = Date.now() - startTime;
      
      if (responseTime > 5000) { // 5 second threshold
        throw new Error(`Response time too slow: ${responseTime}ms`);
      }
      
      this.log('info', 'Performance metrics', {
        responseTime: `${responseTime}ms`,
        threshold: '5000ms'
      });
    }, 'performance');

    await this.runTest('Concurrent Requests', async () => {
      const concurrentRequests = 10;
      const promises = Array.from({ length: concurrentRequests }, () =>
        this.makeRequest('/api/mcp/health')
      );
      
      const startTime = Date.now();
      const responses = await Promise.all(promises);
      const totalTime = Date.now() - startTime;
      
      const successfulRequests = responses.filter(r => r.status === 200).length;
      
      if (successfulRequests < concurrentRequests * 0.9) { // 90% success rate
        throw new Error(`Too many failed requests: ${successfulRequests}/${concurrentRequests}`);
      }
      
      this.log('info', 'Concurrent request metrics', {
        totalRequests: concurrentRequests,
        successful: successfulRequests,
        totalTime: `${totalTime}ms`,
        avgTime: `${(totalTime / concurrentRequests).toFixed(2)}ms`
      });
    }, 'performance');
  }

  async testIntegrationWithExistingServices() {
    this.log('info', 'Starting integration tests with existing services...');
    
    await this.runTest('GraphQL Endpoint Compatibility', async () => {
      // Test that GraphQL still works alongside MCP
      const response = await this.makeRequest('/graphql', {
        method: 'POST',
        data: {
          query: '{ __schema { types { name } } }'
        },
        expectedStatus: [200, 400, 401] // May require auth
      });
      
      this.log('info', 'GraphQL endpoint status', { status: response.status });
    }, 'integration');

    await this.runTest('Billing Endpoints Unaffected', async () => {
      // Test that existing billing endpoints still work
      const response = await this.makeRequest('/usage', {
        method: 'POST',
        data: {
          tenant_id: this.mockData.tenantId,
          cpu_ms: 100,
          net_bytes: 1024
        },
        requiresAuth: true,
        expectedStatus: [200, 401, 403] // May require valid auth
      });
      
      this.log('info', 'Billing endpoint status', { status: response.status });
    }, 'integration');
  }

  generateDetailedReport() {
    this.log('info', 'Generating detailed test report...');
    
    const report = {
      summary: {
        total: this.passedTests + this.failedTests + this.skippedTests,
        passed: this.passedTests,
        failed: this.failedTests,
        skipped: this.skippedTests,
        successRate: ((this.passedTests / (this.passedTests + this.failedTests)) * 100).toFixed(1)
      },
      categories: {},
      timestamp: new Date().toISOString(),
      environment: {
        baseUrl: this.config.baseUrl,
        wsUrl: this.config.wsUrl,
        timeout: this.config.timeout
      }
    };

    // Group results by category
    this.testResults.forEach(result => {
      if (!report.categories[result.category]) {
        report.categories[result.category] = {
          total: 0,
          passed: 0,
          failed: 0,
          skipped: 0,
          tests: []
        };
      }
      
      const category = report.categories[result.category];
      category.total++;
      category[result.status.toLowerCase()]++;
      category.tests.push(result);
    });

    return report;
  }

  printSummary() {
    const report = this.generateDetailedReport();
    
    console.log('\n' + '='.repeat(80));
    console.log('🧪 COMPREHENSIVE MCP INTEGRATION TEST REPORT');
    console.log('='.repeat(80));
    
    this.log('info', 'Overall Summary', {
      total: report.summary.total,
      passed: report.summary.passed,
      failed: report.summary.failed,
      skipped: report.summary.skipped,
      successRate: `${report.summary.successRate}%`
    });

    console.log('\n📊 Results by Category:');
    Object.entries(report.categories).forEach(([category, stats]) => {
      const successRate = stats.total > 0 ? 
        ((stats.passed / (stats.passed + stats.failed)) * 100).toFixed(1) : '0.0';
      
      console.log(`  ${category}:`);
      console.log(`    ✅ Passed: ${stats.passed}`);
      console.log(`    ❌ Failed: ${stats.failed}`);
      console.log(`    ⏭️  Skipped: ${stats.skipped}`);
      console.log(`    📈 Success Rate: ${successRate}%`);
    });

    if (report.summary.failed > 0) {
      console.log('\n❌ Failed Tests:');
      this.testResults
        .filter(result => result.status === 'FAIL')
        .forEach(result => {
          console.log(`  - [${result.category}] ${result.name}: ${result.error}`);
        });
    }

    if (report.summary.skipped > 0) {
      console.log('\n⏭️ Skipped Tests:');
      this.testResults
        .filter(result => result.status === 'SKIP')
        .forEach(result => {
          console.log(`  - [${result.category}] ${result.name}: ${result.reason}`);
        });
    }

    console.log('\n🎯 Test Results Summary:');
    this.testResults.forEach(result => {
      const icon = result.status === 'PASS' ? '✅' : 
                   result.status === 'FAIL' ? '❌' : '⏭️';
      const duration = result.duration ? ` (${result.duration}ms)` : '';
      console.log(`  ${icon} [${result.category}] ${result.name}${duration}`);
    });

    console.log(`\n🏆 Overall Success Rate: ${report.summary.successRate}%`);
    
    if (report.summary.failed === 0) {
      this.log('success', '🎉 All tests passed! MCP integration is working correctly.');
    } else {
      this.log('warning', '⚠️ Some tests failed. Please review the MCP service configuration.');
    }

    // Save report to file
    const reportPath = path.join(__dirname, 'mcp-test-report.json');
    fs.writeFileSync(reportPath, JSON.stringify(report, null, 2));
    this.log('info', `Detailed report saved to: ${reportPath}`);

    return report.summary.failed === 0;
  }

  async runAllTests() {
    this.log('info', '🚀 Starting Comprehensive MCP Integration Tests...');
    this.log('info', `🔗 Testing against: ${this.config.baseUrl}`);
    this.log('info', `🔌 WebSocket endpoint: ${this.config.wsUrl}`);
    
    try {
      // Core functionality tests
      await this.testHealthChecks();
      await this.testMcpEndpoints();
      await this.testErrorHandling();
      await this.testPolicyEnforcement();
      
      // WebSocket tests
      try {
        await this.testWebSocketConnection();
        this.passedTests++; // Count WebSocket tests as one passed test
        this.testResults.push({
          name: 'WebSocket Integration',
          status: 'PASS',
          category: 'websocket'
        });
      } catch (error) {
        await this.runTest('WebSocket Integration', async () => {
          throw error;
        }, 'websocket');
      }
      
      // Performance tests
      await this.testPerformanceMetrics();
      
      // Integration tests
      await this.testIntegrationWithExistingServices();
      
    } catch (error) {
      this.log('error', 'Test suite execution failed', { error: error.message });
    }

    return this.printSummary();
  }
}

// Run tests if this script is executed directly
if (require.main === module) {
  const tester = new ComprehensiveMcpTest();
  
  tester.runAllTests().then(success => {
    process.exit(success ? 0 : 1);
  }).catch(error => {
    console.error('❌ Test suite failed to run:', error.message);
    process.exit(1);
  });
}

module.exports = ComprehensiveMcpTest;
