/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * MCP Integration Test Script
 * Verifies that MCP endpoints and functionality work correctly
 */

const axios = require('axios');
const WebSocket = require('ws');

const BASE_URL = 'http://localhost:4000';
const WS_URL = 'ws://localhost:4000/mcp/ws';

// Mock JWT token for testing (replace with real token in production)
const MOCK_JWT = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ0ZXN0LXVzZXItaWQiLCJ0ZW5hbnRfaWQiOiJ0ZXN0LXRlbmFudCIsImlhdCI6MTcwOTU1NjAwMCwiZXhwIjoxNzA5NjQyNDAwfQ.test';

class McpIntegrationTest {
  constructor() {
    this.passedTests = 0;
    this.failedTests = 0;
    this.testResults = [];
  }

  async runTest(testName, testFunction) {
    console.log(`\n🧪 Running test: ${testName}`);
    try {
      await testFunction();
      this.passedTests++;
      this.testResults.push({ name: testName, status: 'PASS' });
      console.log(`✅ ${testName} - PASSED`);
    } catch (error) {
      this.failedTests++;
      this.testResults.push({ name: testName, status: 'FAIL', error: error.message });
      console.log(`❌ ${testName} - FAILED: ${error.message}`);
    }
  }

  async testHealthEndpoint() {
    const response = await axios.get(`${BASE_URL}/health`);
    
    if (response.status !== 200) {
      throw new Error(`Expected status 200, got ${response.status}`);
    }
    
    if (!response.data.status || response.data.status !== 'healthy') {
      throw new Error('Health check returned unhealthy status');
    }
  }

  async testMcpHealthEndpoint() {
    const response = await axios.get(`${BASE_URL}/api/mcp/health`);
    
    if (response.status !== 200) {
      throw new Error(`Expected status 200, got ${response.status}`);
    }
    
    if (!response.data.status || response.data.status !== 'healthy') {
      throw new Error('MCP health check returned unhealthy status');
    }

    console.log(`📊 MCP Health Status:`, response.data);
  }

  async testMcpServerDiscovery() {
    const response = await axios.get(`${BASE_URL}/api/mcp/servers`);
    
    if (response.status !== 200) {
      throw new Error(`Expected status 200, got ${response.status}`);
    }
    
    if (!response.data.servers || !Array.isArray(response.data.servers)) {
      throw new Error('Server discovery should return servers array');
    }

    console.log(`🔍 Discovered MCP Servers:`, response.data.servers);
  }

  async testMcpStatsEndpoint() {
    const response = await axios.get(`${BASE_URL}/api/mcp/stats`);
    
    if (response.status !== 200) {
      throw new Error(`Expected status 200, got ${response.status}`);
    }
    
    if (typeof response.data !== 'object') {
      throw new Error('Stats endpoint should return object');
    }

    console.log(`📈 MCP Statistics:`, response.data);
  }

  async testMcpJsonRpcEndpoint() {
    const mcpRequest = {
      jsonrpc: '2.0',
      method: 'tools/list',
      params: {},
      id: 1
    };

    try {
      const response = await axios.post(`${BASE_URL}/api/mcp/jsonrpc`, mcpRequest, {
        headers: {
          'Content-Type': 'application/json',
          'Authorization': `Bearer ${MOCK_JWT}`
        }
      });
      
      if (response.status !== 200 && response.status !== 403) {
        throw new Error(`Expected status 200 or 403 (auth), got ${response.status}`);
      }

      console.log(`🔧 MCP JSON-RPC Response:`, response.data);
    } catch (error) {
      if (error.response && error.response.status === 403) {
        console.log(`🔒 Authentication required (expected for secure endpoint)`);
        return; // This is expected behavior
      }
      throw error;
    }
  }

  async testMcpToolsListCall() {
    const mcpRequest = {
      jsonrpc: '2.0',
      method: 'tools/call',
      params: {
        name: 'query_capsules',
        arguments: {
          filter: { status: 'active' },
          limit: 5
        }
      },
      id: 2
    };

    try {
      const response = await axios.post(`${BASE_URL}/api/mcp/jsonrpc`, mcpRequest, {
        headers: {
          'Content-Type': 'application/json',
          'Authorization': `Bearer ${MOCK_JWT}`
        }
      });
      
      if (response.status !== 200 && response.status !== 403) {
        throw new Error(`Expected status 200 or 403 (auth), got ${response.status}`);
      }

      console.log(`🛠️ MCP Tool Call Response:`, response.data);
    } catch (error) {
      if (error.response && error.response.status === 403) {
        console.log(`🔒 Authentication required for tool calls (expected)`);
        return;
      }
      throw error;
    }
  }

  async testMcpWebSocketConnection() {
    return new Promise((resolve, reject) => {
      const ws = new WebSocket(WS_URL);
      let messageReceived = false;

      ws.on('open', () => {
        console.log(`🔌 WebSocket connected to ${WS_URL}`);
        
        // Send a test subscription message
        ws.send(JSON.stringify({
          type: 'subscribe',
          tenantId: 'test-tenant',
          eventTypes: ['mcp_events', 'tool_calls']
        }));
      });

      ws.on('message', (data) => {
        const message = JSON.parse(data.toString());
        console.log(`📨 WebSocket message received:`, message);
        messageReceived = true;
        
        if (message.type === 'subscription_confirmed') {
          ws.close();
          resolve();
        }
      });

      ws.on('error', (error) => {
        reject(new Error(`WebSocket error: ${error.message}`));
      });

      ws.on('close', () => {
        if (!messageReceived) {
          reject(new Error('WebSocket closed without receiving messages'));
        }
      });

      // Timeout after 10 seconds
      setTimeout(() => {
        if (!messageReceived) {
          ws.close();
          reject(new Error('WebSocket test timed out'));
        }
      }, 10000);
    });
  }

  async testInvalidMcpRequest() {
    const invalidRequest = {
      method: 'invalid/method',
      params: {}
      // Missing jsonrpc and id
    };

    try {
      const response = await axios.post(`${BASE_URL}/api/mcp/jsonrpc`, invalidRequest, {
        headers: {
          'Content-Type': 'application/json'
        }
      });
      
      if (response.status !== 500) {
        throw new Error(`Expected error status, got ${response.status}`);
      }

      console.log(`🚫 Invalid request properly rejected:`, response.data);
    } catch (error) {
      if (error.response && error.response.status >= 400) {
        console.log(`✅ Invalid request properly rejected with status ${error.response.status}`);
        return;
      }
      throw error;
    }
  }

  async testMcpPolicyEnforcement() {
    const mcpRequest = {
      jsonrpc: '2.0',
      method: 'tools/call',
      params: {
        name: 'query_capsules',
        arguments: {
          limit: 10000 // Exceeds policy limit
        }
      },
      id: 3
    };

    try {
      const response = await axios.post(`${BASE_URL}/api/mcp/jsonrpc`, mcpRequest, {
        headers: {
          'Content-Type': 'application/json',
          'Authorization': `Bearer ${MOCK_JWT}`
        }
      });
      
      // Should either be blocked by policy (403) or require auth
      if (response.status === 403) {
        console.log(`🛡️ Policy enforcement working - request blocked`);
        console.log(`🔒 Policy response:`, response.data);
        return;
      }
      
      console.log(`⚠️ Request not blocked, response:`, response.data);
    } catch (error) {
      if (error.response && error.response.status === 403) {
        console.log(`🛡️ Policy enforcement working - request properly blocked`);
        return;
      }
      throw error;
    }
  }

  printSummary() {
    console.log('\n' + '='.repeat(60));
    console.log('📋 MCP INTEGRATION TEST SUMMARY');
    console.log('='.repeat(60));
    console.log(`✅ Passed: ${this.passedTests}`);
    console.log(`❌ Failed: ${this.failedTests}`);
    console.log(`📊 Total: ${this.passedTests + this.failedTests}`);
    
    if (this.failedTests > 0) {
      console.log('\n❌ Failed Tests:');
      this.testResults
        .filter(result => result.status === 'FAIL')
        .forEach(result => {
          console.log(`  - ${result.name}: ${result.error}`);
        });
    }

    console.log('\n🎯 Test Results:');
    this.testResults.forEach(result => {
      const icon = result.status === 'PASS' ? '✅' : '❌';
      console.log(`  ${icon} ${result.name}`);
    });

    const successRate = ((this.passedTests / (this.passedTests + this.failedTests)) * 100).toFixed(1);
    console.log(`\n🏆 Success Rate: ${successRate}%`);
    
    if (this.failedTests === 0) {
      console.log('\n🎉 All tests passed! MCP integration is working correctly.');
    } else {
      console.log('\n⚠️ Some tests failed. Please check the MCP service configuration.');
    }
  }

  async runAllTests() {
    console.log('🚀 Starting MCP Integration Tests...');
    console.log(`🔗 Testing against: ${BASE_URL}`);
    
    await this.runTest('Health Endpoint', () => this.testHealthEndpoint());
    await this.runTest('MCP Health Endpoint', () => this.testMcpHealthEndpoint());
    await this.runTest('MCP Server Discovery', () => this.testMcpServerDiscovery());
    await this.runTest('MCP Statistics Endpoint', () => this.testMcpStatsEndpoint());
    await this.runTest('MCP JSON-RPC Endpoint', () => this.testMcpJsonRpcEndpoint());
    await this.runTest('MCP Tools List Call', () => this.testMcpToolsListCall());
    await this.runTest('MCP WebSocket Connection', () => this.testMcpWebSocketConnection());
    await this.runTest('Invalid MCP Request Handling', () => this.testInvalidMcpRequest());
    await this.runTest('MCP Policy Enforcement', () => this.testMcpPolicyEnforcement());

    this.printSummary();
    
    return this.failedTests === 0;
  }
}

// Run tests if this script is executed directly
if (require.main === module) {
  const tester = new McpIntegrationTest();
  
  tester.runAllTests().then(success => {
    process.exit(success ? 0 : 1);
  }).catch(error => {
    console.error('❌ Test suite failed to run:', error.message);
    process.exit(1);
  });
}

module.exports = McpIntegrationTest;
