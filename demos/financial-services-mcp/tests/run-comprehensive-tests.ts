/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Comprehensive Test Runner for Financial Services MCP
 * Orchestrates all test suites with detailed reporting
 */

import { spawn } from 'child_process';
import fs from 'fs/promises';
import path from 'path';
import { performance } from 'perf_hooks';

interface TestSuite {
  name: string;
  description: string;
  file: string;
  timeout: number;
  priority: 'critical' | 'high' | 'medium' | 'low';
  dependencies: string[];
  estimatedDurationMin: number;
}

interface TestResult {
  suiteName: string;
  passed: boolean;
  duration: number;
  testCount: number;
  passedTests: number;
  failedTests: number;
  skippedTests: number;
  errorMessage?: string;
  coverage?: {
    lines: number;
    functions: number;
    branches: number;
    statements: number;
  };
}

interface ComprehensiveTestReport {
  startTime: number;
  endTime: number;
  totalDuration: number;
  suiteResults: TestResult[];
  overallResults: {
    totalSuites: number;
    passedSuites: number;
    failedSuites: number;
    totalTests: number;
    passedTests: number;
    failedTests: number;
    skippedTests: number;
    overallPassed: boolean;
  };
  performanceMetrics: {
    avgSuiteDuration: number;
    longestSuite: string;
    shortestSuite: string;
    criticalSuitesPassed: boolean;
  };
  recommendations: string[];
}

class ComprehensiveTestRunner {
  private testSuites: TestSuite[] = [
    {
      name: 'Enhanced Integration Tests',
      description: 'Comprehensive performance and accuracy validation',
      file: 'enhanced-test-suite.ts',
      timeout: 600000, // 10 minutes
      priority: 'critical',
      dependencies: [],
      estimatedDurationMin: 8
    },
    {
      name: 'Original Integration Tests',
      description: 'Baseline integration testing suite',
      file: 'integration-test-suite.ts',
      timeout: 300000, // 5 minutes
      priority: 'high',
      dependencies: [],
      estimatedDurationMin: 4
    },
    {
      name: 'Security and Audit Tests',
      description: 'Security vulnerability and audit trail validation',
      file: 'security-audit-test-suite.ts',
      timeout: 420000, // 7 minutes
      priority: 'critical',
      dependencies: [],
      estimatedDurationMin: 6
    },
    {
      name: 'Stress Tests',
      description: 'Extreme load and breaking point analysis',
      file: 'stress-test-suite.ts',
      timeout: 900000, // 15 minutes
      priority: 'medium',
      dependencies: ['Enhanced Integration Tests'],
      estimatedDurationMin: 12
    }
  ];
  
  private results: TestResult[] = [];
  private startTime: number = 0;
  
  async runAllTests(options: {
    skipStress?: boolean;
    skipSecurity?: boolean;
    parallel?: boolean;
    generateReport?: boolean;
    outputDir?: string;
  } = {}): Promise<ComprehensiveTestReport> {
    this.startTime = Date.now();
    
    console.log('🚀 Starting Comprehensive Financial Services MCP Test Suite');
    console.log('=' .repeat(80));
    
    // Filter test suites based on options
    let suitesToRun = this.testSuites.filter(suite => {
      if (options.skipStress && suite.name.includes('Stress')) return false;
      if (options.skipSecurity && suite.name.includes('Security')) return false;
      return true;
    });
    
    // Sort by priority and dependencies
    suitesToRun = this.resolveDependencies(suitesToRun);
    
    const estimatedDuration = suitesToRun.reduce((sum, suite) => sum + suite.estimatedDurationMin, 0);
    console.log(`📅 Estimated Duration: ${estimatedDuration} minutes`);
    console.log(`🧪 Test Suites: ${suitesToRun.length}`);
    console.log(`⚡ Parallel Execution: ${options.parallel ? 'Enabled' : 'Disabled'}`);
    console.log('');
    
    try {
      if (options.parallel) {
        await this.runTestsInParallel(suitesToRun);
      } else {
        await this.runTestsSequentially(suitesToRun);
      }
      
      const report = this.generateReport();
      
      if (options.generateReport) {
        await this.saveReport(report, options.outputDir);
      }
      
      this.printSummary(report);
      
      return report;
      
    } catch (error) {
      console.error('❌ Test execution failed:', error);
      throw error;
    }
  }
  
  private resolveDependencies(suites: TestSuite[]): TestSuite[] {
    const resolved: TestSuite[] = [];
    const visited = new Set<string>();
    const visiting = new Set<string>();
    
    const visit = (suite: TestSuite) => {
      if (visiting.has(suite.name)) {
        throw new Error(`Circular dependency detected: ${suite.name}`);
      }
      
      if (visited.has(suite.name)) {
        return;
      }
      
      visiting.add(suite.name);
      
      for (const depName of suite.dependencies) {
        const dependency = suites.find(s => s.name === depName);
        if (dependency) {
          visit(dependency);
        }
      }
      
      visiting.delete(suite.name);
      visited.add(suite.name);
      resolved.push(suite);
    };
    
    for (const suite of suites) {
      visit(suite);
    }
    
    return resolved;
  }
  
  private async runTestsSequentially(suites: TestSuite[]): Promise<void> {
    for (let i = 0; i < suites.length; i++) {
      const suite = suites[i];
      
      console.log(`\n🧪 Running Suite ${i + 1}/${suites.length}: ${suite.name}`);
      console.log(`📝 Description: ${suite.description}`);
      console.log(`⏱️  Priority: ${suite.priority.toUpperCase()}`);
      console.log(`🕐 Estimated: ${suite.estimatedDurationMin} minutes`);
      console.log('-'.repeat(60));
      
      const result = await this.runSingleTest(suite);
      this.results.push(result);
      
      this.printSuiteResult(result);
      
      // If a critical test fails, consider stopping
      if (!result.passed && suite.priority === 'critical') {
        console.log('💥 Critical test suite failed - considering early termination');
        
        // Ask user if they want to continue (in a real scenario)
        // For automated testing, we'll continue but mark it
        console.log('⚠️  Continuing with remaining tests...');
      }
    }
  }
  
  private async runTestsInParallel(suites: TestSuite[]): Promise<void> {
    // Group suites by dependency level
    const levels = this.groupByDependencyLevel(suites);
    
    for (let level = 0; level < levels.length; level++) {
      const levelSuites = levels[level];
      
      console.log(`\n🚀 Running Level ${level + 1} tests in parallel (${levelSuites.length} suites)`);
      
      const promises = levelSuites.map(suite => this.runSingleTest(suite));
      const results = await Promise.all(promises);
      
      this.results.push(...results);
      
      for (const result of results) {
        this.printSuiteResult(result);
      }
    }
  }
  
  private groupByDependencyLevel(suites: TestSuite[]): TestSuite[][] {
    const levels: TestSuite[][] = [];
    const processed = new Set<string>();
    
    while (processed.size < suites.length) {
      const currentLevel: TestSuite[] = [];
      
      for (const suite of suites) {
        if (processed.has(suite.name)) continue;
        
        const dependenciesMet = suite.dependencies.every(dep => processed.has(dep));
        if (dependenciesMet) {
          currentLevel.push(suite);
        }
      }
      
      if (currentLevel.length === 0) {
        throw new Error('Unresolvable dependencies detected');
      }
      
      levels.push(currentLevel);
      currentLevel.forEach(suite => processed.add(suite.name));
    }
    
    return levels;
  }
  
  private async runSingleTest(suite: TestSuite): Promise<TestResult> {
    const startTime = performance.now();
    
    return new Promise((resolve) => {
      const testFile = path.join(__dirname, suite.file);
      
      const jestProcess = spawn('npx', ['jest', testFile, '--verbose', '--coverage'], {
        stdio: ['pipe', 'pipe', 'pipe'],
        cwd: process.cwd(),
        timeout: suite.timeout
      });
      
      let stdout = '';
      let stderr = '';
      
      jestProcess.stdout?.on('data', (data) => {
        const output = data.toString();
        stdout += output;
        
        // Stream output to console with suite prefix
        const lines = output.split('\n').filter(line => line.trim());
        for (const line of lines) {
          console.log(`[${suite.name}] ${line}`);
        }
      });
      
      jestProcess.stderr?.on('data', (data) => {
        const output = data.toString();
        stderr += output;
        
        // Stream error output
        const lines = output.split('\n').filter(line => line.trim());
        for (const line of lines) {
          console.error(`[${suite.name}] ERROR: ${line}`);
        }
      });
      
      jestProcess.on('close', (code) => {
        const duration = performance.now() - startTime;
        const result = this.parseJestOutput(suite.name, stdout, stderr, code === 0, duration);
        resolve(result);
      });
      
      jestProcess.on('error', (error) => {
        const duration = performance.now() - startTime;
        resolve({
          suiteName: suite.name,
          passed: false,
          duration,
          testCount: 0,
          passedTests: 0,
          failedTests: 0,
          skippedTests: 0,
          errorMessage: `Process error: ${error.message}`
        });
      });
      
      // Handle timeout
      setTimeout(() => {
        if (!jestProcess.killed) {
          jestProcess.kill();
          const duration = performance.now() - startTime;
          resolve({
            suiteName: suite.name,
            passed: false,
            duration,
            testCount: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            errorMessage: `Test suite timed out after ${suite.timeout}ms`
          });
        }
      }, suite.timeout);
    });
  }
  
  private parseJestOutput(
    suiteName: string,
    stdout: string,
    stderr: string,
    passed: boolean,
    duration: number
  ): TestResult {
    let testCount = 0;
    let passedTests = 0;
    let failedTests = 0;
    let skippedTests = 0;
    let coverage;
    
    // Parse Jest output for test counts
    const testSummaryMatch = stdout.match(/Tests:\s+(\d+)\s+failed,\s+(\d+)\s+passed,\s+(\d+)\s+total/);
    if (testSummaryMatch) {
      failedTests = parseInt(testSummaryMatch[1]);
      passedTests = parseInt(testSummaryMatch[2]);
      testCount = parseInt(testSummaryMatch[3]);
    } else {
      // Alternative parsing
      const passedMatch = stdout.match(/(\d+)\s+passed/);
      const failedMatch = stdout.match(/(\d+)\s+failed/);
      const skippedMatch = stdout.match(/(\d+)\s+skipped/);
      
      if (passedMatch) passedTests = parseInt(passedMatch[1]);
      if (failedMatch) failedTests = parseInt(failedMatch[1]);
      if (skippedMatch) skippedTests = parseInt(skippedMatch[1]);
      
      testCount = passedTests + failedTests + skippedTests;
    }
    
    // Parse coverage if available
    const coverageMatch = stdout.match(/All files\s+\|\s+([\d.]+)\s+\|\s+([\d.]+)\s+\|\s+([\d.]+)\s+\|\s+([\d.]+)/);
    if (coverageMatch) {
      coverage = {
        statements: parseFloat(coverageMatch[1]),
        branches: parseFloat(coverageMatch[2]),
        functions: parseFloat(coverageMatch[3]),
        lines: parseFloat(coverageMatch[4])
      };
    }
    
    let errorMessage;
    if (!passed) {
      // Extract error message from stderr or stdout
      if (stderr.trim()) {
        errorMessage = stderr.split('\n')[0]; // First line of error
      } else {
        const failureMatch = stdout.match(/FAIL\s+.*\n(.*)/);
        if (failureMatch) {
          errorMessage = failureMatch[1];
        } else {
          errorMessage = 'Test suite failed';
        }
      }
    }
    
    return {
      suiteName,
      passed,
      duration,
      testCount,
      passedTests,
      failedTests,
      skippedTests,
      errorMessage,
      coverage
    };
  }
  
  private generateReport(): ComprehensiveTestReport {
    const endTime = Date.now();
    const totalDuration = endTime - this.startTime;
    
    const totalSuites = this.results.length;
    const passedSuites = this.results.filter(r => r.passed).length;
    const failedSuites = totalSuites - passedSuites;
    
    const totalTests = this.results.reduce((sum, r) => sum + r.testCount, 0);
    const passedTests = this.results.reduce((sum, r) => sum + r.passedTests, 0);
    const failedTests = this.results.reduce((sum, r) => sum + r.failedTests, 0);
    const skippedTests = this.results.reduce((sum, r) => sum + r.skippedTests, 0);
    
    const overallPassed = failedSuites === 0 && failedTests === 0;
    
    // Performance metrics
    const avgSuiteDuration = totalSuites > 0 ? totalDuration / totalSuites : 0;
    const longestSuite = this.results.reduce((longest, current) => 
      current.duration > longest.duration ? current : longest, this.results[0] || { duration: 0, suiteName: 'None' });
    const shortestSuite = this.results.reduce((shortest, current) => 
      current.duration < shortest.duration ? current : shortest, this.results[0] || { duration: 0, suiteName: 'None' });
    
    const criticalSuites = this.testSuites.filter(s => s.priority === 'critical').map(s => s.name);
    const criticalResults = this.results.filter(r => criticalSuites.includes(r.suiteName));
    const criticalSuitesPassed = criticalResults.every(r => r.passed);
    
    // Generate recommendations
    const recommendations = this.generateRecommendations();
    
    return {
      startTime: this.startTime,
      endTime,
      totalDuration,
      suiteResults: this.results,
      overallResults: {
        totalSuites,
        passedSuites,
        failedSuites,
        totalTests,
        passedTests,
        failedTests,
        skippedTests,
        overallPassed
      },
      performanceMetrics: {
        avgSuiteDuration,
        longestSuite: longestSuite.suiteName,
        shortestSuite: shortestSuite.suiteName,
        criticalSuitesPassed
      },
      recommendations
    };
  }
  
  private generateRecommendations(): string[] {
    const recommendations: string[] = [];
    
    // Check for failed critical tests
    const criticalSuites = this.testSuites.filter(s => s.priority === 'critical').map(s => s.name);
    const failedCritical = this.results.filter(r => criticalSuites.includes(r.suiteName) && !r.passed);
    
    if (failedCritical.length > 0) {
      recommendations.push(`Critical test suites failed: ${failedCritical.map(r => r.suiteName).join(', ')} - immediate attention required`);
    }
    
    // Check for performance issues
    const longRunningSuites = this.results.filter(r => r.duration > 300000); // 5 minutes
    if (longRunningSuites.length > 0) {
      recommendations.push(`Long-running test suites detected: ${longRunningSuites.map(r => r.suiteName).join(', ')} - consider optimization`);
    }
    
    // Check for low test coverage
    const lowCoverageSuites = this.results.filter(r => r.coverage && r.coverage.lines < 80);
    if (lowCoverageSuites.length > 0) {
      recommendations.push(`Low test coverage in: ${lowCoverageSuites.map(r => r.suiteName).join(', ')} - add more test cases`);
    }
    
    // Check for high failure rate
    const failureRate = this.results.reduce((sum, r) => sum + r.failedTests, 0) / Math.max(1, this.results.reduce((sum, r) => sum + r.testCount, 0));
    if (failureRate > 0.05) { // More than 5% failure rate
      recommendations.push(`High test failure rate (${(failureRate * 100).toFixed(1)}%) - review and fix failing tests`);
    }
    
    // Positive recommendations
    if (recommendations.length === 0) {
      recommendations.push('All tests passing - system is functioning within expected parameters');
      recommendations.push('Consider implementing continuous performance monitoring to maintain these standards');
    }
    
    return recommendations;
  }
  
  private printSuiteResult(result: TestResult): void {
    const status = result.passed ? '✅ PASSED' : '❌ FAILED';
    const duration = (result.duration / 1000).toFixed(1);
    
    console.log(`\n📊 ${result.suiteName}: ${status}`);
    console.log(`   Duration: ${duration}s`);
    console.log(`   Tests: ${result.passedTests}/${result.testCount} passed`);
    
    if (result.failedTests > 0) {
      console.log(`   ❌ Failed: ${result.failedTests}`);
    }
    
    if (result.skippedTests > 0) {
      console.log(`   ⏭️  Skipped: ${result.skippedTests}`);
    }
    
    if (result.coverage) {
      console.log(`   📈 Coverage: ${result.coverage.lines.toFixed(1)}% lines, ${result.coverage.functions.toFixed(1)}% functions`);
    }
    
    if (result.errorMessage) {
      console.log(`   💥 Error: ${result.errorMessage}`);
    }
  }
  
  private printSummary(report: ComprehensiveTestReport): void {
    const duration = (report.totalDuration / 1000 / 60).toFixed(1);
    const overallStatus = report.overallResults.overallPassed ? '🎉 ALL TESTS PASSED' : '⚠️  SOME TESTS FAILED';
    
    console.log('\n' + '='.repeat(80));
    console.log('📋 COMPREHENSIVE TEST SUITE SUMMARY');
    console.log('='.repeat(80));
    console.log(`\n${overallStatus}\n`);
    
    console.log(`⏱️  Total Duration: ${duration} minutes`);
    console.log(`🧪 Test Suites: ${report.overallResults.passedSuites}/${report.overallResults.totalSuites} passed`);
    console.log(`✅ Individual Tests: ${report.overallResults.passedTests}/${report.overallResults.totalTests} passed`);
    
    if (report.overallResults.failedTests > 0) {
      console.log(`❌ Failed Tests: ${report.overallResults.failedTests}`);
    }
    
    if (report.overallResults.skippedTests > 0) {
      console.log(`⏭️  Skipped Tests: ${report.overallResults.skippedTests}`);
    }
    
    console.log(`\n🏆 Performance Metrics:`);
    console.log(`   Critical Suites: ${report.performanceMetrics.criticalSuitesPassed ? '✅ PASSED' : '❌ FAILED'}`);
    console.log(`   Longest Suite: ${report.performanceMetrics.longestSuite}`);
    console.log(`   Shortest Suite: ${report.performanceMetrics.shortestSuite}`);
    
    if (report.recommendations.length > 0) {
      console.log(`\n💡 Recommendations:`);
      for (const recommendation of report.recommendations) {
        console.log(`   • ${recommendation}`);
      }
    }
    
    console.log('\n' + '='.repeat(80));
  }
  
  private async saveReport(report: ComprehensiveTestReport, outputDir: string = './reports'): Promise<void> {
    try {
      await fs.mkdir(outputDir, { recursive: true });
      
      const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
      const filename = `comprehensive-test-report-${timestamp}.json`;
      const filepath = path.join(outputDir, filename);
      
      await fs.writeFile(filepath, JSON.stringify(report, null, 2));
      
      // Also generate a human-readable markdown report
      const markdownReport = this.generateMarkdownReport(report);
      const markdownFilename = `comprehensive-test-report-${timestamp}.md`;
      const markdownFilepath = path.join(outputDir, markdownFilename);
      
      await fs.writeFile(markdownFilepath, markdownReport);
      
      console.log(`\n📄 Reports saved:`);
      console.log(`   JSON: ${filepath}`);
      console.log(`   Markdown: ${markdownFilepath}`);
      
    } catch (error) {
      console.error('Failed to save report:', error);
    }
  }
  
  private generateMarkdownReport(report: ComprehensiveTestReport): string {
    const duration = (report.totalDuration / 1000 / 60).toFixed(1);
    const timestamp = new Date(report.startTime).toISOString();
    
    const lines = [
      '# Financial Services MCP - Comprehensive Test Report',
      '',
      `**Generated:** ${timestamp}`,
      `**Duration:** ${duration} minutes`,
      `**Overall Status:** ${report.overallResults.overallPassed ? '✅ PASSED' : '❌ FAILED'}`,
      '',
      '## Executive Summary',
      '',
      `- **Test Suites:** ${report.overallResults.passedSuites}/${report.overallResults.totalSuites} passed`,
      `- **Individual Tests:** ${report.overallResults.passedTests}/${report.overallResults.totalTests} passed`,
      `- **Critical Suites:** ${report.performanceMetrics.criticalSuitesPassed ? '✅ PASSED' : '❌ FAILED'}`,
      '',
      '## Test Suite Results',
      ''
    ];
    
    for (const result of report.suiteResults) {
      const status = result.passed ? '✅' : '❌';
      const duration = (result.duration / 1000).toFixed(1);
      
      lines.push(`### ${result.suiteName} ${status}`);
      lines.push('');
      lines.push(`- **Duration:** ${duration}s`);
      lines.push(`- **Tests:** ${result.passedTests}/${result.testCount} passed`);
      
      if (result.failedTests > 0) {
        lines.push(`- **Failed:** ${result.failedTests}`);
      }
      
      if (result.coverage) {
        lines.push(`- **Coverage:** ${result.coverage.lines.toFixed(1)}% lines`);
      }
      
      if (result.errorMessage) {
        lines.push(`- **Error:** \`${result.errorMessage}\``);
      }
      
      lines.push('');
    }
    
    if (report.recommendations.length > 0) {
      lines.push('## Recommendations');
      lines.push('');
      
      for (const recommendation of report.recommendations) {
        lines.push(`- ${recommendation}`);
      }
    }
    
    return lines.join('\n');
  }
}

// CLI interface
async function main() {
  const args = process.argv.slice(2);
  const options = {
    skipStress: args.includes('--skip-stress'),
    skipSecurity: args.includes('--skip-security'),
    parallel: args.includes('--parallel'),
    generateReport: !args.includes('--no-report'),
    outputDir: args.find(arg => arg.startsWith('--output='))?.split('=')[1]
  };
  
  const runner = new ComprehensiveTestRunner();
  
  try {
    const report = await runner.runAllTests(options);
    
    process.exit(report.overallResults.overallPassed ? 0 : 1);
    
  } catch (error) {
    console.error('💥 Test runner failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

export { ComprehensiveTestRunner, TestResult, ComprehensiveTestReport };
