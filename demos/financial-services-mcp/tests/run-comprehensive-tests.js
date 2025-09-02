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
class ComprehensiveTestRunner {
    testSuites = [
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
    results = [];
    startTime = 0;
    async runAllTests(options = {}) {
        this.startTime = Date.now();
        console.log('🚀 Starting Comprehensive Financial Services MCP Test Suite');
        console.log('='.repeat(80));
        // Filter test suites based on options
        let suitesToRun = this.testSuites.filter(suite => {
            if (options.skipStress && suite.name.includes('Stress'))
                return false;
            if (options.skipSecurity && suite.name.includes('Security'))
                return false;
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
            }
            else {
                await this.runTestsSequentially(suitesToRun);
            }
            const report = this.generateReport();
            if (options.generateReport) {
                await this.saveReport(report, options.outputDir);
            }
            this.printSummary(report);
            return report;
        }
        catch (error) {
            console.error('❌ Test execution failed:', error);
            throw error;
        }
    }
    resolveDependencies(suites) {
        const resolved = [];
        const visited = new Set();
        const visiting = new Set();
        const visit = (suite) => {
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
    async runTestsSequentially(suites) {
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
    async runTestsInParallel(suites) {
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
    groupByDependencyLevel(suites) {
        const levels = [];
        const processed = new Set();
        while (processed.size < suites.length) {
            const currentLevel = [];
            for (const suite of suites) {
                if (processed.has(suite.name))
                    continue;
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
    async runSingleTest(suite) {
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
    parseJestOutput(suiteName, stdout, stderr, passed, duration) {
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
        }
        else {
            // Alternative parsing
            const passedMatch = stdout.match(/(\d+)\s+passed/);
            const failedMatch = stdout.match(/(\d+)\s+failed/);
            const skippedMatch = stdout.match(/(\d+)\s+skipped/);
            if (passedMatch)
                passedTests = parseInt(passedMatch[1]);
            if (failedMatch)
                failedTests = parseInt(failedMatch[1]);
            if (skippedMatch)
                skippedTests = parseInt(skippedMatch[1]);
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
            }
            else {
                const failureMatch = stdout.match(/FAIL\s+.*\n(.*)/);
                if (failureMatch) {
                    errorMessage = failureMatch[1];
                }
                else {
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
    generateReport() {
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
        const longestSuite = this.results.reduce((longest, current) => current.duration > longest.duration ? current : longest, this.results[0] || { duration: 0, suiteName: 'None' });
        const shortestSuite = this.results.reduce((shortest, current) => current.duration < shortest.duration ? current : shortest, this.results[0] || { duration: 0, suiteName: 'None' });
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
    generateRecommendations() {
        const recommendations = [];
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
    printSuiteResult(result) {
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
    printSummary(report) {
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
    async saveReport(report, outputDir = './reports') {
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
        }
        catch (error) {
            console.error('Failed to save report:', error);
        }
    }
    generateMarkdownReport(report) {
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
    }
    catch (error) {
        console.error('💥 Test runner failed:', error);
        process.exit(1);
    }
}
if (require.main === module) {
    main();
}
export { ComprehensiveTestRunner };
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoicnVuLWNvbXByZWhlbnNpdmUtdGVzdHMuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyJydW4tY29tcHJlaGVuc2l2ZS10ZXN0cy50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQTs7Ozs7O0dBTUc7QUFFSCxPQUFPLEVBQUUsS0FBSyxFQUFFLE1BQU0sZUFBZSxDQUFDO0FBQ3RDLE9BQU8sRUFBRSxNQUFNLGFBQWEsQ0FBQztBQUM3QixPQUFPLElBQUksTUFBTSxNQUFNLENBQUM7QUFDeEIsT0FBTyxFQUFFLFdBQVcsRUFBRSxNQUFNLFlBQVksQ0FBQztBQXFEekMsTUFBTSx1QkFBdUI7SUFDbkIsVUFBVSxHQUFnQjtRQUNoQztZQUNFLElBQUksRUFBRSw0QkFBNEI7WUFDbEMsV0FBVyxFQUFFLG1EQUFtRDtZQUNoRSxJQUFJLEVBQUUsd0JBQXdCO1lBQzlCLE9BQU8sRUFBRSxNQUFNLEVBQUUsYUFBYTtZQUM5QixRQUFRLEVBQUUsVUFBVTtZQUNwQixZQUFZLEVBQUUsRUFBRTtZQUNoQixvQkFBb0IsRUFBRSxDQUFDO1NBQ3hCO1FBQ0Q7WUFDRSxJQUFJLEVBQUUsNEJBQTRCO1lBQ2xDLFdBQVcsRUFBRSxvQ0FBb0M7WUFDakQsSUFBSSxFQUFFLDJCQUEyQjtZQUNqQyxPQUFPLEVBQUUsTUFBTSxFQUFFLFlBQVk7WUFDN0IsUUFBUSxFQUFFLE1BQU07WUFDaEIsWUFBWSxFQUFFLEVBQUU7WUFDaEIsb0JBQW9CLEVBQUUsQ0FBQztTQUN4QjtRQUNEO1lBQ0UsSUFBSSxFQUFFLDBCQUEwQjtZQUNoQyxXQUFXLEVBQUUsbURBQW1EO1lBQ2hFLElBQUksRUFBRSw4QkFBOEI7WUFDcEMsT0FBTyxFQUFFLE1BQU0sRUFBRSxZQUFZO1lBQzdCLFFBQVEsRUFBRSxVQUFVO1lBQ3BCLFlBQVksRUFBRSxFQUFFO1lBQ2hCLG9CQUFvQixFQUFFLENBQUM7U0FDeEI7UUFDRDtZQUNFLElBQUksRUFBRSxjQUFjO1lBQ3BCLFdBQVcsRUFBRSwwQ0FBMEM7WUFD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