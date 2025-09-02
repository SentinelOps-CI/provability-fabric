/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 *
 * Comprehensive Test Runner for Financial Services MCP
 * Orchestrates all test suites with detailed reporting
 */
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
declare class ComprehensiveTestRunner {
    private testSuites;
    private results;
    private startTime;
    runAllTests(options?: {
        skipStress?: boolean;
        skipSecurity?: boolean;
        parallel?: boolean;
        generateReport?: boolean;
        outputDir?: string;
    }): Promise<ComprehensiveTestReport>;
    private resolveDependencies;
    private runTestsSequentially;
    private runTestsInParallel;
    private groupByDependencyLevel;
    private runSingleTest;
    private parseJestOutput;
    private generateReport;
    private generateRecommendations;
    private printSuiteResult;
    private printSummary;
    private saveReport;
    private generateMarkdownReport;
}
export { ComprehensiveTestRunner, TestResult, ComprehensiveTestReport };
//# sourceMappingURL=run-comprehensive-tests.d.ts.map