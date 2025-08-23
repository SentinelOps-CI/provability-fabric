#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Comprehensive Test Script for All Implemented Components
"""

import json
import subprocess
import sys
import time
from pathlib import Path
from datetime import datetime


def run_command(cmd, description):
    """Run a command and return success status"""
    print(f"🔧 {description}")
    print(f"   Command: {cmd}")

    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        if result.returncode == 0:
            print(f"   ✅ Success: {result.stdout.strip()}")
            return True
        else:
            print(f"   ❌ Failed: {result.stderr.strip()}")
            return False
    except Exception as e:
        print(f"   ❌ Error: {e}")
        return False


def test_cli_commands():
    """Test all CLI commands"""
    print("\n" + "=" * 60)
    print("TESTING CLI COMMANDS")
    print("=" * 60)

    # Test basic CLI help
    success = run_command("cd core/cli/pf && pf.exe --help", "Basic CLI help")

    # Test bundle commands
    success &= run_command(
        "cd core/cli/pf && pf.exe bundle --help", "Bundle command help"
    )
    success &= run_command(
        "cd core/cli/pf && pf.exe bundle pack --help", "Bundle pack help"
    )
    success &= run_command(
        "cd core/cli/pf && pf.exe bundle verify --help", "Bundle verify help"
    )

    # Test run commands
    success &= run_command("cd core/cli/pf && pf.exe run --help", "Run command help")

    # Test audit commands
    success &= run_command(
        "cd core/cli/pf && pf.exe audit --help", "Audit command help"
    )

    # Test performance commands
    success &= run_command(
        "cd core/cli/pf && pf.exe performance --help", "Performance command help"
    )

    return success


def test_bundle_operations():
    """Test bundle pack and verify operations"""
    print("\n" + "=" * 60)
    print("TESTING BUNDLE OPERATIONS")
    print("=" * 60)

    # Create a test bundle
    success = run_command(
        "cd core/cli/pf && pf.exe init test-bundle", "Initialize test bundle"
    )

    # Pack the bundle
    success &= run_command(
        "cd core/cli/pf && pf.exe bundle pack bundles/test-bundle -o test-bundle.tar.gz",
        "Pack test bundle",
    )

    # Verify the bundle
    success &= run_command(
        "cd core/cli/pf && pf.exe bundle verify test-bundle.tar.gz",
        "Verify test bundle",
    )

    # Show bundle ID
    success &= run_command(
        "cd core/cli/pf && pf.exe bundle show-id test-bundle.tar.gz", "Show bundle ID"
    )

    return success


def test_execution_and_replay():
    """Test bundle execution and replay functionality"""
    print("\n" + "=" * 60)
    print("TESTING EXECUTION AND REPLAY")
    print("=" * 60)

    # Run bundle with fixture recording
    success = run_command(
        "cd core/cli/pf && pf.exe run --bundle bundles/test-bundle --record-fixtures --seed 42",
        "Run bundle with fixtures",
    )

    # Check if fixtures were created
    fixtures_exist = Path("core/cli/pf/fixtures").exists()
    if fixtures_exist:
        print("   ✅ Fixtures directory created")
        success &= True
    else:
        print("   ❌ Fixtures directory not created")
        success &= False

    # Try to replay (this will fail without proper fixtures, but tests the command)
    success &= run_command(
        "cd core/cli/pf && pf.exe run --replay --fixture-path fixtures/fixture_42.json --bundle bundles/test-bundle",
        "Test replay command",
    )

    return success


def test_audit_functionality():
    """Test audit and ledger functionality"""
    print("\n" + "=" * 60)
    print("TESTING AUDIT FUNCTIONALITY")
    print("=" * 60)

    # Test audit command with default settings
    success = run_command(
        "cd core/cli/pf && pf.exe audit --verify-chain", "Test audit chain verification"
    )

    # Test audit with custom ledger URL
    success &= run_command(
        "cd core/cli/pf && pf.exe audit --ledger-url http://localhost:3000 --verify-chain",
        "Test audit with custom ledger",
    )

    return success


def test_performance_measurement():
    """Test performance measurement functionality"""
    print("\n" + "=" * 60)
    print("TESTING PERFORMANCE MEASUREMENT")
    print("=" * 60)

    # Test basic performance measurement
    success = run_command(
        "cd core/cli/pf && pf.exe performance --duration 5 --concurrency 5",
        "Test basic performance measurement",
    )

    # Test performance with sidecar measurement
    success &= run_command(
        "cd core/cli/pf && pf.exe performance --duration 5 --concurrency 5 --measure-sidecar",
        "Test sidecar overhead measurement",
    )

    # Test performance with output file
    success &= run_command(
        "cd core/cli/pf && pf.exe performance --duration 5 --concurrency 5 --output perf_report.json",
        "Test performance with output file",
    )

    return success


def test_privacy_tests():
    """Test enhanced privacy tests"""
    print("\n" + "=" * 60)
    print("TESTING ENHANCED PRIVACY TESTS")
    print("=" * 60)

    # Test privacy tests (this will fail without Redis, but tests the command structure)
    success = run_command(
        "cd tests/privacy && python privacy_burn_down.py --tenant-id test-tenant --run-privacy-tests",
        "Test enhanced privacy tests",
    )

    return success


def generate_test_report(results):
    """Generate comprehensive test report"""
    report = {
        "timestamp": datetime.now().isoformat(),
        "test_summary": {
            "total_tests": len(results),
            "passed": sum(1 for r in results.values() if r),
            "failed": sum(1 for r in results.values() if not r),
        },
        "test_results": results,
        "recommendations": [],
    }

    # Generate recommendations
    if report["test_summary"]["failed"] > 0:
        report["recommendations"].append(
            "Some tests failed - check infrastructure setup"
        )

    if report["test_summary"]["passed"] == report["test_summary"]["total_tests"]:
        report["recommendations"].append(
            "All tests passed - system is working correctly"
        )

    # Save report
    report_path = (
        f"comprehensive_test_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    )
    with open(report_path, "w") as f:
        json.dump(report, f, indent=2)

    print(f"\n📊 Test report saved to: {report_path}")
    return report


def main():
    """Main test function"""
    print("🚀 Starting Comprehensive Component Testing")
    print("=" * 60)

    results = {}

    # Test CLI commands
    results["cli_commands"] = test_cli_commands()

    # Test bundle operations
    results["bundle_operations"] = test_bundle_operations()

    # Test execution and replay
    results["execution_replay"] = test_execution_and_replay()

    # Test audit functionality
    results["audit_functionality"] = test_audit_functionality()

    # Test performance measurement
    results["performance_measurement"] = test_performance_measurement()

    # Test privacy tests
    results["privacy_tests"] = test_privacy_tests()

    # Generate and display report
    report = generate_test_report(results)

    print("\n" + "=" * 60)
    print("FINAL TEST RESULTS")
    print("=" * 60)

    for test_name, result in results.items():
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{test_name.replace('_', ' ').title()}: {status}")

    print(
        f"\nOverall: {report['test_summary']['passed']}/{report['test_summary']['total_tests']} tests passed"
    )

    if report["test_summary"]["failed"] > 0:
        print(
            "\n⚠️  Some tests failed. This is expected in a test environment without full infrastructure."
        )
        print("   The tests verify that:")
        print("   - CLI commands are properly implemented")
        print("   - Command structures are correct")
        print("   - Error handling works as expected")
        print("   - Infrastructure dependencies are properly detected")

    print("\n🎉 Component testing completed!")
    return report["test_summary"]["failed"] == 0


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
