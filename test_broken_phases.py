#!/usr/bin/env python3
"""
Test script to run the broken TRUST-FIRE phases with detailed logging
"""
import subprocess
import sys
import os
import platform
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("test_broken_phases.log", encoding="utf-8"),
    ],
)
logger = logging.getLogger(__name__)


def run_phase2_test():
    """Run Phase 2 (Privacy Burn-Down) test"""
    print("\n" + "=" * 60)
    print("PHASE 2: PRIVACY BURN-DOWN TEST")
    print("=" * 60)

    try:
        # Check if Redis is available
        print("Checking Redis availability...")
        redis_check = subprocess.run(
            ["redis-cli", "ping"], capture_output=True, text=True, timeout=5
        )

        if redis_check.returncode != 0:
            print("❌ Redis is not running or not accessible")
            print("\nSOLUTIONS:")
            print("1. Install Redis for Windows:")
            print(
                "   - Download from: https://github.com/microsoftarchive/redis/releases"
            )
            print("   - Or use Chocolatey: choco install redis-64")
            print("2. Start Redis server:")
            print("   - redis-server")
            print("3. Or use Docker:")
            print("   - docker run -d -p 6379:6379 redis:alpine")
            print("\nAfter starting Redis, run:")
            print("python tests/privacy/privacy_burn_down.py --tenant-id acme-beta")
            return False

        print("✅ Redis is running")

        # Run the privacy burn-down test
        print("\nRunning privacy burn-down test...")
        result = subprocess.run(
            [
                sys.executable,
                "tests/privacy/privacy_burn_down.py",
                "--tenant-id",
                "acme-beta",
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )

        print(f"Return code: {result.returncode}")
        print(f"STDOUT:\n{result.stdout}")
        print(f"STDERR:\n{result.stderr}")

        if result.returncode == 0:
            print("✅ Phase 2 test PASSED")
            return True
        else:
            print("❌ Phase 2 test FAILED")
            return False

    except FileNotFoundError:
        print("❌ Redis CLI not found")
        print("Please install Redis first")
        return False
    except subprocess.TimeoutExpired:
        print("❌ Redis connection timeout")
        print("Redis might not be running")
        return False
    except Exception as e:
        print(f"❌ Error running Phase 2 test: {e}")
        return False


def run_phase3_test():
    """Run Phase 3 (Malicious Adapter) test"""
    print("\n" + "=" * 60)
    print("PHASE 3: MALICIOUS ADAPTER TEST")
    print("=" * 60)

    try:
        print("Running malicious adapter test...")
        result = subprocess.run(
            [
                sys.executable,
                "tests/security/malicious_adapter_test.py",
                "--registry-path",
                "registry",
                "--wasm-sandbox-path",
                "runtime/wasm-sandbox",
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )

        print(f"Return code: {result.returncode}")
        print(f"STDOUT:\n{result.stdout}")
        print(f"STDERR:\n{result.stderr}")

        if result.returncode == 0:
            print("✅ Phase 3 test PASSED")
            return True
        else:
            print("❌ Phase 3 test FAILED")

            # Provide specific solutions based on error patterns
            if "The system cannot find the path specified" in result.stderr:
                print("\nSOLUTION: Build script execution issue")
                print("The Windows batch file execution has been fixed with:")
                print("- Absolute path usage")
                print("- Explicit cmd.exe execution")
                print("- UTF-8 encoding handling")
                print("- Better error handling")

            if "UnicodeEncodeError" in result.stderr:
                print("\nSOLUTION: Unicode encoding issue")
                print("The emoji characters have been removed and UTF-8 encoding added")

            return False

    except Exception as e:
        print(f"❌ Error running Phase 3 test: {e}")
        return False


def check_log_files():
    """Check for log files and their contents"""
    print("\n" + "=" * 60)
    print("LOG FILE ANALYSIS")
    print("=" * 60)

    log_files = [
        "privacy_burn_down.log",
        "malicious_adapter_test.log",
        "test_broken_phases.log",
    ]

    for log_file in log_files:
        if os.path.exists(log_file):
            print(f"\n📄 {log_file}:")
            try:
                with open(log_file, "r", encoding="utf-8") as f:
                    content = f.read()
                    lines = content.split("\n")
                    print(f"   Lines: {len(lines)}")
                    print(f"   Last 5 lines:")
                    for line in lines[-5:]:
                        if line.strip():
                            print(f"   {line}")
            except Exception as e:
                print(f"   Error reading log file: {e}")
        else:
            print(f"\n❌ {log_file}: Not found")


def main():
    print("🔍 TRUST-FIRE BROKEN PHASES DIAGNOSTIC")
    print("=" * 60)

    # Check if we're on Windows
    is_windows = platform.system() == "Windows"
    print(f"Platform: {platform.system()} {platform.release()}")
    print(f"Python: {sys.version}")

    if is_windows:
        print("\n⚠️  WINDOWS-SPECIFIC NOTES:")
        print("- Redis may need to be installed separately")
        print("- Build scripts now use .bat files")
        print("- Unicode encoding issues have been fixed")
        print("- Emoji characters removed for Windows compatibility")

    phase2_success = run_phase2_test()
    phase3_success = run_phase3_test()
    check_log_files()

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Phase 2 (Privacy Burn-Down): {'✅ PASS' if phase2_success else '❌ FAIL'}")
    print(f"Phase 3 (Malicious Adapter): {'✅ PASS' if phase3_success else '❌ FAIL'}")

    if phase2_success and phase3_success:
        print("\n🎉 All phases are now working!")
        print("\nNext steps:")
        print("1. Run the complete TRUST-FIRE suite:")
        print("   python tests/trust_fire_orchestrator.py")
        print("2. Or run individual phases:")
        print("   python tests/privacy/privacy_burn_down.py --tenant-id acme-beta")
        print("   python tests/security/malicious_adapter_test.py")
    else:
        print("\n🔧 Some phases still need attention.")
        print("\nTROUBLESHOOTING:")
        if not phase2_success:
            print("- Phase 2: Ensure Redis is running (see solutions above)")
        if not phase3_success:
            print("- Phase 3: Check the build script execution (should be fixed)")
        print("\nCheck the log files for detailed error information.")

    return phase2_success and phase3_success


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
