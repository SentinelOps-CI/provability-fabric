#!/usr/bin/env python3
"""
Injection Test Runner for Multi-Channel Input Contract

Tests the hardening of trusted vs untrusted channel separation
and ensures proper quoting requirements are enforced.
"""

import json
import hashlib
import requests
import time
from typing import Dict, List, Any
from dataclasses import dataclass
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class InjectionTest:
    test_id: str
    description: str
    input: Dict[str, Any]
    expected_block: bool
    reason: str


class InjectionRunner:
    def __init__(self, kernel_url: str = "http://localhost:8080"):
        self.kernel_url = kernel_url
        self.results = []
        
    def load_corpus(self, corpus_file: str) -> List[InjectionTest]:
        """Load injection test cases from JSONL file"""
        tests = []
        with open(corpus_file, 'r') as f:
            for line_num, line in enumerate(f, 1):
                try:
                    data = json.loads(line.strip())
                    test = InjectionTest(
                        test_id=data['test_id'],
                        description=data['description'],
                        input=data['input'],
                        expected_block=data['expected_block'],
                        reason=data['reason']
                    )
                    tests.append(test)
                except json.JSONDecodeError as e:
                    logger.error(f"Invalid JSON on line {line_num}: {e}")
                except KeyError as e:
                    logger.error(f"Missing required field on line {line_num}: {e}")
        return tests
    
    def create_test_plan(self, test_input: Dict[str, Any]) -> Dict[str, Any]:
        """Create a test plan with the given input channels"""
        # Generate valid hashes for required fields
        system_hash = hashlib.sha256("test system prompt".encode()).hexdigest()
        policy_hash = hashlib.sha256("test policy".encode()).hexdigest()
        
        # Ensure input channels have proper structure
        input_channels = {
            "system": {
                "hash": test_input.get("system", {}).get("hash", system_hash),
                "policy_hash": test_input.get("system", {}).get(
                    "policy_hash", policy_hash)
            },
            "user": test_input.get("user", {
                "content_hash": hashlib.sha256("test user content".encode()).hexdigest(),
                "quoted": True
            }),
            "retrieved": test_input.get("retrieved", []),
            "file": test_input.get("file", [])
        }
        
        # Create a minimal valid plan
        plan = {
            "plan_id": f"test_plan_{int(time.time())}",
            "tenant": "test-tenant",
            "subject": {
                "id": "test-subject",
                "caps": ["read_docs", "send_email"]
            },
            "input_channels": input_channels,
            "steps": [
                {
                    "tool": "test_tool",
                    "args": {"param": "value"},
                    "caps_required": ["read_docs"],
                    "labels_in": ["public"],
                    "labels_out": ["processed"]
                }
            ],
            "constraints": {
                "budget": 1.0,
                "pii": False,
                "dp_epsilon": 0.1,
                "dp_delta": 1e-6,
                "latency_max": 30.0
            },
            "system_prompt_hash": input_channels["system"]["hash"],
            "created_at": int(time.time()),
            "expires_at": int(time.time()) + 3600
        }
        
        return plan
    
    def validate_plan(self, plan: Dict[str, Any]) -> Dict[str, Any]:
        """Send plan to policy kernel for validation"""
        try:
            response = requests.post(
                f"{self.kernel_url}/validate",
                json=plan,
                headers={"Content-Type": "application/json"},
                timeout=10
            )
            
            if response.status_code == 200:
                return {
                    "valid": True,
                    "response": response.json()
                }
            else:
                return {
                    "valid": False,
                    "status_code": response.status_code,
                    "response": response.text
                }
        except requests.RequestException as e:
            return {
                "valid": False,
                "error": str(e)
            }
    
    def run_test(self, test: InjectionTest) -> Dict[str, Any]:
        """Run a single injection test"""
        logger.info(f"Running test: {test.test_id} - {test.description}")
        
        # Create test plan with the injection input
        plan = self.create_test_plan(test.input)
        
        # Validate the plan
        result = self.validate_plan(plan)
        
        # Determine if the test was blocked as expected
        was_blocked = not result.get("valid", True)
        test_passed = (was_blocked == test.expected_block)
        
        test_result = {
            "test_id": test.test_id,
            "description": test.description,
            "expected_block": test.expected_block,
            "was_blocked": was_blocked,
            "test_passed": test_passed,
            "reason": test.reason,
            "kernel_response": result
        }
        
        if test_passed:
            logger.info(f"✓ Test {test.test_id} PASSED")
        else:
            logger.error(f"✗ Test {test.test_id} FAILED")
            logger.error(f"  Expected: {'BLOCKED' if test.expected_block else 'ALLOWED'}")
            logger.error(f"  Actual: {'BLOCKED' if was_blocked else 'ALLOWED'}")
        
        return test_result
    
    def run_corpus(self, corpus_file: str) -> Dict[str, Any]:
        """Run the entire injection corpus"""
        logger.info(f"Loading injection corpus from {corpus_file}")
        tests = self.load_corpus(corpus_file)
        
        logger.info(f"Running {len(tests)} injection tests")
        
        results = []
        passed = 0
        failed = 0
        
        for test in tests:
            result = self.run_test(test)
            results.append(result)
            
            if result["test_passed"]:
                passed += 1
            else:
                failed += 1
        
        # Calculate block rate for adversarial inputs
        adversarial_tests = [r for r in results if r["expected_block"]]
        blocked_count = sum(1 for r in adversarial_tests if r["was_blocked"])
        block_rate = (blocked_count / len(adversarial_tests)) * 100 if adversarial_tests else 0
        
        summary = {
            "total_tests": len(tests),
            "passed": passed,
            "failed": failed,
            "pass_rate": (passed / len(tests)) * 100,
            "adversarial_tests": len(adversarial_tests),
            "blocked_adversarial": blocked_count,
            "block_rate": block_rate,
            "results": results
        }
        
        logger.info("Test Summary:")
        logger.info(f"  Total tests: {summary['total_tests']}")
        logger.info(f"  Passed: {summary['passed']}")
        logger.info(f"  Failed: {summary['failed']}")
        logger.info(f"  Pass rate: {summary['pass_rate']:.1f}%")
        logger.info(f"  Adversarial block rate: {summary['block_rate']:.1f}%")
        
        return summary
    
    def save_results(self, results: Dict[str, Any], output_file: str):
        """Save test results to JSON file"""
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        logger.info(f"Results saved to {output_file}")


def main():
    """Main entry point for injection testing"""
    import argparse
    
    parser = argparse.ArgumentParser(description="Run injection hardening tests")
    parser.add_argument("--corpus", default="tests/redteam/injection_corpus.jsonl",
                       help="Path to injection corpus file")
    parser.add_argument("--kernel-url", default="http://localhost:8080",
                       help="Policy kernel URL")
    parser.add_argument("--output", default="injection_test_results.json",
                       help="Output file for results")
    
    args = parser.parse_args()
    
    runner = InjectionRunner(args.kernel_url)
    
    try:
        results = runner.run_corpus(args.corpus)
        runner.save_results(results, args.output)
        
        # Exit with error code if tests failed
        if results["failed"] > 0:
            logger.error(f"Tests failed: {results['failed']} failures")
            exit(1)
        
        # Check if block rate meets requirements
        if results["block_rate"] < 95.0:
            logger.error(f"Block rate {results['block_rate']:.1f}% below required 95%")
            exit(1)
        
        logger.info("All tests passed! ✓")
        
    except Exception as e:
        logger.error(f"Test execution failed: {e}")
        exit(1)


if __name__ == "__main__":
    main()
