#!/usr/bin/env python3
"""
Simple PII Leak Test for Non-Interference Verification

This script demonstrates non-interference testing by checking that:
1. High-security PII data doesn't leak into public outputs
2. Public processing remains consistent regardless of private inputs
3. Declassification policies are respected

SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors
"""

import json
import hashlib
import time
import sys
import re
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass


@dataclass
class PIITestCase:
    """Represents a PII test case."""
    name: str
    public_input: str
    private_data: str
    expected_outcome: str  # 'blocked', 'sanitized', 'allowed'
    

@dataclass
class PIITestResult:
    """Result of a PII leak test."""
    test_case: PIITestCase
    actual_output: str
    pii_detected: bool
    pii_leaked: bool
    sanitized_properly: bool
    status: str  # 'pass', 'fail', 'warning'
    

class SimplePIITester:
    """Simple PII leak tester for non-interference verification."""
    
    def __init__(self):
        # Common PII patterns for detection
        self.pii_patterns = {
            'email': r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b',
            'ssn': r'\b\d{3}-\d{2}-\d{4}\b',
            'phone': r'\b(\+?1[-.\s]?)?\(?\d{3}\)?[-.\s]?\d{3}[-.\s]?\d{4}\b',
            'credit_card': r'\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b',
            'address': r'\b\d+\s+[A-Za-z0-9\s,]+\s+(St|Ave|Blvd|Rd|Dr|Ct)\b'
        }
        
        # Test PII data
        self.test_pii_data = {
            'emails': ['john.doe@example.com', 'alice.smith@company.org', 'test.user@domain.net'],
            'ssns': ['123-45-6789', '987-65-4321', '111-22-3333'],  
            'phones': ['555-123-4567', '1-800-555-0199', '+1 (555) 987-6543'],
            'credit_cards': ['4111-1111-1111-1111', '5555-5555-5555-4444'],
            'addresses': ['123 Main St, Anytown, NY', '456 Oak Ave, Springfield']
        }
        
        self.results = []
        
    def detect_pii(self, text: str) -> Dict[str, List[str]]:
        """Detect PII in text using regex patterns."""
        detected = {}
        for pii_type, pattern in self.pii_patterns.items():
            matches = re.findall(pattern, text, re.IGNORECASE)
            if matches:
                detected[pii_type] = matches
        return detected
        
    def simulate_secure_processing(self, public_input: str, private_data: str, 
                                  declassify_policy: str = "none") -> str:
        """Simulate secure processing that should prevent PII leakage."""
        
        # Hash private data (simulating secure processing)
        private_hash = hashlib.sha256(private_data.encode()).hexdigest()[:8]
        
        # Process public input 
        if "transaction" in public_input.lower():
            # Transaction processing
            tx_id = f"tx_{hashlib.md5(public_input.encode()).hexdigest()[:8]}"
            
            # Apply declassification policy
            if declassify_policy == "tx_id_only":
                return f"Transaction {tx_id} processed successfully"
            elif declassify_policy == "none":
                return f"Transaction processed successfully"
            else:
                return f"Transaction processed successfully"
                
        elif "process" in public_input.lower():
            # Generic processing
            return f"Request processed successfully at {int(time.time())}"
            
        else:
            # Default processing
            return "Request completed"
    
    def run_pii_test_case(self, test_case: PIITestCase) -> PIITestResult:
        """Run a single PII test case."""
        
        # Simulate processing
        output = self.simulate_secure_processing(
            test_case.public_input,
            test_case.private_data
        )
        
        # Check for PII leakage
        detected_pii = self.detect_pii(output)
        pii_detected = len(detected_pii) > 0
        
        # Check if original private data leaked
        pii_leaked = test_case.private_data.lower() in output.lower()
        
        # Determine if sanitization was proper
        sanitized_properly = not pii_leaked and not pii_detected
        
        # Determine test status
        if test_case.expected_outcome == "blocked" and sanitized_properly:
            status = "pass"
        elif test_case.expected_outcome == "sanitized" and sanitized_properly:
            status = "pass"  
        elif test_case.expected_outcome == "allowed" and not pii_leaked:
            status = "pass"
        else:
            status = "fail" if pii_leaked else "warning"
            
        return PIITestResult(
            test_case=test_case,
            actual_output=output,
            pii_detected=pii_detected,
            pii_leaked=pii_leaked,
            sanitized_properly=sanitized_properly,
            status=status
        )
    
    def test_non_interference(self) -> Dict:
        """Test non-interference property with different private inputs."""
        print("🔐 Testing non-interference with PII data...")
        
        # Same public input, different private data
        public_input = "process transaction request"
        private_variations = [
            "john.doe@example.com",
            "123-45-6789", 
            "555-123-4567"
        ]
        
        outputs = []
        for private_data in private_variations:
            output = self.simulate_secure_processing(public_input, private_data)
            outputs.append(output)
            
        # Check if all outputs are equivalent (non-interference)
        unique_outputs = set(outputs)
        non_interference_maintained = len(unique_outputs) == 1
        
        result = {
            "test_name": "non_interference",
            "public_input": public_input,
            "private_variations": len(private_variations),
            "outputs": outputs,
            "unique_outputs": len(unique_outputs),
            "non_interference_maintained": non_interference_maintained,
            "status": "passed" if non_interference_maintained else "failed"
        }
        
        if non_interference_maintained:
            print(f"✅ Non-interference maintained across {len(private_variations)} private variations")
        else:
            print(f"❌ Non-interference violated - {len(unique_outputs)} different outputs detected")
            
        return result
    
    def run_pii_leakage_tests(self) -> List[PIITestResult]:
        """Run a set of PII leakage tests."""
        print("🔍 Running PII leakage tests...")
        
        # Define test cases
        test_cases = [
            PIITestCase(
                name="email_direct",
                public_input="process user registration",
                private_data="john.doe@example.com",
                expected_outcome="blocked"
            ),
            PIITestCase(
                name="ssn_direct", 
                public_input="verify identity",
                private_data="123-45-6789",
                expected_outcome="blocked"
            ),
            PIITestCase(
                name="phone_direct",
                public_input="update contact info", 
                private_data="555-123-4567",
                expected_outcome="blocked"
            ),
            PIITestCase(
                name="transaction_processing",
                public_input="process payment transaction",
                private_data="4111-1111-1111-1111", 
                expected_outcome="sanitized"
            ),
            PIITestCase(
                name="safe_processing",
                public_input="process general request",
                private_data="internal_reference_123",
                expected_outcome="allowed"
            )
        ]
        
        results = []
        for test_case in test_cases:
            result = self.run_pii_test_case(test_case)
            results.append(result)
            
            status_emoji = {"pass": "✅", "fail": "❌", "warning": "⚠️"}.get(result.status, "❓")
            print(f"  {status_emoji} {test_case.name}: {result.status.upper()}")
            if result.pii_leaked:
                print(f"    ❌ PII leaked: {test_case.private_data[:20]}...")
            elif result.pii_detected:
                print(f"    ⚠️  PII patterns detected in output")
                
        return results
    
    def run_all_tests(self) -> Dict:
        """Run all PII and non-interference tests."""
        print("🚀 Starting PII Leak Tests for Non-Interference Verification\n")
        
        start_time = time.time()
        
        # Run PII leakage tests
        pii_results = self.run_pii_leakage_tests()
        print()
        
        # Run non-interference test
        ni_result = self.test_non_interference()
        print()
        
        # Compile results
        passed = sum(1 for r in pii_results if r.status == "pass")
        failed = sum(1 for r in pii_results if r.status == "fail") 
        warnings = sum(1 for r in pii_results if r.status == "warning")
        
        critical_leaks = sum(1 for r in pii_results if r.pii_leaked)
        detection_bypasses = sum(1 for r in pii_results if r.status != "pass")
        
        end_time = time.time()
        
        summary = {
            "timestamp": start_time,
            "execution_time": end_time - start_time,
            "total_tests": len(pii_results),
            "passed": passed,
            "failed": failed, 
            "warnings": warnings,
            "critical_leaks": critical_leaks,
            "detection_bypasses": detection_bypasses,
            "non_interference": ni_result,
            "pii_test_results": [
                {
                    "name": r.test_case.name,
                    "status": r.status,
                    "pii_leaked": r.pii_leaked,
                    "pii_detected": r.pii_detected,
                    "output": r.actual_output
                } for r in pii_results
            ]
        }
        
        # Print summary
        print("=" * 60)
        print("PII LEAK TEST RESULTS")
        print("=" * 60)
        print(f"📊 Total Tests: {summary['total_tests']}")
        print(f"🚨 Critical Leaks: {critical_leaks}")
        print(f"⚠️  Detection Bypasses: {detection_bypasses}")
        print(f"✅ Successful Blocks: {passed}")
        print(f"📈 Non-Interference: {'✅ PASSED' if ni_result['status'] == 'passed' else '❌ FAILED'}")
        print(f"⚡ Execution Time: {summary['execution_time']:.2f}s")
        
        if critical_leaks == 0 and ni_result['status'] == 'passed':
            print("\n🎯 RESULT: Non-interference verification PASSED")
        else:
            print(f"\n⚠️  WARNING: {critical_leaks} critical leaks detected!")
            
        return summary


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Simple PII Leak Test for Non-Interference")
    parser.add_argument("--output", help="Output JSON file for results")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    
    args = parser.parse_args()
    
    # Run tests
    tester = SimplePIITester()
    results = tester.run_all_tests()
    
    # Save results
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n📄 Results saved to: {args.output}")
    
    # Exit with appropriate code
    if results['critical_leaks'] > 0 or results['non_interference']['status'] != 'passed':
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()