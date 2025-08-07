#!/usr/bin/env python3
"""
Test broker enforcement - verifies that tool broker refuses unapproved steps
"""

import asyncio
from typing import Dict, Any


class BrokerEnforcementTest:
    def __init__(self):
        self.kernel_url = "http://localhost:8080"
        self.broker_url = "http://localhost:8081"

    async def setup_kernel(self):
        """Start the policy kernel"""
        # This would start the kernel service
        # For now, we'll simulate the kernel responses
        pass

    async def setup_broker(self):
        """Start the tool broker"""
        # This would start the broker service
        # For now, we'll simulate the broker behavior
        pass

    def create_test_plan(self) -> Dict[str, Any]:
        """Create a test plan with approved and unapproved steps"""
        return {
            "plan_id": "test-plan-enforcement",
            "tenant": "tenant-1",
            "subject": {"id": "user-1", "caps": ["read_docs", "send_email"]},
            "steps": [
                {
                    "tool": "retrieval",
                    "args": {"query": "test"},
                    "caps_required": ["read_docs"],
                    "labels_in": [],
                    "labels_out": ["docs"],
                },
                {
                    "tool": "email",
                    "args": {"to": "test@example.com"},
                    "caps_required": ["send_email"],
                    "labels_in": ["docs"],
                    "labels_out": [],
                },
            ],
            "constraints": {"budget": 10.0, "pii": False, "dp_epsilon": 1.0},
            "system_prompt_hash": "a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6",
        }

    def create_kernel_decision(self, plan: Dict[str, Any]) -> Dict[str, Any]:
        """Simulate kernel decision"""
        return {
            "approved_steps": [
                {
                    "step_index": 0,
                    "tool": "retrieval",
                    "args": {"query": "test"},
                    "receipts": [],
                },
                {
                    "step_index": 1,
                    "tool": "email",
                    "args": {"to": "test@example.com"},
                    "receipts": [],
                },
            ],
            "reason": "Plan approved for execution",
            "valid": True,
            "errors": None,
            "warnings": None,
        }

    async def test_approved_tool_execution(self):
        """Test that approved tools execute successfully"""
        print("Testing approved tool execution...")

        plan = self.create_test_plan()
        decision = self.create_kernel_decision(plan)

        # Simulate broker receiving approved steps
        broker = MockToolBroker()
        broker.set_approved_steps("test-plan-enforcement", decision["approved_steps"])

        # Try to execute an approved tool
        tool_call = {
            "tool": "retrieval",
            "args": {"query": "test"},
            "step_index": 0,
            "plan_id": "test-plan-enforcement",
        }

        result = await broker.execute_tool(tool_call)

        assert result["success"], f"Approved tool should succeed, got: {result}"
        assert (
            result["error"] is None
        ), f"Approved tool should not have error, got: {result['error']}"

        print("✓ Approved tool execution test passed")

    async def test_unapproved_tool_rejection(self):
        """Test that unapproved tools are rejected"""
        print("Testing unapproved tool rejection...")

        plan = self.create_test_plan()
        decision = self.create_kernel_decision(plan)

        # Simulate broker receiving approved steps
        broker = MockToolBroker()
        broker.set_approved_steps("test-plan-enforcement", decision["approved_steps"])

        # Try to execute an unapproved tool
        tool_call = {
            "tool": "unauthorized_tool",
            "args": {"malicious": "payload"},
            "step_index": 2,
            "plan_id": "test-plan-enforcement",
        }

        result = await broker.execute_tool(tool_call)

        assert result["success"] == False, f"Unapproved tool should fail, got: {result}"
        assert (
            result["error"] is not None
        ), f"Unapproved tool should have error, got: {result}"
        assert (
            "not in approved steps" in result["error"]
        ), f"Error should mention unapproved tool, got: {result['error']}"

        # Check that violation was logged
        violations = broker.get_violations()
        assert len(violations) > 0, "Violation should be logged"
        assert (
            violations[0]["violation_type"] == "UNAPPROVED_TOOL"
        ), f"Wrong violation type: {violations[0]}"

        print("✓ Unapproved tool rejection test passed")

    async def test_no_plan_approval_rejection(self):
        """Test that tools without plan approval are rejected"""
        print("Testing no plan approval rejection...")

        broker = MockToolBroker()

        # Try to execute a tool without any plan approval
        tool_call = {
            "tool": "any_tool",
            "args": {"test": "data"},
            "step_index": 0,
            "plan_id": "nonexistent-plan",
        }

        result = await broker.execute_tool(tool_call)

        assert (
            result["success"] == False
        ), f"Tool without plan should fail, got: {result}"
        assert (
            result["error"] is not None
        ), f"Tool without plan should have error, got: {result}"
        assert (
            "No approved plan found" in result["error"]
        ), f"Error should mention no plan, got: {result['error']}"

        # Check that violation was logged
        violations = broker.get_violations()
        assert len(violations) > 0, "Violation should be logged"
        assert (
            violations[0]["violation_type"] == "NO_PLAN_APPROVAL"
        ), f"Wrong violation type: {violations[0]}"

        print("✓ No plan approval rejection test passed")

    async def test_enforcement_mode_toggle(self):
        """Test that enforcement mode can be toggled"""
        print("Testing enforcement mode toggle...")

        broker = MockToolBroker()

        # Test non-enforcement mode
        broker.set_enforcement_mode(False)

        tool_call = {
            "tool": "unauthorized_tool",
            "args": {"test": "data"},
            "step_index": 0,
            "plan_id": "test-plan",
        }

        result = await broker.execute_tool(tool_call)
        assert (
            result["success"] == True
        ), f"Non-enforcement mode should allow all tools, got: {result}"
        assert (
            result["result"]["mode"] == "non_enforcement"
        ), f"Should be in non-enforcement mode, got: {result}"

        # Test enforcement mode
        broker.set_enforcement_mode(True)

        result = await broker.execute_tool(tool_call)
        assert (
            result["success"] == False
        ), f"Enforcement mode should block unapproved tools, got: {result}"

        print("✓ Enforcement mode toggle test passed")

    async def run_all_tests(self):
        """Run all broker enforcement tests"""
        print("Running broker enforcement tests...")

        await self.test_approved_tool_execution()
        await self.test_unapproved_tool_rejection()
        await self.test_no_plan_approval_rejection()
        await self.test_enforcement_mode_toggle()

        print("All broker enforcement tests passed! ✓")


class MockToolBroker:
    """Mock tool broker for testing"""

    def __init__(self):
        self.approved_steps = {}
        self.violations = []
        self.enforcement_mode = True

    def set_approved_steps(self, plan_id: str, steps: list):
        """Set approved steps for a plan"""
        self.approved_steps[plan_id] = steps

    def set_enforcement_mode(self, mode: bool):
        """Set enforcement mode"""
        self.enforcement_mode = mode

    async def execute_tool(self, tool_call: dict) -> dict:
        """Execute a tool call"""
        import uuid
        import datetime

        execution_id = str(uuid.uuid4())
        timestamp = datetime.datetime.utcnow().isoformat()

        if not self.enforcement_mode:
            return {
                "success": True,
                "result": {
                    "type": "tool_result",
                    "tool": tool_call["tool"],
                    "execution_id": execution_id,
                    "mode": "non_enforcement",
                },
                "error": None,
                "execution_id": execution_id,
                "timestamp": timestamp,
            }

        # Check if plan is approved
        plan_id = tool_call["plan_id"]
        if plan_id not in self.approved_steps:
            violation = {
                "violation_type": "NO_PLAN_APPROVAL",
                "reason": "No approved plan found",
                "tool_call": tool_call,
                "timestamp": timestamp,
            }
            self.violations.append(violation)

            return {
                "success": False,
                "result": None,
                "error": "No approved plan found",
                "execution_id": execution_id,
                "timestamp": timestamp,
            }

        # Check if tool is approved
        steps = self.approved_steps[plan_id]
        approved_step = None

        for step in steps:
            if step["tool"] == tool_call["tool"] and step[
                "step_index"
            ] == tool_call.get("step_index", 0):
                approved_step = step
                break

        if approved_step is None:
            violation = {
                "violation_type": "UNAPPROVED_TOOL",
                "reason": f"Tool '{tool_call['tool']}' not in approved steps",
                "tool_call": tool_call,
                "timestamp": timestamp,
            }
            self.violations.append(violation)

            return {
                "success": False,
                "result": None,
                "error": f"Tool '{tool_call['tool']}' not in approved steps",
                "execution_id": execution_id,
                "timestamp": timestamp,
            }

        # Execute approved tool
        return {
            "success": True,
            "result": {
                "type": "tool_result",
                "tool": approved_step["tool"],
                "execution_id": execution_id,
                "mode": "enforcement",
            },
            "error": None,
            "execution_id": execution_id,
            "timestamp": timestamp,
        }

    def get_violations(self) -> list:
        """Get all violations"""
        return self.violations


async def main():
    """Main test runner"""
    test = BrokerEnforcementTest()
    await test.run_all_tests()


if __name__ == "__main__":
    asyncio.run(main())
