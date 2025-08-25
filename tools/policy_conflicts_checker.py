#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

"""
Policy Conflicts Checker

This tool analyzes policy specifications to detect and resolve conflicts
between different policy rules, ensuring consistency and preventing
contradictory enforcement.
"""

import json
import yaml
import argparse
import sys
from pathlib import Path
from typing import Dict, List, Set, Optional
from dataclasses import dataclass
from enum import Enum


class ConflictType(Enum):
    """Types of policy conflicts"""

    CONTRADICTORY_RULES = "contradictory_rules"
    OVERLAPPING_SCOPE = "overlapping_scope"
    INHERITANCE_CONFLICT = "inheritance_conflict"
    RESOURCE_CONFLICT = "resource_conflict"
    TIMING_CONFLICT = "timing_conflict"


@dataclass
class PolicyConflict:
    """Represents a detected policy conflict"""

    conflict_type: ConflictType
    severity: str  # "low", "medium", "high", "critical"
    description: str
    affected_policies: List[str]
    affected_resources: List[str]
    resolution_suggestions: List[str]
    line_numbers: Optional[List[int]] = None


class PolicyAnalyzer:
    """Analyzes policies for conflicts and inconsistencies"""

    def __init__(self):
        self.policies = {}
        self.conflicts = []
        self.resource_mappings = {}

    def load_policy_file(self, file_path: Path) -> bool:
        """Load a policy file (YAML or JSON)"""
        try:
            if file_path.suffix.lower() in [".yaml", ".yml"]:
                with open(file_path, "r", encoding="utf-8") as f:
                    policy_data = yaml.safe_load(f)
            elif file_path.suffix.lower() == ".json":
                with open(file_path, "r", encoding="utf-8") as f:
                    policy_data = json.load(f)
            else:
                print(f"Unsupported file type: {file_path.suffix}")
                return False

            policy_id = policy_data.get("id", str(file_path))
            self.policies[policy_id] = {
                "file_path": file_path,
                "data": policy_data,
                "resources": self._extract_resources(policy_data),
                "rules": self._extract_rules(policy_data),
            }

            print(f"✅ Loaded policy: {policy_id}")
            return True

        except Exception as e:
            print(f"❌ Failed to load {file_path}: {e}")
            return False

    def _extract_resources(self, policy_data: Dict) -> Set[str]:
        """Extract resource identifiers from policy data"""
        resources = set()

        # Extract from various policy sections
        if "resources" in policy_data:
            resources.update(policy_data["resources"])

        if "scope" in policy_data:
            scope = policy_data["scope"]
            if isinstance(scope, dict):
                resources.update(scope.get("resources", []))
            elif isinstance(scope, list):
                resources.extend(scope)

        # Extract from rules
        if "rules" in policy_data:
            for rule in policy_data["rules"]:
                if isinstance(rule, dict):
                    resources.update(rule.get("resources", []))
                    resources.update(rule.get("targets", []))

        return resources

    def _extract_rules(self, policy_data: Dict) -> List[Dict]:
        """Extract rules from policy data"""
        rules = []

        if "rules" in policy_data:
            rules.extend(policy_data["rules"])

        if "permissions" in policy_data:
            for perm in policy_data["permissions"]:
                if isinstance(perm, dict):
                    rules.append(
                        {
                            "type": "permission",
                            "action": perm.get("action", "allow"),
                            "resource": perm.get("resource", ""),
                            "conditions": perm.get("conditions", {}),
                        }
                    )

        return rules

    def detect_conflicts(self) -> List[PolicyConflict]:
        """Detect all policy conflicts"""
        self.conflicts = []

        # Check for contradictory rules
        self._check_contradictory_rules()

        # Check for overlapping scope conflicts
        self._check_overlapping_scope()

        # Check for inheritance conflicts
        self._check_inheritance_conflicts()

        # Check for resource conflicts
        self._check_resource_conflicts()

        # Check for timing conflicts
        self._check_timing_conflicts()

        return self.conflicts

    def _check_contradictory_rules(self):
        """Check for rules that contradict each other"""
        policy_ids = list(self.policies.keys())

        for i, policy_a_id in enumerate(policy_ids):
            for policy_b_id in policy_ids[i + 1 :]:
                policy_a = self.policies[policy_a_id]
                policy_b = self.policies[policy_b_id]

                # Check for direct contradictions
                for rule_a in policy_a["rules"]:
                    for rule_b in policy_b["rules"]:
                        if self._rules_contradict(rule_a, rule_b):
                            conflict = PolicyConflict(
                                conflict_type=ConflictType.CONTRADICTORY_RULES,
                                severity="high",
                                description=f"Rule in {policy_a_id} contradicts rule in {policy_b_id}",
                                affected_policies=[policy_a_id, policy_b_id],
                                affected_resources=list(
                                    set(rule_a.get("resources", []))
                                    | set(rule_b.get("resources", []))
                                ),
                                resolution_suggestions=[
                                    "Review and reconcile conflicting rules",
                                    "Use priority levels to resolve conflicts",
                                    "Refactor policies to avoid contradictions",
                                ],
                            )
                            self.conflicts.append(conflict)

    def _rules_contradict(self, rule_a: Dict, rule_b: Dict) -> bool:
        """Check if two rules contradict each other"""
        # Check if rules apply to the same resources
        resources_a = set(rule_a.get("resources", []))
        resources_b = set(rule_b.get("resources", []))

        if not resources_a.intersection(resources_b):
            return False  # No resource overlap

        # Check for opposite actions
        action_a = rule_a.get("action", "allow")
        action_b = rule_b.get("action", "allow")

        if action_a != action_b:
            return True

        # Check for conflicting conditions
        conditions_a = rule_a.get("conditions", {})
        conditions_b = rule_b.get("conditions", {})

        return self._conditions_conflict(conditions_a, conditions_b)

    def _conditions_conflict(self, cond_a: Dict, cond_b: Dict) -> bool:
        """Check if conditions conflict"""
        for key in set(cond_a.keys()) & set(cond_b.keys()):
            if cond_a[key] != cond_b[key]:
                return True
        return False

    def _check_overlapping_scope(self):
        """Check for overlapping scope conflicts"""
        policy_ids = list(self.policies.keys())

        for i, policy_a_id in enumerate(policy_ids):
            for policy_b_id in policy_ids[i + 1 :]:
                policy_a = self.policies[policy_a_id]
                policy_b = self.policies[policy_b_id]

                # Check for resource scope overlap
                resources_a = policy_a["resources"]
                resources_b = policy_b["resources"]

                overlap = resources_a.intersection(resources_b)
                if overlap:
                    # Check if overlap causes conflicts
                    if self._overlap_causes_conflict(policy_a, policy_b, overlap):
                        conflict = PolicyConflict(
                            conflict_type=ConflictType.OVERLAPPING_SCOPE,
                            severity="medium",
                            description=f"Overlapping scope between {policy_a_id} and {policy_b_id}",
                            affected_policies=[policy_a_id, policy_b_id],
                            affected_resources=list(overlap),
                            resolution_suggestions=[
                                "Define clear scope boundaries",
                                "Use hierarchical policy structure",
                                "Implement scope precedence rules",
                            ],
                        )
                        self.conflicts.append(conflict)

    def _overlap_causes_conflict(
        self, policy_a: Dict, policy_b: Dict, overlap: Set[str]
    ) -> bool:
        """Check if resource overlap causes conflicts"""
        # Check if overlapping resources have different access patterns
        rules_a = policy_a["rules"]
        rules_b = policy_b["rules"]

        for resource in overlap:
            access_a = self._get_resource_access(rules_a, resource)
            access_b = self._get_resource_access(rules_b, resource)

            if access_a != access_b:
                return True

        return False

    def _get_resource_access(self, rules: List[Dict], resource: str) -> str:
        """Get access level for a specific resource"""
        for rule in rules:
            if resource in rule.get("resources", []):
                return rule.get("action", "allow")
        return "deny"

    def _check_inheritance_conflicts(self):
        """Check for inheritance-related conflicts"""
        for policy_id, policy in self.policies.items():
            if "inherits" in policy["data"]:
                parent_policies = policy["data"]["inherits"]

                for parent_id in parent_policies:
                    if parent_id in self.policies:
                        parent_policy = self.policies[parent_id]

                        # Check for inheritance conflicts
                        if self._has_inheritance_conflict(policy, parent_policy):
                            conflict = PolicyConflict(
                                conflict_type=ConflictType.INHERITANCE_CONFLICT,
                                severity="medium",
                                description=f"Inheritance conflict in {policy_id} from {parent_id}",
                                affected_policies=[policy_id, parent_id],
                                affected_resources=list(
                                    policy["resources"] | parent_policy["resources"]
                                ),
                                resolution_suggestions=[
                                    "Review inheritance hierarchy",
                                    "Override conflicting inherited rules",
                                    "Use composition instead of inheritance",
                                ],
                            )
                            self.conflicts.append(conflict)

    def _has_inheritance_conflict(
        self, child_policy: Dict, parent_policy: Dict
    ) -> bool:
        """Check if there's an inheritance conflict"""
        child_rules = child_policy["rules"]
        parent_rules = parent_policy["rules"]

        # Check for rule overrides that conflict with parent
        for child_rule in child_rules:
            if "override" in child_rule:
                for parent_rule in parent_rules:
                    if self._rules_contradict(child_rule, parent_rule):
                        return True

        return False

    def _check_resource_conflicts(self):
        """Check for resource-specific conflicts"""
        resource_policies = {}

        # Group policies by resource
        for policy_id, policy in self.policies.items():
            for resource in policy["resources"]:
                if resource not in resource_policies:
                    resource_policies[resource] = []
                resource_policies[resource].append(policy_id)

        # Check for conflicts within each resource
        for resource, policy_ids in resource_policies.items():
            if len(policy_ids) > 1:
                # Multiple policies affect the same resource
                if self._resource_has_conflicts(resource, policy_ids):
                    conflict = PolicyConflict(
                        conflict_type=ConflictType.RESOURCE_CONFLICT,
                        severity="high",
                        description=f"Multiple policies conflict for resource: {resource}",
                        affected_policies=policy_ids,
                        affected_resources=[resource],
                        resolution_suggestions=[
                            "Consolidate resource policies",
                            "Define clear policy precedence",
                            "Use resource-specific policy inheritance",
                        ],
                    )
                    self.conflicts.append(conflict)

    def _resource_has_conflicts(self, resource: str, policy_ids: List[str]) -> bool:
        """Check if a resource has conflicting policies"""
        policies = [self.policies[pid] for pid in policy_ids]

        # Check for conflicting access patterns
        access_patterns = set()
        for policy in policies:
            access = self._get_resource_access(policy["rules"], resource)
            access_patterns.add(access)

        return len(access_patterns) > 1

    def _check_timing_conflicts(self):
        """Check for timing-related conflicts"""
        for policy_id, policy in self.policies.items():
            if "schedule" in policy["data"]:
                schedule = policy["data"]["schedule"]

                # Check for conflicting schedules with other policies
                for other_id, other_policy in self.policies.items():
                    if other_id != policy_id and "schedule" in other_policy["data"]:
                        other_schedule = other_policy["data"]["schedule"]

                        if self._schedules_conflict(schedule, other_schedule):
                            conflict = PolicyConflict(
                                conflict_type=ConflictType.TIMING_CONFLICT,
                                severity="low",
                                description=f"Schedule conflict between {policy_id} and {other_id}",
                                affected_policies=[policy_id, other_id],
                                affected_resources=list(
                                    policy["resources"] | other_policy["resources"]
                                ),
                                resolution_suggestions=[
                                    "Adjust policy schedules",
                                    "Use time-based precedence",
                                    "Implement schedule coordination",
                                ],
                            )
                            self.conflicts.append(conflict)

    def _schedules_conflict(self, schedule_a: Dict, schedule_b: Dict) -> bool:
        """Check if two schedules conflict"""
        # Simple overlap check - in practice, this would be more sophisticated
        if "start_time" in schedule_a and "start_time" in schedule_b:
            if schedule_a["start_time"] == schedule_b["start_time"]:
                return True

        return False

    def generate_report(self, output_file: Optional[Path] = None) -> str:
        """Generate a conflict report"""
        if not self.conflicts:
            report = "🎉 No policy conflicts detected!\n"
        else:
            report = f"⚠️  Found {len(self.conflicts)} policy conflicts:\n\n"

            # Group by severity
            by_severity = {}
            for conflict in self.conflicts:
                if conflict.severity not in by_severity:
                    by_severity[conflict.severity] = []
                by_severity[conflict.severity].append(conflict)

            # Report by severity (critical first)
            severity_order = ["critical", "high", "medium", "low"]
            for severity in severity_order:
                if severity in by_severity:
                    conflicts = by_severity[severity]
                    report += (
                        f"\n{severity.upper()} SEVERITY ({len(conflicts)} conflicts):\n"
                    )
                    report += "=" * 50 + "\n"

                    for i, conflict in enumerate(conflicts, 1):
                        report += f"\n{i}. {conflict.description}\n"
                        report += f"   Type: {conflict.conflict_type.value}\n"
                        policies_str = ", ".join(conflict.affected_policies)
                        report += f"   Affected Policies: {policies_str}\n"
                        resources_str = ", ".join(conflict.affected_resources)
                        report += f"   Affected Resources: {resources_str}\n"
                        report += "   Resolution Suggestions:\n"
                        for suggestion in conflict.resolution_suggestions:
                            report += f"     - {suggestion}\n"
                        report += "\n"

        if output_file:
            with open(output_file, "w", encoding="utf-8") as f:
                f.write(report)
            print(f"📄 Report saved to: {output_file}")

        return report

    def suggest_resolutions(self) -> Dict[str, List[str]]:
        """Generate resolution suggestions for all conflicts"""
        resolutions = {}

        for conflict in self.conflicts:
            policy_key = conflict.affected_policies[0]
            if policy_key not in resolutions:
                resolutions[policy_key] = []

            resolutions[policy_key].extend(conflict.resolution_suggestions)

        return resolutions


def main():
    """Main function"""
    parser = argparse.ArgumentParser(
        description="Check for policy conflicts in Provability-Fabric"
    )
    parser.add_argument(
        "policy_files", nargs="+", help="Policy files to analyze (YAML or JSON)"
    )
    parser.add_argument("--output", "-o", help="Output file for the conflict report")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")

    args = parser.parse_args()

    # Initialize analyzer
    analyzer = PolicyAnalyzer()

    # Load policy files
    print("🔍 Loading policy files...")
    for policy_file in args.policy_files:
        file_path = Path(policy_file)
        if not file_path.exists():
            print(f"❌ File not found: {policy_file}")
            sys.exit(1)

        analyzer.load_policy_file(file_path)

    if not analyzer.policies:
        print("❌ No valid policy files loaded")
        sys.exit(1)

    print(f"✅ Loaded {len(analyzer.policies)} policy files")

    # Detect conflicts
    print("\n🔍 Analyzing policies for conflicts...")
    conflicts = analyzer.detect_conflicts()

    if args.verbose:
        print(f"Found {len(conflicts)} conflicts")

    # Generate report
    output_file = Path(args.output) if args.output else None
    report = analyzer.generate_report(output_file)

    print("\n" + report)

    # Exit with error code if conflicts found
    if conflicts:
        critical_count = sum(1 for c in conflicts if c.severity == "critical")
        high_count = sum(1 for c in conflicts if c.severity == "high")

        if critical_count > 0 or high_count > 0:
            print("❌ Critical or high-severity conflicts detected")
            sys.exit(1)
        else:
            print("⚠️  Conflicts detected but none are critical")
            sys.exit(0)
    else:
        print("🎉 No conflicts detected")
        sys.exit(0)


if __name__ == "__main__":
    main()
