#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

"""
AI Spec-Assistant Agent

Uses OpenAI function-calls to analyze draft PRs and propose:
- New REQ/NFR lines for specifications
- Lean skeleton code for proofs
- Validation tests for requirements
"""

import os
import json
import re
import argparse
import openai
from typing import Dict, List, Optional, Any
from dataclasses import dataclass
from pathlib import Path
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class SpecSuggestion:
    """Represents a suggestion for specification improvement"""

    type: str  # 'requirement', 'assumption', 'proof', 'test'
    content: str
    reasoning: str
    confidence: float
    line_number: Optional[int] = None


@dataclass
class LeanSkeleton:
    """Represents a Lean proof skeleton"""

    theorem_name: str
    statement: str
    proof_structure: List[str]
    imports: List[str]
    dependencies: List[str]


class SpecAssistantAgent:
    """AI agent for specification assistance"""

    def __init__(self, openai_api_key: str):
        self.client = openai.OpenAI(api_key=openai_api_key)
        self.allowed_words = [
            "MUST",
            "SHALL",
            "REQUIRED",
            "SHOULD",
            "RECOMMENDED",
            "MAY",
            "OPTIONAL",
        ]
        self.prohibited_words = ["MUSTN'T", "SHAN'T", "WON'T", "CANNOT", "IMPOSSIBLE"]

    def analyze_pr_diff(self, diff_content: str) -> List[SpecSuggestion]:
        """Analyze PR diff and generate suggestions"""

        # Extract markdown files from diff
        markdown_files = self._extract_markdown_files(diff_content)

        suggestions = []

        for file_path, file_content in markdown_files.items():
            if self._is_spec_file(file_path):
                file_suggestions = self._analyze_spec_file(file_path, file_content)
                suggestions.extend(file_suggestions)

        return suggestions

    def generate_lean_skeleton(self, requirement: str) -> LeanSkeleton:
        """Generate Lean proof skeleton for a requirement"""

        prompt = f"""
        Generate a Lean proof skeleton for the following requirement:
        
        {requirement}
        
        Provide:
        1. Theorem name
        2. Formal statement
        3. Proof structure (list of steps)
        4. Required imports
        5. Dependencies
        """

        response = self.client.chat.completions.create(
            model="gpt-4",
            messages=[
                {
                    "role": "system",
                    "content": "You are a Lean theorem prover expert. Generate formal proof skeletons.",
                },
                {"role": "user", "content": prompt},
            ],
            functions=[
                {
                    "name": "generate_lean_skeleton",
                    "description": "Generate Lean proof skeleton",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "theorem_name": {"type": "string"},
                            "statement": {"type": "string"},
                            "proof_structure": {
                                "type": "array",
                                "items": {"type": "string"},
                            },
                            "imports": {"type": "array", "items": {"type": "string"}},
                            "dependencies": {
                                "type": "array",
                                "items": {"type": "string"},
                            },
                        },
                        "required": [
                            "theorem_name",
                            "statement",
                            "proof_structure",
                            "imports",
                            "dependencies",
                        ],
                    },
                }
            ],
            function_call={"name": "generate_lean_skeleton"},
        )

        result = json.loads(response.choices[0].message.function_call.arguments)
        return LeanSkeleton(**result)

    def validate_spec_language(self, content: str) -> List[str]:
        """Validate specification language for compliance"""

        violations = []

        # Check for prohibited words
        for word in self.prohibited_words:
            if word.lower() in content.lower():
                violations.append(f"Prohibited word '{word}' found")

        # Check for proper requirement language
        requirement_pattern = r"\b(REQ|NFR)\s+\d+"
        if not re.search(requirement_pattern, content):
            violations.append("Missing proper REQ/NFR numbering")

        # Check for traceability
        if "REQ" in content or "NFR" in content:
            if not re.search(r"→\s*REQ|→\s*NFR", content):
                violations.append("Missing traceability arrows (→)")

        return violations

    def propose_requirements(self, context: str) -> List[SpecSuggestion]:
        """Propose new requirements based on context"""

        prompt = f"""
        Analyze the following specification context and propose missing requirements:
        
        {context}
        
        Consider:
        1. Security requirements
        2. Performance requirements  
        3. Privacy requirements
        4. Compliance requirements
        5. Usability requirements
        
        Use proper REQ/NFR format with traceability.
        """

        response = self.client.chat.completions.create(
            model="gpt-4",
            messages=[
                {
                    "role": "system",
                    "content": "You are a specification expert. Propose requirements using proper format.",
                },
                {"role": "user", "content": prompt},
            ],
            functions=[
                {
                    "name": "propose_requirements",
                    "description": "Propose new requirements",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "suggestions": {
                                "type": "array",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "type": {"type": "string"},
                                        "content": {"type": "string"},
                                        "reasoning": {"type": "string"},
                                        "confidence": {"type": "number"},
                                    },
                                },
                            }
                        },
                    },
                }
            ],
            function_call={"name": "propose_requirements"},
        )

        result = json.loads(response.choices[0].message.function_call.arguments)
        return [SpecSuggestion(**s) for s in result["suggestions"]]

    def generate_validation_tests(self, requirement: str) -> List[str]:
        """Generate validation tests for a requirement"""

        prompt = f"""
        Generate validation tests for the following requirement:
        
        {requirement}
        
        Provide:
        1. Unit tests
        2. Integration tests
        3. Property-based tests
        4. Edge case tests
        """

        response = self.client.chat.completions.create(
            model="gpt-4",
            messages=[
                {
                    "role": "system",
                    "content": "You are a testing expert. Generate comprehensive validation tests.",
                },
                {"role": "user", "content": prompt},
            ],
        )

        # Parse response into test cases
        test_content = response.choices[0].message.content
        tests = self._parse_test_cases(test_content)

        return tests

    def _extract_markdown_files(self, diff_content: str) -> Dict[str, str]:
        """Extract markdown files from diff content"""

        files = {}
        current_file = None
        current_content = []

        for line in diff_content.split("\n"):
            if line.startswith("+++ b/"):
                if current_file and current_content:
                    files[current_file] = "\n".join(current_content)
                current_file = line[6:]  # Remove '+++ b/'
                current_content = []
            elif line.startswith("+") and not line.startswith("+++"):
                current_content.append(line[1:])  # Remove '+'

        if current_file and current_content:
            files[current_file] = "\n".join(current_content)

        return files

    def _is_spec_file(self, file_path: str) -> bool:
        """Check if file is a specification file"""

        spec_patterns = [
            r"spec\.md$",
            r"requirements\.md$",
            r"\.spec\.md$",
            r"docs/specs/",
            r"spec-templates/",
        ]

        return any(re.search(pattern, file_path) for pattern in spec_patterns)

    def _analyze_spec_file(self, file_path: str, content: str) -> List[SpecSuggestion]:
        """Analyze a specification file and generate suggestions"""

        suggestions = []

        # Validate language compliance
        violations = self.validate_spec_language(content)
        for violation in violations:
            suggestions.append(
                SpecSuggestion(
                    type="validation",
                    content=f"Language violation: {violation}",
                    reasoning="Specification language must comply with standards",
                    confidence=0.9,
                )
            )

        # Propose missing requirements
        req_suggestions = self.propose_requirements(content)
        suggestions.extend(req_suggestions)

        # Generate Lean skeletons for requirements
        requirements = self._extract_requirements(content)
        for req in requirements:
            lean_skeleton = self.generate_lean_skeleton(req)
            suggestions.append(
                SpecSuggestion(
                    type="proof",
                    content=f"Lean skeleton for {lean_skeleton.theorem_name}",
                    reasoning="Formal proof needed for requirement",
                    confidence=0.8,
                )
            )

        # Generate validation tests
        for req in requirements:
            tests = self.generate_validation_tests(req)
            suggestions.append(
                SpecSuggestion(
                    type="test",
                    content=f"Validation tests: {len(tests)} test cases",
                    reasoning="Comprehensive testing needed",
                    confidence=0.7,
                )
            )

        return suggestions

    def _extract_requirements(self, content: str) -> List[str]:
        """Extract requirements from specification content"""

        requirements = []

        # Find REQ/NFR lines
        req_pattern = r"(REQ|NFR)\s+\d+[:\s]+(.+)"
        matches = re.findall(req_pattern, content)

        for req_type, req_content in matches:
            requirements.append(f"{req_type}: {req_content.strip()}")

        return requirements

    def _parse_test_cases(self, test_content: str) -> List[str]:
        """Parse test cases from AI response"""

        tests = []

        # Simple parsing - look for test patterns
        test_patterns = [
            r"def test_\w+\(\):",
            r'it\([\'"][^\'"]+[\'"]',
            r'describe\([\'"][^\'"]+[\'"]',
            r"assert\(",
            r"expect\(",
        ]

        lines = test_content.split("\n")
        for line in lines:
            if any(re.search(pattern, line) for pattern in test_patterns):
                tests.append(line.strip())

        return tests

    def format_suggestions(self, suggestions: List[SpecSuggestion]) -> str:
        """Format suggestions for GitHub comment"""

        if not suggestions:
            return "No suggestions found for this specification."

        comment = "## AI Spec-Assistant Suggestions 🤖\n\n"

        # Group by type
        by_type = {}
        for suggestion in suggestions:
            if suggestion.type not in by_type:
                by_type[suggestion.type] = []
            by_type[suggestion.type].append(suggestion)

        for suggestion_type, type_suggestions in by_type.items():
            comment += f"### {suggestion_type.title()} Suggestions\n\n"

            for suggestion in type_suggestions:
                comment += f"**{suggestion.content}**\n"
                comment += f"*Reasoning: {suggestion.reasoning}*\n"
                comment += f"*Confidence: {suggestion.confidence:.1%}*\n\n"

        comment += "---\n*Generated by AI Spec-Assistant*"

        return comment


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="AI Spec-Assistant Agent")
    parser.add_argument("--diff-file", help="Path to diff file")
    parser.add_argument("--output", help="Output file for suggestions")
    parser.add_argument("--api-key", help="OpenAI API key")
    parser.add_argument("--test", action="store_true", help="Run in test mode")

    args = parser.parse_args()

    # Use API key from args or environment
    api_key = args.api_key or os.getenv("OPENAI_API_KEY", "test-key")
    agent = SpecAssistantAgent(api_key)

    if args.test:
        # Test with sample content
        sample_content = """
        REQ 1: The system MUST authenticate users before allowing access.
        REQ 2: The system SHOULD provide audit logs for all actions.
        """

        suggestions = agent.propose_requirements(sample_content)

        for suggestion in suggestions:
            print(f"Type: {suggestion.type}")
            print(f"Content: {suggestion.content}")
            print(f"Reasoning: {suggestion.reasoning}")
            print(f"Confidence: {suggestion.confidence}")
            print("---")

    elif args.diff_file:
        # Read diff file
        with open(args.diff_file, "r") as f:
            diff_content = f.read()

        # Analyze diff
        suggestions = agent.analyze_pr_diff(diff_content)

        # Convert to JSON for output
        suggestions_json = []
        for suggestion in suggestions:
            suggestions_json.append(
                {
                    "type": suggestion.type,
                    "content": suggestion.content,
                    "reasoning": suggestion.reasoning,
                    "confidence": suggestion.confidence,
                    "line_number": suggestion.line_number,
                }
            )

        # Write output
        if args.output:
            with open(args.output, "w") as f:
                json.dump(suggestions_json, f, indent=2)
            logger.info(f"Suggestions written to {args.output}")
        else:
            print(json.dumps(suggestions_json, indent=2))

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
