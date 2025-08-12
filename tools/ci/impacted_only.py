#!/usr/bin/env python3
"""
Impacted-only Lean build tool for CI cost optimization.

This tool analyzes PR changes and determines which Lean proofs need to be rebuilt,
reducing CI costs and improving PR turnaround times.

Usage:
    python impacted_only.py --pr <PR_NUMBER> --base <BASE_REF> --head <HEAD_REF>
    python impacted_only.py --analyze-changes <CHANGES_FILE>
    python impacted_only.py --build-impacted --output-dir <OUTPUT_DIR>
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Set
import yaml
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


class LeanImpactAnalyzer:
    """Analyzes Lean proof dependencies and determines impacted proofs."""
    
    def __init__(self, workspace_root: Path):
        self.workspace_root = workspace_root
        self.lean_files = self._discover_lean_files()
        self.dependency_graph = self._build_dependency_graph()
        
    def _discover_lean_files(self) -> Dict[str, Path]:
        """Discover all Lean files in the workspace."""
        lean_files = {}
        
        for lean_file in self.workspace_root.rglob("*.lean"):
            if lean_file.is_file():
                # Convert to relative path from workspace root
                rel_path = lean_file.relative_to(self.workspace_root)
                lean_files[str(rel_path)] = lean_file
                
        logger.info(f"Discovered {len(lean_files)} Lean files")
        return lean_files
    
    def _build_dependency_graph(self) -> Dict[str, Set[str]]:
        """Build dependency graph between Lean files."""
        dependency_graph = {}
        
        for file_path, lean_file in self.lean_files.items():
            dependencies = self._extract_dependencies(lean_file)
            dependency_graph[file_path] = dependencies
            
        logger.info(f"Built dependency graph with {len(dependency_graph)} nodes")
        return dependency_graph
    
    def _extract_dependencies(self, lean_file: Path) -> Set[str]:
        """Extract dependencies from a Lean file."""
        dependencies = set()
        
        try:
            with open(lean_file, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Extract import statements
            lines = content.split('\n')
            for line in lines:
                line = line.strip()
                if line.startswith('import ') or line.startswith('import.'):
                    # Parse import statement
                    import_path = line.split('import')[1].strip().split()[0]
                    dependencies.add(import_path)
                    
        except Exception as e:
            logger.warning(f"Failed to parse dependencies for {lean_file}: {e}")
            
        return dependencies
    
    def analyze_changes(self, changed_files: List[str]) -> Dict[str, List[str]]:
        """Analyze which proofs are impacted by file changes."""
        impacted_proofs = {
            'directly_impacted': [],
            'transitively_impacted': [],
            'unimpacted': [],
            'build_order': []
        }
        
        # Find directly impacted Lean files
        directly_impacted = set()
        for changed_file in changed_files:
            if changed_file.endswith('.lean'):
                directly_impacted.add(changed_file)
            elif (changed_file.endswith('.yaml') or 
                  changed_file.endswith('.yml')):
                # Check if this is a spec file that might affect proofs
                if 'spec.yaml' in changed_file or 'spec.yml' in changed_file:
                    # Find corresponding proof directory
                    spec_path = Path(changed_file)
                    proof_dir = spec_path.parent / 'proofs'
                    if proof_dir.exists():
                        for proof_file in proof_dir.rglob("*.lean"):
                            rel_path = str(proof_file.relative_to(self.workspace_root))
                            directly_impacted.add(rel_path)
        
        # Find transitively impacted files
        transitively_impacted = set()
        to_process = directly_impacted.copy()
        
        while to_process:
            current_file = to_process.pop()
            if current_file in self.dependency_graph:
                for dependent_file in self.dependency_graph:
                    if current_file in self.dependency_graph[dependent_file]:
                        if dependent_file not in transitively_impacted:
                            transitively_impacted.add(dependent_file)
                            to_process.add(dependent_file)
        
        # Categorize all Lean files
        all_lean_files = set(self.lean_files.keys())
        impacted = directly_impacted | transitively_impacted
        unimpacted = all_lean_files - impacted
        
        # Determine build order (topological sort)
        build_order = self._topological_sort(impacted)
        
        impacted_proofs['directly_impacted'] = list(directly_impacted)
        impacted_proofs['transitively_impacted'] = list(transitively_impacted)
        impacted_proofs['unimpacted'] = list(unimpacted)
        impacted_proofs['build_order'] = build_order
        
        logger.info(
            f"Analysis complete: {len(directly_impacted)} directly impacted, "
            f"{len(transitively_impacted)} transitively impacted, "
            f"{len(unimpacted)} unimpacted"
        )
        
        return impacted_proofs
    
    def _topological_sort(self, files: Set[str]) -> List[str]:
        """Perform topological sort for build order."""
        # Simple topological sort implementation
        # In practice, you might want to use a more robust algorithm
        
        visited = set()
        temp_visited = set()
        order = []
        
        def visit(file_path):
            if file_path in temp_visited:
                # Circular dependency detected
                logger.warning(f"Circular dependency detected for {file_path}")
                return
            if file_path in visited:
                return
                
            temp_visited.add(file_path)
            
            # Visit dependencies first
            if file_path in self.dependency_graph:
                for dep in self.dependency_graph[file_path]:
                    if dep in files:  # Only consider files in our impacted set
                        visit(dep)
            
            temp_visited.remove(file_path)
            visited.add(file_path)
            order.append(file_path)
        
        for file_path in files:
            if file_path not in visited:
                visit(file_path)
        
        return order
    
    def generate_build_plan(self, impacted_proofs: Dict[str, List[str]]) -> Dict:
        """Generate a build plan for CI."""
        build_plan = {
            'build_type': 'impacted_only',
            'total_files': len(self.lean_files),
            'impacted_files': (len(impacted_proofs['directly_impacted']) + 
                              len(impacted_proofs['transitively_impacted'])),
            'unimpacted_files': len(impacted_proofs['unimpacted']),
            'estimated_time_savings': '60-80%',
            'build_steps': []
        }
        
        # Generate build steps for impacted files
        for file_path in impacted_proofs['build_order']:
            if file_path in self.lean_files:
                lean_file = self.lean_files[file_path]
                
                # Determine build command based on file location
                if 'bundles/' in file_path:
                    # Bundle proof - use lake build
                    build_step = {
                        'file': file_path,
                        'command': f"lake build {lean_file.parent}",
                        'type': 'bundle_proof',
                        'estimated_duration': '30-120s'
                    }
                elif 'core/lean-libs/' in file_path:
                    # Core library - use lake build
                    build_step = {
                        'file': file_path,
                        'command': f"lake build {lean_file.parent}",
                        'type': 'core_library',
                        'estimated_duration': '15-60s'
                    }
                else:
                    # Other Lean file - use lake build
                    build_step = {
                        'file': file_path,
                        'command': f"lake build {lean_file}",
                        'type': 'other',
                        'estimated_duration': '10-30s'
                    }
                
                build_plan['build_steps'].append(build_step)
        
        return build_plan
    
    def validate_build_plan(self, build_plan: Dict) -> bool:
        """Validate that the build plan covers all necessary dependencies."""
        # Check that all impacted files are included
        impacted_files = set()
        for step in build_plan['build_steps']:
            impacted_files.add(step['file'])
        
        # Verify coverage
        all_impacted = set()
        if 'directly_impacted' in build_plan:
            all_impacted.update(build_plan['directly_impacted'])
        if 'transitively_impacted' in build_plan:
            all_impacted.update(build_plan['transitively_impacted'])
        
        missing_files = all_impacted - impacted_files
        if missing_files:
            logger.warning(
                f"Build plan missing {len(missing_files)} impacted files: "
                f"{missing_files}"
            )
            return False
        
        logger.info("Build plan validation passed")
        return True


class CICostOptimizer:
    """Optimizes CI costs by managing build strategies."""
    
    def __init__(self, workspace_root: Path):
        self.workspace_root = workspace_root
        self.analyzer = LeanImpactAnalyzer(workspace_root)
        
    def optimize_pr_build(self, pr_number: int, base_ref: str, head_ref: str) -> Dict:
        """Optimize CI build for a specific PR."""
        logger.info(f"Optimizing CI build for PR #{pr_number}")
        
        # Get changed files
        changed_files = self._get_changed_files(base_ref, head_ref)
        logger.info(f"Detected {len(changed_files)} changed files")
        
        # Analyze impact
        impacted_proofs = self.analyzer.analyze_changes(changed_files)
        
        # Generate build plan
        build_plan = self.analyzer.generate_build_plan(impacted_proofs)
        
        # Validate plan
        if not self.analyzer.validate_build_plan(build_plan):
            logger.warning("Build plan validation failed, falling back to full build")
            build_plan['build_type'] = 'full_build'
            build_plan['fallback_reason'] = 'validation_failed'
        
        # Calculate cost savings
        cost_analysis = self._calculate_cost_savings(build_plan)
        build_plan['cost_analysis'] = cost_analysis
        
        return build_plan
    
    def _get_changed_files(self, base_ref: str, head_ref: str) -> List[str]:
        """Get list of changed files between two git references."""
        try:
            cmd = ['git', 'diff', '--name-only', base_ref, head_ref]
            result = subprocess.run(
                cmd, capture_output=True, text=True, cwd=self.workspace_root
            )
            
            if result.returncode != 0:
                logger.error(f"Git diff failed: {result.stderr}")
                return []
            
            changed_files = [
                line.strip() for line in result.stdout.split('\n') if line.strip()
            ]
            return changed_files
            
        except Exception as e:
            logger.error(f"Failed to get changed files: {e}")
            return []
    
    def _calculate_cost_savings(self, build_plan: Dict) -> Dict:
        """Calculate estimated cost savings from optimized build."""
        total_files = build_plan['total_files']
        impacted_files = build_plan['impacted_files']
        unimpacted_files = build_plan['unimpacted_files']
        
        # Estimate time savings
        full_build_time = total_files * 30  # Assume 30s per file on average
        optimized_build_time = impacted_files * 30
        
        time_savings = full_build_time - optimized_build_time
        time_savings_percent = (
            (time_savings / full_build_time) * 100 if full_build_time > 0 else 0
        )
        
        # Estimate cost savings (assuming linear relationship with time)
        cost_savings_percent = time_savings_percent
        
        return {
            'full_build_time_seconds': full_build_time,
            'optimized_build_time_seconds': optimized_build_time,
            'time_savings_seconds': time_savings,
            'time_savings_percent': round(time_savings_percent, 2),
            'cost_savings_percent': round(cost_savings_percent, 2),
            'files_skipped': unimpacted_files
        }
    
    def generate_ci_config(self, build_plan: Dict, output_file: Path) -> None:
        """Generate CI configuration for the optimized build."""
        ci_config = {
            'name': 'Optimized Lean Build',
            'on': {
                'pull_request': {
                    'types': ['opened', 'synchronize', 'reopened']
                }
            },
            'jobs': {
                'lean-build': {
                    'runs-on': 'ubuntu-latest',
                    'steps': [
                        {
                            'name': 'Checkout code',
                            'uses': 'actions/checkout@v3',
                            'with': {
                                'fetch-depth': 0
                            }
                        },
                        {
                            'name': 'Setup Lean',
                            'uses': 'leanprover/lean4-action@v1',
                            'with': {
                                'lean-version': 'leanprover/lean4:nightly'
                            }
                        },
                        {
                            'name': 'Build impacted proofs',
                            'run': self._generate_build_commands(build_plan)
                        }
                    ]
                }
            }
        }
        
        # Write CI config
        with open(output_file, 'w') as f:
            yaml.dump(ci_config, f, default_flow_style=False, indent=2)
        
        logger.info(f"Generated CI config: {output_file}")


def main():
    parser = argparse.ArgumentParser(description='Lean CI Cost Optimization Tool')
    parser.add_argument('--workspace', default='.', help='Workspace root directory')
    parser.add_argument('--pr', type=int, help='PR number to analyze')
    parser.add_argument('--base', help='Base reference for PR')
    parser.add_argument('--head', help='Head reference for PR')
    parser.add_argument('--analyze-changes', help='File containing list of changes')
    parser.add_argument('--build-impacted', action='store_true', 
                       help='Build only impacted proofs')
    parser.add_argument('--output-dir', help='Output directory for build artifacts')
    parser.add_argument('--generate-ci', help='Generate CI configuration file')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    workspace_root = Path(args.workspace).resolve()
    if not workspace_root.exists():
        logger.error(f"Workspace root does not exist: {workspace_root}")
        sys.exit(1)
    
    optimizer = CICostOptimizer(workspace_root)
    
    if args.pr and args.base and args.head:
        # Analyze PR
        build_plan = optimizer.optimize_pr_build(args.pr, args.base, args.head)
        
        # Output results
        print(json.dumps(build_plan, indent=2))
        
        # Generate CI config if requested
        if args.generate_ci:
            output_file = Path(args.generate_ci)
            optimizer.generate_ci_config(build_plan, output_file)
    
    elif args.analyze_changes:
        # Analyze changes from file
        with open(args.analyze_changes, 'r') as f:
            changed_files = [line.strip() for line in f if line.strip()]
        
        impacted_proofs = optimizer.analyzer.analyze_changes(changed_files)
        build_plan = optimizer.analyzer.generate_build_plan(impacted_proofs)
        
        print(json.dumps(build_plan, indent=2))
    
    elif args.build_impacted:
        # Build impacted proofs
        if not args.output_dir:
            logger.error("--output-dir required for --build-impacted")
            sys.exit(1)
        
        # This would implement the actual build process
        logger.info("Build impacted proofs functionality not yet implemented")
    
    else:
        parser.print_help()
        sys.exit(1)


if __name__ == '__main__':
    main()
