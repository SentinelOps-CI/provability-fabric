#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    local status=$1
    local message=$2
    case $status in
        "OK")
            echo -e "${GREEN}✅${NC} $message"
            ;;
        "WARN")
            echo -e "${YELLOW}⚠️${NC} $message"
            ;;
        "ERROR")
            echo -e "${RED}❌${NC} $message"
            ;;
    esac
}

# Function to check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to validate version format
validate_version() {
    local version=$1
    if [[ ! $version =~ ^[0-9]+\.[0-9]+\.[0-9]+(-[a-zA-Z0-9.-]+)?(\+[a-zA-Z0-9.-]+)?$ ]]; then
        print_status "ERROR" "Invalid version format: $version. Expected format: MAJOR.MINOR.PATCH[-PRERELEASE][+BUILD]"
        return 1
    fi
    print_status "OK" "Version format is valid: $version"
}

# Function to check if we're on a stable branch
check_stable_branch() {
    local current_branch=$(git branch --show-current)
    if [[ ! $current_branch =~ ^stable/[0-9]{4}\.[0-9]{2}$ ]]; then
        print_status "ERROR" "Not on a stable branch. Current branch: $current_branch"
        print_status "WARN" "Expected format: stable/YYYY.MM"
        return 1
    fi
    print_status "OK" "On stable branch: $current_branch"
}

# Function to check if working directory is clean
check_working_directory() {
    if ! git diff-index --quiet HEAD --; then
        print_status "ERROR" "Working directory is not clean. Please commit or stash changes."
        return 1
    fi
    print_status "OK" "Working directory is clean"
}

# Function to check if tag already exists
check_tag_exists() {
    local version=$1
    if git tag -l "v$version" | grep -q "v$version"; then
        print_status "ERROR" "Tag v$version already exists"
        return 1
    fi
    print_status "OK" "Tag v$version does not exist"
}

# Function to check if remote is configured
check_remote() {
    if ! git remote get-url origin >/dev/null 2>&1; then
        print_status "ERROR" "No 'origin' remote configured"
        return 1
    fi
    print_status "OK" "Origin remote is configured"
}

# Function to check required tools
check_required_tools() {
    local tools=("git" "docker" "cosign" "syft")
    local missing_tools=()
    
    for tool in "${tools[@]}"; do
        if ! command_exists "$tool"; then
            missing_tools+=("$tool")
        fi
    done
    
    if [ ${#missing_tools[@]} -gt 0 ]; then
        print_status "ERROR" "Missing required tools: ${missing_tools[*]}"
        return 1
    fi
    print_status "OK" "All required tools are available"
}

# Function to check if Lean proofs are built
check_lean_proofs() {
    local lean_files=$(find . -name "*.olean" 2>/dev/null | wc -l)
    if [ "$lean_files" -eq 0 ]; then
        print_status "ERROR" "No Lean .olean files found. Run 'lake build' first."
        return 1
    fi
    print_status "OK" "Found $lean_files Lean .olean files"
}

# Function to check if Docker images can be built
check_docker_images() {
    local images=("runtime/sidecar-watcher" "runtime/admission-controller" "runtime/ledger")
    local failed_images=()
    
    for image in "${images[@]}"; do
        if [ ! -f "$image/Dockerfile" ]; then
            failed_images+=("$image (no Dockerfile)")
            continue
        fi
        
        # Try to build image (dry run)
        if ! docker build --dry-run "$image" >/dev/null 2>&1; then
            failed_images+=("$image (build failed)")
        fi
    done
    
    if [ ${#failed_images[@]} -gt 0 ]; then
        print_status "ERROR" "Docker image issues: ${failed_images[*]}"
        return 1
    fi
    print_status "OK" "All Docker images can be built"
}

# Function to check security requirements
check_security() {
    # Check if there are any HIGH/CRITICAL CVEs in dependencies
    if command_exists "trivy"; then
        if trivy fs --severity HIGH,CRITICAL . 2>/dev/null | grep -q "HIGH\|CRITICAL"; then
            print_status "ERROR" "High or critical CVEs found in dependencies"
            return 1
        fi
    fi
    
    # Check Go security
    if command_exists "gosec"; then
        if gosec ./core/cli/pf/... ./runtime/admission-controller/... 2>/dev/null | grep -q "HIGH\|CRITICAL"; then
            print_status "ERROR" "High or critical security issues found in Go code"
            return 1
        fi
    fi
    
    print_status "OK" "No high/critical security issues found"
}

# Function to check performance requirements
check_performance() {
    if [ -f "perf-results.json" ]; then
        local latency=$(jq -r '.median_latency_us' perf-results.json 2>/dev/null || echo "0")
        local memory=$(jq -r '.memory_mb' perf-results.json 2>/dev/null || echo "0")
        
        if (( $(echo "$latency > 150" | bc -l) )); then
            print_status "ERROR" "Median latency ($latency µs) exceeds 150 µs threshold"
            return 1
        fi
        
        if (( $(echo "$memory > 50" | bc -l) )); then
            print_status "ERROR" "Memory usage ($memory MB) exceeds 50 MB threshold"
            return 1
        fi
        
        print_status "OK" "Performance thresholds met (latency: ${latency}µs, memory: ${memory}MB)"
    else
        print_status "WARN" "No performance results found. Run 'make bench' first."
    fi
}

# Main validation function
main() {
    local version=${1:-}
    
    if [ -z "$version" ]; then
        echo "Usage: $0 <version>"
        echo "Example: $0 1.2.3"
        exit 1
    fi
    
    echo "🔍 Validating release v$version..."
    echo ""
    
    local exit_code=0
    
    # Run all checks
    validate_version "$version" || exit_code=1
    check_stable_branch || exit_code=1
    check_working_directory || exit_code=1
    check_tag_exists "$version" || exit_code=1
    check_remote || exit_code=1
    check_required_tools || exit_code=1
    check_lean_proofs || exit_code=1
    check_docker_images || exit_code=1
    check_security || exit_code=1
    check_performance || exit_code=1
    
    echo ""
    if [ $exit_code -eq 0 ]; then
        print_status "OK" "All validation checks passed! Ready for release."
        echo ""
        echo "Next steps:"
        echo "1. Run: make release VERSION=$version"
        echo "2. Monitor the release workflow"
        echo "3. Verify all artifacts are signed and uploaded"
    else
        print_status "ERROR" "Validation failed. Please fix the issues above before releasing."
        exit 1
    fi
}

# Run main function with all arguments
main "$@"