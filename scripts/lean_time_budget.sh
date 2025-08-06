#!/bin/bash
# Lean Time Budget Checker
# Times per-file builds and enforces time budgets

set -euo pipefail

# Configuration
TOTAL_TIMEOUT=360  # 6 minutes in seconds
PER_FILE_TIMEOUT=90  # 90 seconds per file
WARN_THRESHOLD=60   # Warn at 60 seconds
GRACE_PERIOD=30     # 30 seconds grace period

# Colors for output
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Global state
TOTAL_TIME=0
SLOW_FILES=()
FAILED_FILES=()
WARNED_FILES=()

echo "🔧 Lean Time Budget Checker"
echo "📋 Total budget: ${TOTAL_TIMEOUT}s"
echo "📋 Per-file budget: ${PER_FILE_TIMEOUT}s"
echo "📋 Warning threshold: ${WARN_THRESHOLD}s"
echo ""

# Function to find all Lean files that need building
find_lean_targets() {
    local targets=()
    
    # Find all lakefile.lean files
    while IFS= read -r -d '' file; do
        local dir=$(dirname "$file")
        if [[ -d "$dir" ]]; then
            targets+=("$dir")
        fi
    done < <(find . -name "lakefile.lean" -print0 2>/dev/null || true)
    
    echo "${targets[@]}"
}

# Function to time a build
time_build() {
    local target="$1"
    local start_time=$(date +%s)
    
    echo -n "🔨 Building $target... "
    
    # Run lake build with timeout
    if timeout "${PER_FILE_TIMEOUT}s" lake build "$target" >/dev/null 2>&1; then
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        
        echo -e "${GREEN}✅ ${duration}s${NC}"
        
        # Check if it's slow
        if [[ $duration -gt $WARN_THRESHOLD ]]; then
            WARNED_FILES+=("$target:${duration}s")
        fi
        
        TOTAL_TIME=$((TOTAL_TIME + duration))
        return 0
    else
        local exit_code=$?
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        
        if [[ $exit_code -eq 124 ]]; then
            echo -e "${RED}⏰ TIMEOUT (${duration}s)${NC}"
            FAILED_FILES+=("$target:TIMEOUT")
        else
            echo -e "${RED}❌ FAILED (${duration}s)${NC}"
            FAILED_FILES+=("$target:FAILED")
        fi
        
        TOTAL_TIME=$((TOTAL_TIME + duration))
        return 1
    fi
}

# Function to check if we're approaching total timeout
check_total_budget() {
    local remaining=$((TOTAL_TIMEOUT - TOTAL_TIME))
    
    if [[ $remaining -lt $GRACE_PERIOD ]]; then
        echo -e "${YELLOW}⚠️  Warning: Only ${remaining}s remaining in total budget${NC}"
        return 1
    fi
    
    return 0
}

# Function to print results
print_results() {
    echo ""
    echo "="*60
    echo "📊 LEAN BUILD TIME RESULTS"
    echo "="*60
    
    echo -e "⏱️  Total build time: ${TOTAL_TIME}s / ${TOTAL_TIMEOUT}s"
    
    if [[ $TOTAL_TIME -gt $TOTAL_TIMEOUT ]]; then
        echo -e "${RED}❌ Total time exceeded budget!${NC}"
    else
        echo -e "${GREEN}✅ Total time within budget${NC}"
    fi
    
    echo ""
    
    if [[ ${#WARNED_FILES[@]} -gt 0 ]]; then
        echo -e "${YELLOW}⚠️  Slow files (${#WARNED_FILES[@]}):${NC}"
        for file in "${WARNED_FILES[@]}"; do
            echo "   $file"
        done
        echo ""
    fi
    
    if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
        echo -e "${RED}❌ Failed files (${#FAILED_FILES[@]}):${NC}"
        for file in "${FAILED_FILES[@]}"; do
            echo "   $file"
        done
        echo ""
    fi
    
    # Summary
    local total_files=$((${#WARNED_FILES[@]} + ${#FAILED_FILES[@]}))
    if [[ $total_files -eq 0 ]]; then
        echo -e "${GREEN}✅ All builds completed successfully!${NC}"
        return 0
    else
        echo -e "${RED}❌ Found $total_files problematic files${NC}"
        return 1
    fi
}

# Main execution
main() {
    local targets=($(find_lean_targets))
    
    if [[ ${#targets[@]} -eq 0 ]]; then
        echo "ℹ️  No Lean targets found"
        exit 0
    fi
    
    echo "📁 Found ${#targets[@]} Lean targets to build"
    echo ""
    
    # Build each target
    for target in "${targets[@]}"; do
        if ! check_total_budget; then
            echo -e "${YELLOW}⚠️  Stopping due to total budget constraint${NC}"
            break
        fi
        
        time_build "$target"
    done
    
    # Print results
    print_results
}

# Run main function
main "$@" 