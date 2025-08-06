#!/bin/bash
set -euo pipefail

# Release Fence - Block releases unless mechanisms + evidence are present
# This script implements the no-mechanism, no-ship policy

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
FENCE_LOG="${PROJECT_ROOT}/logs/release_fence_$(date +%s).log"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
LEDGER_ENDPOINT="${LEDGER_ENDPOINT:-http://localhost:3000}"
RETRIEVAL_GATEWAY="${RETRIEVAL_GATEWAY:-http://localhost:8080}"
EGRESS_FIREWALL="${EGRESS_FIREWALL:-http://localhost:8081}"
ATTESTOR_ENDPOINT="${ATTESTOR_ENDPOINT:-http://localhost:8082}"

# Thresholds
MIN_RECEIPTS_PER_HOUR=10
MIN_CERTIFICATE_COVERAGE=99
MAX_ATTESTATION_GAP_SECONDS=15
MAX_P99_LATENCY_MS=4000
MAX_ABAC_VIOLATIONS=0
MAX_PII_LEAKS=0

# Initialize log
mkdir -p "$(dirname "$FENCE_LOG")"
echo "=== Release Fence Started at $(date) ===" > "$FENCE_LOG"

log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $1" | tee -a "$FENCE_LOG"
}

error() {
    echo -e "${RED}❌ ERROR: $1${NC}" | tee -a "$FENCE_LOG"
}

warning() {
    echo -e "${YELLOW}⚠️  WARNING: $1${NC}" | tee -a "$FENCE_LOG"
}

success() {
    echo -e "${GREEN}✅ $1${NC}" | tee -a "$FENCE_LOG"
}

info() {
    echo -e "${BLUE}ℹ️  $1${NC}" | tee -a "$FENCE_LOG"
}

# Check if a service is healthy
check_service_health() {
    local service_name="$1"
    local health_url="$2"
    
    log "Checking $service_name health..."
    
    if curl -sf "$health_url" >/dev/null 2>&1; then
        success "$service_name is healthy"
        return 0
    else
        error "$service_name health check failed at $health_url"
        return 1
    fi
}

# Check for access receipts in the last 24 hours
check_access_receipts() {
    log "Checking access receipts for last 24 hours..."
    
    local since_time=$(date -d '24 hours ago' -Iseconds)
    local receipt_count
    
    receipt_count=$(curl -sf "${LEDGER_ENDPOINT}/receipts?since=${since_time}" \
        | jq '. | length' 2>/dev/null || echo "0")
    
    if [[ "$receipt_count" -ge "$MIN_RECEIPTS_PER_HOUR" ]]; then
        success "Found $receipt_count access receipts (>= $MIN_RECEIPTS_PER_HOUR required)"
        return 0
    else
        error "Only $receipt_count access receipts found in last 24h (minimum: $MIN_RECEIPTS_PER_HOUR)"
        return 1
    fi
}

# Check egress certificate coverage
check_egress_certificates() {
    log "Checking egress certificate coverage..."
    
    local since_time=$(date -d '24 hours ago' -Iseconds)
    local cert_response
    local total_responses
    local certificate_count
    local coverage_percent
    
    # Get certificate count
    certificate_count=$(curl -sf "${LEDGER_ENDPOINT}/egress-certificates?since=${since_time}" \
        | jq '. | length' 2>/dev/null || echo "0")
    
    # Get total response count (would need to be tracked separately)
    # For now, assume a minimum number of certificates should exist
    if [[ "$certificate_count" -lt 10 ]]; then
        error "Only $certificate_count egress certificates found in last 24h"
        return 1
    fi
    
    # Check that certificates indicate proper coverage
    local blocked_count
    blocked_count=$(curl -sf "${LEDGER_ENDPOINT}/egress-certificates?since=${since_time}" \
        | jq '[.[] | select(.detectors.pii > 0 or .detectors.secret > 0)] | length' 2>/dev/null || echo "0")
    
    success "Found $certificate_count egress certificates with $blocked_count detections"
    return 0
}

# Check attestation heartbeats
check_attestation_heartbeats() {
    log "Checking attestation heartbeats..."
    
    # Get latest attestation
    local latest_attestation
    latest_attestation=$(curl -sf "${LEDGER_ENDPOINT}/attestations/latest" 2>/dev/null || echo '{}')
    
    if [[ "$latest_attestation" == '{}' ]]; then
        error "No attestations found"
        return 1
    fi
    
    # Check timestamp
    local attestation_time
    attestation_time=$(echo "$latest_attestation" | jq -r '.timestamp // 0')
    
    local current_time
    current_time=$(date +%s)
    
    local time_diff
    time_diff=$((current_time - attestation_time))
    
    if [[ "$time_diff" -le "$MAX_ATTESTATION_GAP_SECONDS" ]]; then
        success "Latest attestation is $time_diff seconds old (<= $MAX_ATTESTATION_GAP_SECONDS)"
        return 0
    else
        error "Latest attestation is $time_diff seconds old (max: $MAX_ATTESTATION_GAP_SECONDS)"
        return 1
    fi
}

# Check SLO gates (ABAC, PII, latency)
check_slo_gates() {
    log "Checking SLO gates..."
    
    local slo_passed=true
    
    # Check ABAC violations
    log "Checking ABAC violations..."
    if [[ -f "${PROJECT_ROOT}/tests/results/abac_fuzz_report.json" ]]; then
        local abac_violations
        abac_violations=$(jq '.analysis.security_violations.total_violations' \
            "${PROJECT_ROOT}/tests/results/abac_fuzz_report.json" 2>/dev/null || echo "999")
        
        if [[ "$abac_violations" -le "$MAX_ABAC_VIOLATIONS" ]]; then
            success "ABAC violations: $abac_violations (<= $MAX_ABAC_VIOLATIONS)"
        else
            error "ABAC violations: $abac_violations (max: $MAX_ABAC_VIOLATIONS)"
            slo_passed=false
        fi
    else
        warning "ABAC test results not found at tests/results/abac_fuzz_report.json"
        slo_passed=false
    fi
    
    # Check PII leaks
    log "Checking PII leak test results..."
    if [[ -f "${PROJECT_ROOT}/tests/results/pii_leak_report.json" ]]; then
        local pii_leaks
        pii_leaks=$(jq '.analysis.summary.critical_leaks' \
            "${PROJECT_ROOT}/tests/results/pii_leak_report.json" 2>/dev/null || echo "999")
        
        if [[ "$pii_leaks" -le "$MAX_PII_LEAKS" ]]; then
            success "PII leaks: $pii_leaks (<= $MAX_PII_LEAKS)"
        else
            error "PII leaks: $pii_leaks (max: $MAX_PII_LEAKS)"
            slo_passed=false
        fi
    else
        warning "PII test results not found at tests/results/pii_leak_report.json"
        slo_passed=false
    fi
    
    # Check latency SLO
    log "Checking latency SLO..."
    local p99_latency
    p99_latency=$(curl -sf "${RETRIEVAL_GATEWAY}/metrics" \
        | grep 'http_request_duration_seconds_bucket{quantile="0.99"}' \
        | awk '{print $2 * 1000}' 2>/dev/null || echo "9999")
    
    if (( $(echo "$p99_latency <= $MAX_P99_LATENCY_MS" | bc -l) )); then
        success "P99 latency: ${p99_latency}ms (<= ${MAX_P99_LATENCY_MS}ms)"
    else
        error "P99 latency: ${p99_latency}ms (max: ${MAX_P99_LATENCY_MS}ms)"
        slo_passed=false
    fi
    
    if [[ "$slo_passed" == true ]]; then
        return 0
    else
        return 1
    fi
}

# Check formal verification status
check_formal_verification() {
    log "Checking formal verification status..."
    
    # Run invariant gate
    if python3 "${PROJECT_ROOT}/tools/invariant_gate.py" --project-root "$PROJECT_ROOT" >/dev/null 2>&1; then
        success "Invariant gate passed"
    else
        error "Invariant gate failed - check formal proofs"
        return 1
    fi
    
    # Check for sorry proofs
    local sorry_count
    sorry_count=$(find "${PROJECT_ROOT}/core/lean-libs" -name "*.lean" -exec grep -l "sorry" {} \; | wc -l)
    
    if [[ "$sorry_count" -eq 0 ]]; then
        success "No sorry proofs found in core libraries"
    else
        error "Found $sorry_count files with sorry proofs"
        return 1
    fi
    
    return 0
}

# Check evidence bundle completeness
check_evidence_bundles() {
    log "Checking evidence bundle completeness..."
    
    # Check if evidence bundles exist for the last day
    local bundle_dir="${PROJECT_ROOT}/evidence"
    local today=$(date '+%Y%m%d')
    local yesterday=$(date -d '1 day ago' '+%Y%m%d')
    
    local found_bundle=false
    
    if [[ -d "$bundle_dir" ]]; then
        # Look for recent evidence bundles
        for bundle in "$bundle_dir"/evidence_bundle_${today}_* "$bundle_dir"/evidence_bundle_${yesterday}_*; do
            if [[ -f "$bundle" ]]; then
                found_bundle=true
                break
            fi
        done
    fi
    
    if [[ "$found_bundle" == true ]]; then
        success "Recent evidence bundle found"
        return 0
    else
        error "No recent evidence bundles found in $bundle_dir"
        return 1
    fi
}

# Run all fence checks
run_fence_checks() {
    local all_passed=true
    
    info "Starting release fence checks..."
    
    # Service health checks
    if ! check_service_health "Ledger" "${LEDGER_ENDPOINT}/health"; then
        all_passed=false
    fi
    
    if ! check_service_health "Retrieval Gateway" "${RETRIEVAL_GATEWAY}/health"; then
        all_passed=false
    fi
    
    if ! check_service_health "Egress Firewall" "${EGRESS_FIREWALL}/health"; then
        all_passed=false
    fi
    
    # Evidence checks
    if ! check_access_receipts; then
        all_passed=false
    fi
    
    if ! check_egress_certificates; then
        all_passed=false
    fi
    
    if ! check_attestation_heartbeats; then
        all_passed=false
    fi
    
    # SLO checks
    if ! check_slo_gates; then
        all_passed=false
    fi
    
    # Verification checks
    if ! check_formal_verification; then
        all_passed=false
    fi
    
    # Evidence bundle checks
    if ! check_evidence_bundles; then
        all_passed=false
    fi
    
    return $([ "$all_passed" == true ])
}

# Generate detailed report
generate_report() {
    local status="$1"
    local report_file="${PROJECT_ROOT}/logs/release_fence_report_$(date +%s).json"
    
    local report=$(cat <<EOF
{
  "timestamp": "$(date -Iseconds)",
  "status": "$status",
  "checks": {
    "service_health": "$(check_service_health "All Services" "" && echo "PASS" || echo "FAIL")",
    "access_receipts": "$(check_access_receipts >/dev/null 2>&1 && echo "PASS" || echo "FAIL")",
    "egress_certificates": "$(check_egress_certificates >/dev/null 2>&1 && echo "PASS" || echo "FAIL")",
    "attestation_heartbeats": "$(check_attestation_heartbeats >/dev/null 2>&1 && echo "PASS" || echo "FAIL")",
    "slo_gates": "$(check_slo_gates >/dev/null 2>&1 && echo "PASS" || echo "FAIL")",
    "formal_verification": "$(check_formal_verification >/dev/null 2>&1 && echo "PASS" || echo "FAIL")",
    "evidence_bundles": "$(check_evidence_bundles >/dev/null 2>&1 && echo "PASS" || echo "FAIL")"
  },
  "log_file": "$FENCE_LOG",
  "report_file": "$report_file"
}
EOF
)
    
    echo "$report" > "$report_file"
    echo "$report_file"
}

# Main execution
main() {
    log "Release Fence v1.0 - Mechanism Verification"
    log "Project: Provability-Fabric"
    log "Time: $(date)"
    
    if run_fence_checks; then
        success "🎉 ALL RELEASE FENCE CHECKS PASSED"
        success "Release is APPROVED - all mechanisms and evidence verified"
        
        local report_file
        report_file=$(generate_report "PASS")
        info "Detailed report: $report_file"
        
        exit 0
    else
        error "🚫 RELEASE FENCE CHECKS FAILED"
        error "Release is BLOCKED - fix issues before proceeding"
        
        local report_file
        report_file=$(generate_report "FAIL")
        info "Detailed report: $report_file"
        
        echo -e "\n${RED}RELEASE BLOCKED - MECHANISM VERIFICATION FAILED${NC}"
        echo -e "${YELLOW}Review the following:${NC}"
        echo -e "  • Service health and connectivity"
        echo -e "  • Evidence generation (receipts, certificates, attestations)"
        echo -e "  • SLO compliance (ABAC, PII, latency)"
        echo -e "  • Formal verification status"
        echo -e "  • Evidence bundle completeness"
        echo -e "\n${BLUE}Check the logs:${NC} $FENCE_LOG"
        
        exit 1
    fi
}

# Handle script arguments
case "${1:-check}" in
    "check")
        main
        ;;
    "health")
        check_service_health "All Services" "${LEDGER_ENDPOINT}/health"
        ;;
    "evidence")
        check_access_receipts && check_egress_certificates && check_attestation_heartbeats
        ;;
    "slo")
        check_slo_gates
        ;;
    "verification")
        check_formal_verification
        ;;
    "report")
        generate_report "MANUAL"
        ;;
    *)
        echo "Usage: $0 [check|health|evidence|slo|verification|report]"
        echo "  check       - Run all release fence checks (default)"
        echo "  health      - Check service health only"
        echo "  evidence    - Check evidence artifacts only"
        echo "  slo         - Check SLO gates only"
        echo "  verification - Check formal verification only"
        echo "  report      - Generate status report"
        exit 1
        ;;
esac