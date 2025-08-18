#!/bin/bash

# Provability Fabric Bundle Signing Script
# This script signs bundles with DSSE, cosign, and includes them in Rekor

set -euo pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
COSIGN_KEY_PATH="${COSIGN_KEY_PATH:-$PROJECT_ROOT/keys/cosign.key}"
REKOR_URL="${REKOR_URL:-https://rekor.sigstore.dev}"
BUNDLE_PATH="${1:-}"
OUTPUT_PATH="${2:-}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Logging functions
log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check dependencies
check_dependencies() {
    log_info "Checking dependencies..."
    
    if ! command -v cosign &> /dev/null; then
        log_error "cosign is not installed. Please install it first."
        exit 1
    fi
    
    if ! command -v jq &> /dev/null; then
        log_error "jq is not installed. Please install it first."
        exit 1
    fi
    
    if ! command -v sha256sum &> /dev/null; then
        log_error "sha256sum is not installed. Please install it first."
        exit 1
    fi
    
    log_info "All dependencies are available"
}

# Validate bundle
validate_bundle() {
    local bundle_path="$1"
    
    if [[ ! -f "$bundle_path" ]]; then
        log_error "Bundle file not found: $bundle_path"
        exit 1
    fi
    
    if [[ ! -f "$bundle_path/spec.yaml" ]]; then
        log_error "Bundle spec.yaml not found: $bundle_path/spec.yaml"
        exit 1
    fi
    
    if [[ ! -f "$bundle_path/spec.md" ]]; then
        log_error "Bundle spec.md not found: $bundle_path/spec.md"
        exit 1
    fi
    
    log_info "Bundle validation passed"
}

# Generate bundle hash
generate_bundle_hash() {
    local bundle_path="$1"
    local hash_file="$bundle_path/bundle.sha256"
    
    log_info "Generating bundle hash..."
    
    # Create a temporary file with sorted file list
    local temp_file=$(mktemp)
    find "$bundle_path" -type f -name "*.yaml" -o -name "*.md" -o -name "*.lean" | sort > "$temp_file"
    
    # Generate hash of all files
    while IFS= read -r file; do
        if [[ -f "$file" ]]; then
            sha256sum "$file" >> "$hash_file"
        fi
    done < "$temp_file"
    
    # Generate final bundle hash
    local bundle_hash=$(sha256sum "$hash_file" | cut -d' ' -f1)
    echo "$bundle_hash" > "$bundle_path/bundle.hash"
    
    rm "$temp_file"
    log_info "Bundle hash generated: $bundle_hash"
    echo "$bundle_hash"
}

# Sign bundle with cosign
sign_bundle() {
    local bundle_path="$1"
    local bundle_hash="$2"
    
    log_info "Signing bundle with cosign..."
    
    # Create DSSE envelope
    local envelope_file="$bundle_path/bundle.dsse"
    cat > "$envelope_file" << EOF
{
  "payloadType": "application/vnd.in-toto+json",
  "payload": "$bundle_hash",
  "signatures": []
}
EOF
    
    # Sign with cosign
    if [[ -f "$COSIGN_KEY_PATH" ]]; then
        cosign sign-blob --key "$COSIGN_KEY_PATH" "$envelope_file" > "$bundle_path/bundle.cosign"
        log_info "Bundle signed with cosign key"
    else
        log_warn "Cosign key not found, using keyless signing"
        cosign sign-blob --keyless "$envelope_file" > "$bundle_path/bundle.cosign"
        log_info "Bundle signed with keyless cosign"
    fi
    
    # Include in Rekor
    log_info "Including bundle in Rekor..."
    cosign upload --rekor-url "$REKOR_URL" "$bundle_path/bundle.cosign"
    log_info "Bundle included in Rekor"
}

# Generate proof metadata
generate_proof_metadata() {
    local bundle_path="$1"
    local bundle_hash="$2"
    
    log_info "Generating proof metadata..."
    
    # Create proof metadata
    local proof_file="$bundle_path/proof.json"
    cat > "$proof_file" << EOF
{
  "bundle_hash": "$bundle_hash",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "signer": "$(cosign version | head -n1)",
  "rekor_url": "$REKOR_URL",
  "proof_type": "cosign_dsse_rekor",
  "verification_command": "cosign verify-blob --rekor-url $REKOR_URL --signature $bundle_path/bundle.cosign $bundle_path/bundle.hash"
}
EOF
    
    log_info "Proof metadata generated"
}

# Verify bundle signature
verify_bundle() {
    local bundle_path="$1"
    
    log_info "Verifying bundle signature..."
    
    if [[ -f "$bundle_path/bundle.cosign" ]] && [[ -f "$bundle_path/bundle.hash" ]]; then
        if cosign verify-blob --rekor-url "$REKOR_URL" --signature "$bundle_path/bundle.cosign" "$bundle_path/bundle.hash"; then
            log_info "Bundle signature verification passed"
        else
            log_error "Bundle signature verification failed"
            exit 1
        fi
    else
        log_error "Bundle signature files not found"
        exit 1
    fi
}

# Main function
main() {
    if [[ $# -lt 1 ]]; then
        echo "Usage: $0 <bundle_path> [output_path]"
        echo "  bundle_path: Path to the bundle directory"
        echo "  output_path: Optional output path for signed bundle"
        exit 1
    fi
    
    local bundle_path="$1"
    local output_path="${2:-$bundle_path}"
    
    log_info "Starting bundle signing process..."
    log_info "Bundle path: $bundle_path"
    log_info "Output path: $output_path"
    
    # Check dependencies
    check_dependencies
    
    # Validate bundle
    validate_bundle "$bundle_path"
    
    # Generate bundle hash
    local bundle_hash=$(generate_bundle_hash "$bundle_path")
    
    # Sign bundle
    sign_bundle "$bundle_path" "$bundle_hash"
    
    # Generate proof metadata
    generate_proof_metadata "$bundle_path" "$bundle_hash"
    
    # Verify bundle
    verify_bundle "$bundle_path"
    
    # Copy to output if different
    if [[ "$bundle_path" != "$output_path" ]]; then
        log_info "Copying signed bundle to output path..."
        cp -r "$bundle_path" "$output_path"
    fi
    
    log_info "Bundle signing completed successfully!"
    log_info "Signed bundle location: $output_path"
    log_info "Bundle hash: $bundle_hash"
}

# Run main function
main "$@"
