#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

# Configuration
REPO_URL="https://github.com/provability-fabric/provability-fabric"
BUILD_ID="${GITHUB_RUN_ID:-$(date +%s)}"
BUILDER_ID="github.com/provability-fabric/provability-fabric/actions/runs/${BUILD_ID}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check prerequisites
check_prerequisites() {
    log_info "Checking prerequisites..."
    
    if ! command -v cosign &> /dev/null; then
        log_error "cosign is not installed"
        exit 1
    fi
    
    if ! command -v gitsign &> /dev/null; then
        log_error "gitsign is not installed"
        exit 1
    fi
    
    if ! command -v docker &> /dev/null; then
        log_error "docker is not installed"
        exit 1
    fi
    
    log_info "All prerequisites satisfied"
}

# Generate provenance for a single image
generate_provenance() {
    local image_name="$1"
    local image_tag="$2"
    local full_image="${image_name}:${image_tag}"
    local provenance_file="${image_name}_provenance.intoto.jsonl"
    
    log_info "Generating provenance for ${full_image}"
    
    # Create SLSA v1 provenance
    cosign attest \
        --predicate-type https://slsa.dev/provenance/v1 \
        --type slsaprovenance \
        --key <(gitsign generate-key-pair --output-key-file /dev/stdout) \
        --output-file "${provenance_file}" \
        "${full_image}"
    
    if [ $? -eq 0 ]; then
        log_info "✅ Provenance generated: ${provenance_file}"
        
        # Verify the provenance
        if cosign verify-attestation --key <(gitsign generate-key-pair --output-key-file /dev/stdout) "${full_image}"; then
            log_info "✅ Provenance verification passed"
        else
            log_error "❌ Provenance verification failed"
            exit 1
        fi
    else
        log_error "❌ Failed to generate provenance for ${full_image}"
        exit 1
    fi
}

# Generate provenance for all images
generate_all_provenance() {
    log_info "Generating provenance for all images..."
    
    # List of images to generate provenance for
    local images=(
        "provability-fabric/sidecar-watcher:latest"
        "provability-fabric/admission-controller:latest"
        "provability-fabric/ledger:latest"
        "provability-fabric/attestor:latest"
    )
    
    for image in "${images[@]}"; do
        # Extract image name and tag
        local image_name=$(echo "$image" | cut -d: -f1)
        local image_tag=$(echo "$image" | cut -d: -f2)
        
        # Check if image exists locally
        if docker image inspect "$image" &> /dev/null; then
            generate_provenance "$image_name" "$image_tag"
        else
            log_warn "Image ${image} not found locally, skipping"
        fi
    done
}

# Upload provenance to GitHub release
upload_to_release() {
    if [ -n "${GITHUB_TOKEN:-}" ] && [ -n "${GITHUB_REPOSITORY:-}" ]; then
        log_info "Uploading provenance files to GitHub release..."
        
        # Get the latest release
        local release_id=$(gh api repos/${GITHUB_REPOSITORY}/releases/latest --jq .id)
        
        if [ -n "$release_id" ]; then
            for provenance_file in *_provenance.intoto.jsonl; do
                if [ -f "$provenance_file" ]; then
                    gh release upload "$release_id" "$provenance_file" --clobber
                    log_info "✅ Uploaded ${provenance_file} to release"
                fi
            done
        else
            log_warn "No release found, skipping upload"
        fi
    else
        log_warn "GitHub token or repository not set, skipping upload"
    fi
}

# Verify provenance from Rekor log
verify_provenance() {
    log_info "Verifying provenance from Rekor log..."
    
    for provenance_file in *_provenance.intoto.jsonl; do
        if [ -f "$provenance_file" ]; then
            log_info "Verifying ${provenance_file}..."
            
            if cosign verify-attestation --type slsaprovenance "$provenance_file"; then
                log_info "✅ ${provenance_file} verified from Rekor log"
            else
                log_error "❌ Failed to verify ${provenance_file} from Rekor log"
                exit 1
            fi
        fi
    done
}

# Main function
main() {
    local command="${1:-generate}"
    
    case "$command" in
        "generate")
            check_prerequisites
            generate_all_provenance
            upload_to_release
            ;;
        "verify")
            verify_provenance
            ;;
        "help")
            echo "Usage: $0 [generate|verify|help]"
            echo "  generate: Generate SLSA v1 provenance for all images"
            echo "  verify:   Verify provenance from Rekor log"
            echo "  help:     Show this help message"
            ;;
        *)
            log_error "Unknown command: $command"
            echo "Use '$0 help' for usage information"
            exit 1
            ;;
    esac
}

# Run main function with all arguments
main "$@"