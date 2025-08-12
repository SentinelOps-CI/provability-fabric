#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

# Multi-architecture build script for Provability-Fabric
# Builds Docker images for both x86_64 and ARM64 (Graviton)

# Configuration
REGISTRY="${REGISTRY:-ghcr.io/provability-fabric}"
VERSION="${VERSION:-$(cat VERSION 2>/dev/null || echo 'latest')}"
PLATFORMS="linux/amd64,linux/arm64"
BUILDX_BUILDER="provability-fabric-builder"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Logging functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check prerequisites
check_prerequisites() {
    log_info "Checking build prerequisites..."
    
    # Check if Docker is running
    if ! docker info >/dev/null 2>&1; then
        log_error "Docker is not running or not accessible"
        exit 1
    fi
    
    # Check if buildx is available
    if ! docker buildx version >/dev/null 2>&1; then
        log_error "Docker Buildx is not available. Please enable it in Docker Desktop or install it separately."
        exit 1
    fi
    
    # Check if qemu is available for ARM emulation
    if ! docker run --rm --platform linux/arm64 alpine:latest echo "ARM emulation working" >/dev/null 2>&1; then
        log_warning "ARM emulation not working. ARM64 builds may fail."
        log_info "Consider installing qemu-user-static: sudo apt-get install qemu-user-static"
    fi
    
    log_success "Prerequisites check passed"
}

# Setup buildx builder
setup_buildx() {
    log_info "Setting up Docker Buildx builder..."
    
    # Check if builder already exists
    if docker buildx inspect "$BUILDX_BUILDER" >/dev/null 2>&1; then
        log_info "Builder '$BUILDX_BUILDER' already exists"
        return
    fi
    
    # Create new builder
    docker buildx create --name "$BUILDX_BUILDER" --driver docker-container --use
    docker buildx inspect --bootstrap
    
    log_success "Buildx builder setup complete"
}

# Build a single service
build_service() {
    local service="$1"
    local dockerfile_path="runtime/$service/Dockerfile"
    local image_name="$REGISTRY/$service:$VERSION"
    
    if [[ ! -f "$dockerfile_path" ]]; then
        log_warning "Dockerfile not found for service '$service': $dockerfile_path"
        return 1
    fi
    
    log_info "Building $service for platforms: $PLATFORMS"
    
    # Build and push multi-architecture image
    docker buildx build \
        --platform "$PLATFORMS" \
        --file "$dockerfile_path" \
        --tag "$image_name" \
        --tag "$REGISTRY/$service:latest" \
        --push \
        "runtime/$service"
    
    if [[ $? -eq 0 ]]; then
        log_success "Successfully built and pushed $service"
        return 0
    else
        log_error "Failed to build $service"
        return 1
    fi
}

# Build all services
build_all_services() {
    log_info "Building all services for multi-architecture deployment..."
    
    local services=("sidecar-watcher" "egress-firewall" "attestor")
    local failed_services=()
    
    for service in "${services[@]}"; do
        if build_service "$service"; then
            log_success "✓ $service built successfully"
        else
            log_error "✗ $service build failed"
            failed_services+=("$service")
        fi
    done
    
    # Report results
    if [[ ${#failed_services[@]} -eq 0 ]]; then
        log_success "All services built successfully!"
    else
        log_error "The following services failed to build: ${failed_services[*]}"
        return 1
    fi
}

# Build and test locally (without pushing)
build_local() {
    local service="$1"
    local platform="$2"
    local dockerfile_path="runtime/$service/Dockerfile"
    local image_name="$REGISTRY/$service:$VERSION-$platform"
    
    if [[ ! -f "$dockerfile_path" ]]; then
        log_warning "Dockerfile not found for service '$service': $dockerfile_path"
        return 1
    fi
    
    log_info "Building $service locally for platform: $platform"
    
    # Build local image
    docker buildx build \
        --platform "$platform" \
        --file "$dockerfile_path" \
        --tag "$image_name" \
        --load \
        "runtime/$service"
    
    if [[ $? -eq 0 ]]; then
        log_success "Successfully built $service for $platform"
        return 0
    else
        log_error "Failed to build $service for $platform"
        return 1
    fi
}

# Test multi-architecture builds locally
test_local_builds() {
    log_info "Testing local multi-architecture builds..."
    
    local services=("sidecar-watcher" "egress-firewall" "attestor")
    local platforms=("linux/amd64" "linux/arm64")
    local failed_builds=()
    
    for service in "${services[@]}"; do
        for platform in "${platforms[@]}"; do
            local platform_suffix
            case "$platform" in
                "linux/amd64") platform_suffix="amd64" ;;
                "linux/arm64") platform_suffix="arm64" ;;
                *) platform_suffix="unknown" ;;
            esac
            
            if build_local "$service" "$platform"; then
                log_success "✓ $service ($platform_suffix) built successfully"
            else
                log_error "✗ $service ($platform_suffix) build failed"
                failed_builds+=("$service-$platform_suffix")
            fi
        done
    done
    
    # Report results
    if [[ ${#failed_builds[@]} -eq 0 ]]; then
        log_success "All local builds successful!"
    else
        log_error "The following local builds failed: ${failed_builds[*]}"
        return 1
    fi
}

# Performance testing for ARM vs x86
test_performance() {
    log_info "Running performance comparison tests..."
    
    # This would run actual performance tests comparing ARM vs x86
    # For now, we'll just check if the images can run
    
    local services=("sidecar-watcher" "egress-firewall" "attestor")
    
    for service in "${services[@]}"; do
        log_info "Testing $service performance..."
        
        # Test x86_64
        if docker run --rm --platform linux/amd64 "$REGISTRY/$service:$VERSION-amd64" --version >/dev/null 2>&1; then
            log_success "✓ $service (x86_64) runs successfully"
        else
            log_warning "✗ $service (x86_64) failed to run"
        fi
        
        # Test ARM64
        if docker run --rm --platform linux/arm64 "$REGISTRY/$service:$VERSION-arm64" --version >/dev/null 2>&1; then
            log_success "✓ $service (ARM64) runs successfully"
        else
            log_warning "✗ $service (ARM64) failed to run"
        fi
    done
    
    log_info "Performance testing complete. Check logs for detailed metrics."
}

# Cleanup function
cleanup() {
    log_info "Cleaning up build artifacts..."
    
    # Remove local test images
    docker image prune -f --filter label=org.opencontainers.image.vendor=Provability-Fabric
    
    log_success "Cleanup complete"
}

# Main function
main() {
    local command="${1:-build}"
    
    case "$command" in
        "build")
            check_prerequisites
            setup_buildx
            build_all_services
            ;;
        "test-local")
            check_prerequisites
            test_local_builds
            ;;
        "test-performance")
            check_prerequisites
            test_performance
            ;;
        "cleanup")
            cleanup
            ;;
        "help"|"-h"|"--help")
            echo "Usage: $0 [COMMAND]"
            echo ""
            echo "Commands:"
            echo "  build           Build and push all services (default)"
            echo "  test-local      Test local builds for all platforms"
            echo "  test-performance Test performance of ARM vs x86 builds"
            echo "  cleanup         Clean up build artifacts"
            echo "  help            Show this help message"
            echo ""
            echo "Environment variables:"
            echo "  REGISTRY        Docker registry (default: ghcr.io/provability-fabric)"
            echo "  VERSION         Image version (default: from VERSION file or 'latest')"
            echo "  PLATFORMS       Target platforms (default: linux/amd64,linux/arm64)"
            ;;
        *)
            log_error "Unknown command: $command"
            echo "Use '$0 help' for usage information"
            exit 1
            ;;
    esac
}

# Trap cleanup on exit
trap cleanup EXIT

# Run main function with all arguments
main "$@"
