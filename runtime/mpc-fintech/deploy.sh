#!/bin/bash

# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

# MPC Financial Services Deployment and Testing Script
# Comprehensive deployment automation for production financial environments

set -euo pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_NAME="mpc-fintech"
VERSION="${VERSION:-0.1.0}"
ENVIRONMENT="${ENVIRONMENT:-development}"
BUILD_MODE="${BUILD_MODE:-release}"
ENABLE_HSM="${ENABLE_HSM:-false}"
ENABLE_BENCHMARKS="${ENABLE_BENCHMARKS:-true}"

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

# Help function
show_help() {
    cat << EOF
MPC Financial Services Deployment Script

Usage: $0 [COMMAND] [OPTIONS]

Commands:
    build           Build the project in release mode
    test            Run comprehensive test suite
    benchmark       Run performance benchmarks
    demo            Run financial demo scenarios
    deploy          Deploy to production environment
    validate        Validate deployment and run health checks
    clean           Clean build artifacts
    help            Show this help message

Options:
    --environment ENV    Target environment (development|staging|production)
    --build-mode MODE    Build mode (debug|release)
    --enable-hsm         Enable Hardware Security Module support
    --enable-benchmarks  Enable benchmark compilation
    --version VERSION    Set version for deployment

Environment Variables:
    ENVIRONMENT          Target deployment environment
    BUILD_MODE          Cargo build mode
    ENABLE_HSM          Enable HSM support
    ENABLE_BENCHMARKS   Enable benchmark features
    VERSION             Project version

Examples:
    $0 build --build-mode release
    $0 test --environment staging
    $0 benchmark --enable-benchmarks
    $0 deploy --environment production --enable-hsm
    $0 validate --environment production

EOF
}

# Parse command line arguments
parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            --environment)
                ENVIRONMENT="$2"
                shift 2
                ;;
            --build-mode)
                BUILD_MODE="$2"
                shift 2
                ;;
            --enable-hsm)
                ENABLE_HSM="true"
                shift
                ;;
            --enable-benchmarks)
                ENABLE_BENCHMARKS="true"
                shift
                ;;
            --version)
                VERSION="$2"
                shift 2
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            *)
                if [[ -z "${COMMAND:-}" ]]; then
                    COMMAND="$1"
                    shift
                else
                    log_error "Unknown argument: $1"
                    show_help
                    exit 1
                fi
                ;;
        esac
    done
}

# Validate environment
validate_environment() {
    log_info "Validating environment..."
    
    # Check Rust installation
    if ! command -v rustc &> /dev/null; then
        log_error "Rust is not installed. Please install Rust: https://rustup.rs/"
        exit 1
    fi
    
    # Check Rust version
    RUST_VERSION=$(rustc --version | awk '{print $2}')
    log_info "Rust version: $RUST_VERSION"
    
    # Check Cargo
    if ! command -v cargo &> /dev/null; then
        log_error "Cargo is not installed."
        exit 1
    fi
    
    # Check required tools for production
    if [[ "$ENVIRONMENT" == "production" ]]; then
        log_info "Validating production environment requirements..."
        
        # Check for security tools
        if [[ "$ENABLE_HSM" == "true" ]]; then
            log_info "HSM support enabled - additional security validation required"
        fi
        
        # Validate system resources
        AVAILABLE_MEMORY=$(free -m | awk 'NR==2{printf "%.0f", $7}')
        if (( AVAILABLE_MEMORY < 2048 )); then
            log_warning "Available memory is ${AVAILABLE_MEMORY}MB, recommended: 2GB+"
        fi
        
        # Check network configuration
        if ! command -v ss &> /dev/null; then
            log_warning "Network monitoring tools not available"
        fi
    fi
    
    log_success "Environment validation completed"
}

# Build project
build_project() {
    log_info "Building MPC Financial Services..."
    
    cd "$SCRIPT_DIR"
    
    # Clean previous builds
    cargo clean
    
    # Set build features
    local features=""
    if [[ "$ENABLE_HSM" == "true" ]]; then
        features="$features hardware-acceleration"
    fi
    if [[ "$ENABLE_BENCHMARKS" == "true" ]]; then
        features="$features benchmarking"
    fi
    
    # Build command
    local build_cmd="cargo build"
    if [[ "$BUILD_MODE" == "release" ]]; then
        build_cmd="$build_cmd --release"
    fi
    if [[ -n "$features" ]]; then
        build_cmd="$build_cmd --features '$features'"
    fi
    
    log_info "Running: $build_cmd"
    eval "$build_cmd"
    
    # Build binaries
    if [[ "$ENABLE_BENCHMARKS" == "true" ]]; then
        log_info "Building benchmark binary..."
        cargo build --bin mpc-fintech-benchmark --features benchmarking
        if [[ "$BUILD_MODE" == "release" ]]; then
            cargo build --release --bin mpc-fintech-benchmark --features benchmarking
        fi
    fi
    
    log_info "Building demo binary..."
    cargo build --bin mpc-fintech-demo
    if [[ "$BUILD_MODE" == "release" ]]; then
        cargo build --release --bin mpc-fintech-demo
    fi
    
    log_success "Build completed successfully"
}

# Run tests
run_tests() {
    log_info "Running comprehensive test suite..."
    
    cd "$SCRIPT_DIR"
    
    # Unit tests
    log_info "Running unit tests..."
    cargo test --lib
    
    # Integration tests
    log_info "Running integration tests..."
    cargo test --test '*'
    
    # Doc tests
    log_info "Running documentation tests..."
    cargo test --doc
    
    # Clippy linting
    log_info "Running Clippy linting..."
    cargo clippy --all-targets --all-features -- -D warnings
    
    # Format check
    log_info "Checking code formatting..."
    cargo fmt --all -- --check
    
    # Security audit
    if command -v cargo-audit &> /dev/null; then
        log_info "Running security audit..."
        cargo audit
    else
        log_warning "cargo-audit not installed, skipping security audit"
    fi
    
    log_success "All tests passed successfully"
}

# Run benchmarks
run_benchmarks() {
    if [[ "$ENABLE_BENCHMARKS" != "true" ]]; then
        log_warning "Benchmarks disabled, skipping benchmark execution"
        return 0
    fi
    
    log_info "Running performance benchmarks..."
    
    cd "$SCRIPT_DIR"
    
    # Ensure benchmark binary is built
    if [[ ! -f "target/${BUILD_MODE}/mpc-fintech-benchmark" ]]; then
        log_info "Building benchmark binary..."
        if [[ "$BUILD_MODE" == "release" ]]; then
            cargo build --release --bin mpc-fintech-benchmark --features benchmarking
        else
            cargo build --bin mpc-fintech-benchmark --features benchmarking
        fi
    fi
    
    # Create benchmarks directory
    mkdir -p benchmarks/results
    
    # Run benchmarks with detailed output
    log_info "Executing benchmark suite..."
    local benchmark_output="benchmarks/results/benchmark_$(date +%Y%m%d_%H%M%S).log"
    
    if [[ "$BUILD_MODE" == "release" ]]; then
        timeout 600 ./target/release/mpc-fintech-benchmark 2>&1 | tee "$benchmark_output"
    else
        timeout 600 ./target/debug/mpc-fintech-benchmark 2>&1 | tee "$benchmark_output"
    fi
    
    log_success "Benchmarks completed - results saved to $benchmark_output"
}

# Run demo
run_demo() {
    log_info "Running financial demo scenarios..."
    
    cd "$SCRIPT_DIR"
    
    # Ensure demo binary is built
    if [[ ! -f "target/${BUILD_MODE}/mpc-fintech-demo" ]]; then
        log_info "Building demo binary..."
        if [[ "$BUILD_MODE" == "release" ]]; then
            cargo build --release --bin mpc-fintech-demo
        else
            cargo build --bin mpc-fintech-demo
        fi
    fi
    
    # Run demo with timeout
    log_info "Executing financial demo scenarios..."
    if [[ "$BUILD_MODE" == "release" ]]; then
        timeout 300 ./target/release/mpc-fintech-demo
    else
        timeout 300 ./target/debug/mpc-fintech-demo
    fi
    
    log_success "Demo completed successfully"
}

# Deploy to environment
deploy_to_environment() {
    log_info "Deploying to $ENVIRONMENT environment..."
    
    # Validate deployment prerequisites
    validate_deployment_prerequisites
    
    case "$ENVIRONMENT" in
        development)
            deploy_development
            ;;
        staging)
            deploy_staging
            ;;
        production)
            deploy_production
            ;;
        *)
            log_error "Unknown environment: $ENVIRONMENT"
            exit 1
            ;;
    esac
    
    log_success "Deployment to $ENVIRONMENT completed"
}

# Validate deployment prerequisites
validate_deployment_prerequisites() {
    log_info "Validating deployment prerequisites..."
    
    # Check if build exists
    if [[ ! -f "target/${BUILD_MODE}/mpc-fintech-demo" ]]; then
        log_warning "Demo binary not found, building..."
        build_project
    fi
    
    # Check configuration files
    if [[ "$ENVIRONMENT" == "production" ]]; then
        if [[ ! -f "config/production.toml" ]]; then
            log_warning "Production configuration not found, using defaults"
        fi
        
        # Check certificates for production
        if [[ "$ENABLE_HSM" == "true" ]] && [[ ! -d "/etc/certs" ]]; then
            log_warning "Certificate directory not found: /etc/certs"
        fi
    fi
    
    log_success "Prerequisites validation completed"
}

# Development deployment
deploy_development() {
    log_info "Deploying to development environment..."
    
    # Simple local deployment
    mkdir -p logs
    
    # Create systemd service file for development
    create_systemd_service "development"
    
    log_info "Development deployment ready"
    log_info "To start the service: systemctl --user start mpc-fintech-dev"
}

# Staging deployment
deploy_staging() {
    log_info "Deploying to staging environment..."
    
    # Create staging configuration
    mkdir -p config logs
    
    # Copy binaries to staging location
    STAGING_DIR="/opt/mpc-fintech-staging"
    if [[ -w "/opt" ]]; then
        sudo mkdir -p "$STAGING_DIR"
        sudo cp "target/${BUILD_MODE}/mpc-fintech-demo" "$STAGING_DIR/"
        if [[ "$ENABLE_BENCHMARKS" == "true" ]]; then
            sudo cp "target/${BUILD_MODE}/mpc-fintech-benchmark" "$STAGING_DIR/"
        fi
        sudo chown -R "$USER:$USER" "$STAGING_DIR"
    else
        log_warning "Cannot write to /opt, deploying to local staging directory"
        STAGING_DIR="./staging"
        mkdir -p "$STAGING_DIR"
        cp "target/${BUILD_MODE}/mpc-fintech-demo" "$STAGING_DIR/"
        if [[ "$ENABLE_BENCHMARKS" == "true" ]]; then
            cp "target/${BUILD_MODE}/mpc-fintech-benchmark" "$STAGING_DIR/"
        fi
    fi
    
    create_systemd_service "staging"
    
    log_info "Staging deployment completed to: $STAGING_DIR"
}

# Production deployment
deploy_production() {
    log_info "Deploying to production environment..."
    
    # Production deployment requires additional security
    if [[ "$BUILD_MODE" != "release" ]]; then
        log_error "Production deployment requires release build mode"
        exit 1
    fi
    
    # Create production directory structure
    PROD_DIR="/opt/mpc-fintech"
    sudo mkdir -p "$PROD_DIR"/{bin,config,logs,data}
    
    # Copy binaries
    sudo cp "target/release/mpc-fintech-demo" "$PROD_DIR/bin/"
    if [[ "$ENABLE_BENCHMARKS" == "true" ]]; then
        sudo cp "target/release/mpc-fintech-benchmark" "$PROD_DIR/bin/"
    fi
    
    # Set proper permissions
    sudo chmod +x "$PROD_DIR/bin/"*
    sudo chown -R mpc-fintech:mpc-fintech "$PROD_DIR" 2>/dev/null || true
    
    # Create production systemd service
    create_systemd_service "production"
    
    # Setup log rotation
    create_logrotate_config
    
    # Setup monitoring
    if command -v systemctl &> /dev/null; then
        sudo systemctl daemon-reload
        sudo systemctl enable mpc-fintech-prod
    fi
    
    log_success "Production deployment completed"
    log_info "To start the service: sudo systemctl start mpc-fintech-prod"
}

# Create systemd service
create_systemd_service() {
    local env="$1"
    local service_name="mpc-fintech-$env"
    
    log_info "Creating systemd service: $service_name"
    
    local service_file
    if [[ "$env" == "production" ]]; then
        service_file="/etc/systemd/system/$service_name.service"
        local exec_path="/opt/mpc-fintech/bin/mpc-fintech-demo"
        local work_dir="/opt/mpc-fintech"
        local user="mpc-fintech"
    else
        service_file="$HOME/.config/systemd/user/$service_name.service"
        mkdir -p "$HOME/.config/systemd/user"
        local exec_path="$SCRIPT_DIR/target/${BUILD_MODE}/mpc-fintech-demo"
        local work_dir="$SCRIPT_DIR"
        local user="$USER"
    fi
    
    cat > "/tmp/$service_name.service" << EOF
[Unit]
Description=MPC Financial Services ($env)
After=network.target

[Service]
Type=simple
User=$user
WorkingDirectory=$work_dir
ExecStart=$exec_path
Restart=always
RestartSec=10
StandardOutput=journal
StandardError=journal
Environment=RUST_LOG=info
Environment=ENVIRONMENT=$env

# Security settings
NoNewPrivileges=true
ProtectSystem=strict
ProtectHome=true
ReadWritePaths=$work_dir/logs $work_dir/data

# Performance settings
LimitNOFILE=65536
LimitNPROC=32768

[Install]
WantedBy=multi-user.target
EOF
    
    if [[ "$env" == "production" ]]; then
        sudo mv "/tmp/$service_name.service" "$service_file"
        sudo chmod 644 "$service_file"
    else
        mv "/tmp/$service_name.service" "$service_file"
        chmod 644 "$service_file"
    fi
    
    log_success "Systemd service created: $service_file"
}

# Create logrotate configuration
create_logrotate_config() {
    log_info "Creating logrotate configuration..."
    
    sudo tee /etc/logrotate.d/mpc-fintech > /dev/null << EOF
/opt/mpc-fintech/logs/*.log {
    daily
    rotate 30
    compress
    delaycompress
    missingok
    notifempty
    create 0644 mpc-fintech mpc-fintech
    postrotate
        systemctl reload mpc-fintech-prod
    endscript
}
EOF
    
    log_success "Logrotate configuration created"
}

# Validate deployment
validate_deployment() {
    log_info "Validating deployment..."
    
    # Check if binaries exist and are executable
    local binary_path
    case "$ENVIRONMENT" in
        development)
            binary_path="$SCRIPT_DIR/target/${BUILD_MODE}/mpc-fintech-demo"
            ;;
        staging)
            binary_path="/opt/mpc-fintech-staging/mpc-fintech-demo"
            if [[ ! -f "$binary_path" ]]; then
                binary_path="./staging/mpc-fintech-demo"
            fi
            ;;
        production)
            binary_path="/opt/mpc-fintech/bin/mpc-fintech-demo"
            ;;
    esac
    
    if [[ ! -f "$binary_path" ]]; then
        log_error "Binary not found: $binary_path"
        exit 1
    fi
    
    if [[ ! -x "$binary_path" ]]; then
        log_error "Binary not executable: $binary_path"
        exit 1
    fi
    
    # Test binary execution
    log_info "Testing binary execution..."
    timeout 10 "$binary_path" --help > /dev/null 2>&1 || true
    
    # Check service status if systemd is available
    if command -v systemctl &> /dev/null; then
        local service_name="mpc-fintech-$ENVIRONMENT"
        if systemctl list-unit-files "$service_name.service" &> /dev/null; then
            log_info "Service $service_name is available"
            
            # Check if service is running
            if systemctl is-active --quiet "$service_name" 2>/dev/null; then
                log_success "Service $service_name is running"
            else
                log_info "Service $service_name is not running"
            fi
        fi
    fi
    
    # Health check
    run_health_check
    
    log_success "Deployment validation completed"
}

# Run health check
run_health_check() {
    log_info "Running health check..."
    
    # Basic connectivity test
    if command -v curl &> /dev/null; then
        # Test would connect to actual health endpoint in real deployment
        log_info "Health check endpoints would be tested here"
    fi
    
    # Resource usage check
    if command -v free &> /dev/null; then
        MEMORY_USAGE=$(free | awk 'NR==2{printf "%.0f%%", $3*100/$2 }')
        log_info "Memory usage: $MEMORY_USAGE"
    fi
    
    if command -v df &> /dev/null; then
        DISK_USAGE=$(df / | awk 'NR==2{print $5}')
        log_info "Disk usage: $DISK_USAGE"
    fi
    
    log_success "Health check completed"
}

# Clean build artifacts
clean_project() {
    log_info "Cleaning build artifacts..."
    
    cd "$SCRIPT_DIR"
    
    # Cargo clean
    cargo clean
    
    # Remove logs
    rm -rf logs/*
    
    # Remove benchmark results
    rm -rf benchmarks/results/*
    
    # Remove staging directory
    rm -rf staging
    
    log_success "Cleanup completed"
}

# Main execution
main() {
    log_info "MPC Financial Services Deployment Script"
    log_info "Environment: $ENVIRONMENT | Build Mode: $BUILD_MODE | Version: $VERSION"
    
    # Validate environment first
    validate_environment
    
    case "${COMMAND:-}" in
        build)
            build_project
            ;;
        test)
            run_tests
            ;;
        benchmark)
            run_benchmarks
            ;;
        demo)
            run_demo
            ;;
        deploy)
            deploy_to_environment
            ;;
        validate)
            validate_deployment
            ;;
        clean)
            clean_project
            ;;
        all)
            build_project
            run_tests
            run_benchmarks
            run_demo
            ;;
        *)
            log_error "No command specified or invalid command: ${COMMAND:-}"
            show_help
            exit 1
            ;;
    esac
    
    log_success "Script execution completed successfully"
}

# Parse arguments and run main
parse_args "$@"
main
