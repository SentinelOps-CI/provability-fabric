#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

# Zero-Downtime Upgrade Script
# Handles blue-green deployments with automatic rollback on failure

set -euo pipefail

# Configuration
PRIMARY_REGION="us-west-2"
SECONDARY_REGION="us-east-1"
DEPLOYMENT_TIMEOUT=600  # 10 minutes
HEALTH_CHECK_TIMEOUT=120  # 2 minutes
ROLLBACK_TIMEOUT=300  # 5 minutes

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

# Function to check if a command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to validate prerequisites
validate_prerequisites() {
    log_info "Validating prerequisites..."
    
    local missing_tools=()
    
    for tool in aws kubectl terraform docker; do
        if ! command_exists "$tool"; then
            missing_tools+=("$tool")
        fi
    done
    
    if [ ${#missing_tools[@]} -ne 0 ]; then
        log_error "Missing required tools: ${missing_tools[*]}"
        exit 1
    fi
    
    # Check AWS credentials
    if ! aws sts get-caller-identity >/dev/null 2>&1; then
        log_error "AWS credentials not configured"
        exit 1
    fi
    
    log_success "Prerequisites validated"
}

# Function to get current deployment status
get_deployment_status() {
    local region=$1
    local namespace=$2
    
    kubectl --context "kind-$region" get deployment -n "$namespace" -o jsonpath='{.items[*].metadata.name}' 2>/dev/null || echo ""
}

# Function to check service health
check_service_health() {
    local region=$1
    local service_url=$2
    local timeout=$3
    
    log_info "Checking service health in $region: $service_url"
    
    local start_time=$(date +%s)
    local end_time=$((start_time + timeout))
    
    while [ $(date +%s) -lt $end_time ]; do
        if curl -f -s "$service_url/health" >/dev/null 2>&1; then
            log_success "Service healthy in $region"
            return 0
        fi
        
        sleep 5
    done
    
    log_error "Service health check failed in $region"
    return 1
}

# Function to deploy to a region
deploy_to_region() {
    local region=$1
    local version=$2
    local is_primary=$3
    
    log_info "Deploying version $version to $region (primary: $is_primary)"
    
    # Set kubectl context
    export KUBECONFIG="/tmp/kubeconfig-$region"
    
    # Create namespace if it doesn't exist
    kubectl create namespace provability-fabric --dry-run=client -o yaml | kubectl apply -f -
    
    # Apply Terraform configuration
    cd ops/terraform/regions
    terraform init
    terraform apply -var="region=$region" -var="version=$version" -auto-approve
    
    # Deploy application
    kubectl apply -f ../../../runtime/admission-controller/deploy/admission/templates/
    kubectl apply -f ../../../runtime/ledger/deploy/
    
    # Wait for deployment to be ready
    kubectl rollout status deployment/ledger -n provability-fabric --timeout=${DEPLOYMENT_TIMEOUT}s
    
    # Check service health
    local service_url="http://localhost:4000"  # This would be the actual ALB URL
    if ! check_service_health "$region" "$service_url" $HEALTH_CHECK_TIMEOUT; then
        log_error "Deployment failed in $region"
        return 1
    fi
    
    log_success "Deployment completed in $region"
    return 0
}

# Function to switch traffic
switch_traffic() {
    local primary_region=$1
    local secondary_region=$2
    local direction=$3  # "to-secondary" or "to-primary"
    
    log_info "Switching traffic: $direction"
    
    if [ "$direction" = "to-secondary" ]; then
        # Update Route 53 to point to secondary
        aws route53 change-resource-record-sets \
            --hosted-zone-id "$ROUTE53_ZONE_ID" \
            --change-batch '{
                "Changes": [{
                    "Action": "UPSERT",
                    "ResourceRecordSet": {
                        "Name": "api.provability-fabric.org",
                        "Type": "A",
                        "SetIdentifier": "primary",
                        "Failover": "SECONDARY",
                        "AliasTarget": {
                            "HostedZoneId": "'"$SECONDARY_ALB_ZONE_ID"'",
                            "DNSName": "'"$SECONDARY_ALB_DNS"'",
                            "EvaluateTargetHealth": true
                        }
                    }
                }]
            }'
    else
        # Update Route 53 to point back to primary
        aws route53 change-resource-record-sets \
            --hosted-zone-id "$ROUTE53_ZONE_ID" \
            --change-batch '{
                "Changes": [{
                    "Action": "UPSERT",
                    "ResourceRecordSet": {
                        "Name": "api.provability-fabric.org",
                        "Type": "A",
                        "SetIdentifier": "primary",
                        "Failover": "PRIMARY",
                        "AliasTarget": {
                            "HostedZoneId": "'"$PRIMARY_ALB_ZONE_ID"'",
                            "DNSName": "'"$PRIMARY_ALB_DNS"'",
                            "EvaluateTargetHealth": true
                        }
                    }
                }]
            }'
    fi
    
    # Wait for DNS propagation
    log_info "Waiting for DNS propagation..."
    sleep 60
    
    log_success "Traffic switched: $direction"
}

# Function to run database migration
run_database_migration() {
    local region=$1
    local version=$2
    
    log_info "Running database migration in $region for version $version"
    
    # Get database endpoint
    local db_endpoint=$(aws rds describe-db-instances \
        --region "$region" \
        --db-instance-identifier "provability-fabric-$region" \
        --query 'DBInstances[0].Endpoint.Address' \
        --output text)
    
    # Run migration using Docker
    docker run --rm \
        -e DATABASE_URL="postgresql://pf_admin:${DB_PASSWORD}@${db_endpoint}:5432/provability_fabric" \
        provability-fabric/ledger:$version \
        npx prisma migrate deploy
    
    log_success "Database migration completed in $region"
}

# Function to rollback deployment
rollback_deployment() {
    local region=$1
    local previous_version=$2
    
    log_warning "Rolling back deployment in $region to version $previous_version"
    
    # Switch traffic back to primary if this is secondary
    if [ "$region" = "$SECONDARY_REGION" ]; then
        switch_traffic "$PRIMARY_REGION" "$SECONDARY_REGION" "to-primary"
    fi
    
    # Deploy previous version
    if ! deploy_to_region "$region" "$previous_version" "false"; then
        log_error "Rollback failed in $region"
        return 1
    fi
    
    log_success "Rollback completed in $region"
}

# Main upgrade function
perform_zero_downtime_upgrade() {
    local new_version=$1
    local previous_version=${2:-$(git describe --tags --abbrev=0)}
    
    log_info "Starting zero-downtime upgrade"
    log_info "Previous version: $previous_version"
    log_info "New version: $new_version"
    
    # Validate prerequisites
    validate_prerequisites
    
    # Store current state for rollback
    local primary_healthy=false
    local secondary_healthy=false
    
    # Check initial health
    if check_service_health "$PRIMARY_REGION" "http://localhost:4000" 30; then
        primary_healthy=true
    fi
    
    if check_service_health "$SECONDARY_REGION" "http://localhost:4000" 30; then
        secondary_healthy=true
    fi
    
    # Step 1: Deploy to secondary region first
    log_info "Step 1: Deploying to secondary region"
    if ! deploy_to_region "$SECONDARY_REGION" "$new_version" "false"; then
        log_error "Secondary deployment failed"
        exit 1
    fi
    
    # Step 2: Run database migration on secondary
    log_info "Step 2: Running database migration on secondary"
    if ! run_database_migration "$SECONDARY_REGION" "$new_version"; then
        log_error "Secondary database migration failed"
        rollback_deployment "$SECONDARY_REGION" "$previous_version"
        exit 1
    fi
    
    # Step 3: Switch traffic to secondary
    log_info "Step 3: Switching traffic to secondary"
    if ! switch_traffic "$PRIMARY_REGION" "$SECONDARY_REGION" "to-secondary"; then
        log_error "Traffic switch failed"
        rollback_deployment "$SECONDARY_REGION" "$previous_version"
        exit 1
    fi
    
    # Step 4: Deploy to primary region
    log_info "Step 4: Deploying to primary region"
    if ! deploy_to_region "$PRIMARY_REGION" "$new_version" "true"; then
        log_error "Primary deployment failed"
        log_warning "Rolling back to previous version"
        rollback_deployment "$SECONDARY_REGION" "$previous_version"
        exit 1
    fi
    
    # Step 5: Run database migration on primary
    log_info "Step 5: Running database migration on primary"
    if ! run_database_migration "$PRIMARY_REGION" "$new_version"; then
        log_error "Primary database migration failed"
        log_warning "Rolling back to previous version"
        rollback_deployment "$PRIMARY_REGION" "$previous_version"
        rollback_deployment "$SECONDARY_REGION" "$previous_version"
        exit 1
    fi
    
    # Step 6: Switch traffic back to primary
    log_info "Step 6: Switching traffic back to primary"
    if ! switch_traffic "$PRIMARY_REGION" "$SECONDARY_REGION" "to-primary"; then
        log_error "Traffic switch back to primary failed"
        log_warning "System is running on secondary region"
    fi
    
    # Step 7: Final health check
    log_info "Step 7: Final health check"
    if check_service_health "$PRIMARY_REGION" "http://localhost:4000" 60; then
        log_success "Zero-downtime upgrade completed successfully"
    else
        log_error "Final health check failed"
        exit 1
    fi
}

# Function to display usage
usage() {
    echo "Usage: $0 <new_version> [previous_version]"
    echo ""
    echo "Performs a zero-downtime upgrade of the Provability-Fabric platform"
    echo ""
    echo "Arguments:"
    echo "  new_version      The version to upgrade to"
    echo "  previous_version The version to rollback to (optional, defaults to latest tag)"
    echo ""
    echo "Environment variables:"
    echo "  ROUTE53_ZONE_ID      Route 53 hosted zone ID"
    echo "  PRIMARY_ALB_DNS      Primary ALB DNS name"
    echo "  PRIMARY_ALB_ZONE_ID  Primary ALB zone ID"
    echo "  SECONDARY_ALB_DNS    Secondary ALB DNS name"
    echo "  SECONDARY_ALB_ZONE_ID Secondary ALB zone ID"
    echo "  DB_PASSWORD          Database password"
}

# Main script
main() {
    if [ $# -lt 1 ]; then
        usage
        exit 1
    fi
    
    local new_version=$1
    local previous_version=${2:-}
    
    # Validate version format
    if [[ ! "$new_version" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
        log_error "Invalid version format. Expected format: vX.Y.Z"
        exit 1
    fi
    
    # Check required environment variables
    local required_vars=("ROUTE53_ZONE_ID" "PRIMARY_ALB_DNS" "PRIMARY_ALB_ZONE_ID" "SECONDARY_ALB_DNS" "SECONDARY_ALB_ZONE_ID" "DB_PASSWORD")
    for var in "${required_vars[@]}"; do
        if [ -z "${!var:-}" ]; then
            log_error "Required environment variable $var is not set"
            exit 1
        fi
    done
    
    # Perform the upgrade
    perform_zero_downtime_upgrade "$new_version" "$previous_version"
}

# Run main function with all arguments
main "$@"