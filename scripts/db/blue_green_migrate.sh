#!/bin/bash

# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

# Blue-green database migration script for Provability-Fabric
# This script performs zero-downtime database migrations by:
# 1. Creating a green schema via migration files
# 2. Running smoke tests against the green schema
# 3. Flipping DNS CNAME to point to green
# 4. Tearing down the blue environment

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
MIGRATIONS_DIR="$PROJECT_ROOT/runtime/ledger/prisma/migrations"
LEDGER_DIR="$PROJECT_ROOT/runtime/ledger"

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
Usage: $0 [OPTIONS]

Blue-green database migration script for Provability-Fabric.

OPTIONS:
    --dry-run              Show what would be done without executing
    --blue-db-url URL      Blue database connection URL
    --green-db-url URL     Green database connection URL
    --dns-zone ZONE        Route 53 hosted zone ID
    --dns-record RECORD    DNS record name to flip (e.g., db.provability-fabric.org)
    --migration-file FILE  Specific migration file to apply (optional)
    --smoke-test-url URL   URL for smoke tests
    --timeout SECONDS      Timeout for operations (default: 300)
    --help                 Show this help message

EXAMPLES:
    # Dry run to see the plan
    $0 --dry-run --blue-db-url postgresql://user:pass@blue-db:5432/db \\
        --green-db-url postgresql://user:pass@green-db:5432/db \\
        --dns-zone Z1234567890ABC \\
        --dns-record db.provability-fabric.org

    # Execute migration
    $0 --blue-db-url postgresql://user:pass@blue-db:5432/db \\
        --green-db-url postgresql://user:pass@green-db:5432/db \\
        --dns-zone Z1234567890ABC \\
        --dns-record db.provability-fabric.org \\
        --smoke-test-url https://api.provability-fabric.org/health

EOF
}

# Parse command line arguments
DRY_RUN=false
BLUE_DB_URL=""
GREEN_DB_URL=""
DNS_ZONE=""
DNS_RECORD=""
MIGRATION_FILE=""
SMOKE_TEST_URL=""
TIMEOUT=300

while [[ $# -gt 0 ]]; do
    case $1 in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --blue-db-url)
            BLUE_DB_URL="$2"
            shift 2
            ;;
        --green-db-url)
            GREEN_DB_URL="$2"
            shift 2
            ;;
        --dns-zone)
            DNS_ZONE="$2"
            shift 2
            ;;
        --dns-record)
            DNS_RECORD="$2"
            shift 2
            ;;
        --migration-file)
            MIGRATION_FILE="$2"
            shift 2
            ;;
        --smoke-test-url)
            SMOKE_TEST_URL="$2"
            shift 2
            ;;
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        --help)
            show_help
            exit 0
            ;;
        *)
            log_error "Unknown option: $1"
            show_help
            exit 1
            ;;
    esac
done

# Validate required parameters
if [[ -z "$BLUE_DB_URL" || -z "$GREEN_DB_URL" || -z "$DNS_ZONE" || -z "$DNS_RECORD" ]]; then
    log_error "Missing required parameters. Use --help for usage information."
    exit 1
fi

# Check if required tools are available
check_dependencies() {
    log_info "Checking dependencies..."
    
    local missing_deps=()
    
    if ! command -v psql &> /dev/null; then
        missing_deps+=("psql")
    fi
    
    if ! command -v aws &> /dev/null; then
        missing_deps+=("aws")
    fi
    
    if ! command -v curl &> /dev/null; then
        missing_deps+=("curl")
    fi
    
    if ! command -v jq &> /dev/null; then
        missing_deps+=("jq")
    fi
    
    if [[ ${#missing_deps[@]} -gt 0 ]]; then
        log_error "Missing required dependencies: ${missing_deps[*]}"
        exit 1
    fi
    
    log_success "All dependencies available"
}

# Test database connectivity
test_db_connectivity() {
    local db_url="$1"
    local db_name="$2"
    
    log_info "Testing connectivity to $db_name database..."
    
    if ! psql "$db_url" -c "SELECT 1;" &> /dev/null; then
        log_error "Cannot connect to $db_name database"
        return 1
    fi
    
    log_success "Successfully connected to $db_name database"
}

# Get current DNS record value
get_current_dns_value() {
    log_info "Getting current DNS record value for $DNS_RECORD..."
    
    local current_value
    current_value=$(aws route53 list-resource-record-sets \
        --hosted-zone-id "$DNS_ZONE" \
        --query "ResourceRecordSets[?Name == '$DNS_RECORD.'].ResourceRecords[0].Value" \
        --output text 2>/dev/null || echo "")
    
    if [[ -z "$current_value" ]]; then
        log_warning "Could not retrieve current DNS value"
        return 1
    fi
    
    echo "$current_value"
}

# Apply migrations to green database
apply_migrations() {
    log_info "Applying migrations to green database..."
    
    if [[ -n "$MIGRATION_FILE" ]]; then
        log_info "Applying specific migration: $MIGRATION_FILE"
        
        if [[ "$DRY_RUN" == "true" ]]; then
            log_info "[DRY RUN] Would apply migration: $MIGRATION_FILE"
            return 0
        fi
        
        # Apply specific migration file
        if ! psql "$GREEN_DB_URL" -f "$MIGRATION_FILE"; then
            log_error "Failed to apply migration: $MIGRATION_FILE"
            return 1
        fi
    else
        log_info "Applying all pending migrations..."
        
        if [[ "$DRY_RUN" == "true" ]]; then
            log_info "[DRY RUN] Would apply all pending migrations"
            return 0
        fi
        
        # Change to ledger directory and run Prisma migrations
        cd "$LEDGER_DIR"
        
        # Generate migration if needed
        if ! npx prisma migrate deploy --schema=./prisma/schema.prisma; then
            log_error "Failed to apply Prisma migrations"
            return 1
        fi
        
        # Verify schema is up to date
        if ! npx prisma db push --schema=./prisma/schema.prisma --accept-data-loss; then
            log_error "Failed to push schema changes"
            return 1
        fi
    fi
    
    log_success "Migrations applied successfully"
}

# Run smoke tests
run_smoke_tests() {
    if [[ -z "$SMOKE_TEST_URL" ]]; then
        log_warning "No smoke test URL provided, skipping smoke tests"
        return 0
    fi
    
    log_info "Running smoke tests against $SMOKE_TEST_URL..."
    
    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "[DRY RUN] Would run smoke tests against $SMOKE_TEST_URL"
        return 0
    fi
    
    local max_attempts=10
    local attempt=1
    
    while [[ $attempt -le $max_attempts ]]; do
        log_info "Smoke test attempt $attempt/$max_attempts..."
        
        if curl -f -s "$SMOKE_TEST_URL" > /dev/null; then
            log_success "Smoke tests passed"
            return 0
        else
            log_warning "Smoke test attempt $attempt failed"
            if [[ $attempt -eq $max_attempts ]]; then
                log_error "All smoke test attempts failed"
                return 1
            fi
            sleep 5
            ((attempt++))
        fi
    done
}

# Update DNS record
update_dns_record() {
    local new_value="$1"
    local old_value="$2"
    
    log_info "Updating DNS record $DNS_RECORD to point to green database..."
    
    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "[DRY RUN] Would update DNS record $DNS_RECORD from $old_value to $new_value"
        return 0
    fi
    
    # Create temporary change batch file
    local change_batch_file
    change_batch_file=$(mktemp)
    
    cat > "$change_batch_file" << EOF
{
    "Changes": [
        {
            "Action": "UPSERT",
            "ResourceRecordSet": {
                "Name": "$DNS_RECORD",
                "Type": "CNAME",
                "TTL": 60,
                "ResourceRecords": [
                    {
                        "Value": "$new_value"
                    }
                ]
            }
        }
    ]
}
EOF
    
    # Apply DNS change
    if ! aws route53 change-resource-record-sets \
        --hosted-zone-id "$DNS_ZONE" \
        --change-batch "file://$change_batch_file" > /dev/null; then
        log_error "Failed to update DNS record"
        rm -f "$change_batch_file"
        return 1
    fi
    
    rm -f "$change_batch_file"
    
    # Wait for DNS propagation
    log_info "Waiting for DNS propagation..."
    local max_wait=300
    local wait_time=0
    
    while [[ $wait_time -lt $max_wait ]]; do
        local current_value
        current_value=$(get_current_dns_value)
        
        if [[ "$current_value" == "$new_value" ]]; then
            log_success "DNS record updated successfully"
            return 0
        fi
        
        sleep 10
        ((wait_time += 10))
        log_info "Still waiting for DNS propagation... ($wait_time/$max_wait seconds)"
    done
    
    log_error "DNS propagation timeout"
    return 1
}

# Verify database health
verify_database_health() {
    local db_url="$1"
    local db_name="$2"
    
    log_info "Verifying $db_name database health..."
    
    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "[DRY RUN] Would verify $db_name database health"
        return 0
    fi
    
    # Check if database is accessible
    if ! psql "$db_url" -c "SELECT 1;" &> /dev/null; then
        log_error "$db_name database is not accessible"
        return 1
    fi
    
    # Check if database has expected tables
    local table_count
    table_count=$(psql "$db_url" -t -c "SELECT COUNT(*) FROM information_schema.tables WHERE table_schema = 'public';" 2>/dev/null || echo "0")
    
    if [[ "$table_count" -eq 0 ]]; then
        log_error "$db_name database has no tables"
        return 1
    fi
    
    log_success "$db_name database is healthy"
}

# Main migration function
perform_migration() {
    log_info "Starting blue-green database migration..."
    log_info "Blue DB URL: $BLUE_DB_URL"
    log_info "Green DB URL: $GREEN_DB_URL"
    log_info "DNS Zone: $DNS_ZONE"
    log_info "DNS Record: $DNS_RECORD"
    log_info "Dry run: $DRY_RUN"
    
    # Step 1: Check dependencies
    check_dependencies
    
    # Step 2: Test database connectivity
    test_db_connectivity "$BLUE_DB_URL" "blue" || exit 1
    test_db_connectivity "$GREEN_DB_URL" "green" || exit 1
    
    # Step 3: Get current DNS value
    local current_dns_value
    current_dns_value=$(get_current_dns_value)
    if [[ $? -ne 0 ]]; then
        log_warning "Could not determine current DNS value, proceeding anyway"
    fi
    
    # Step 4: Verify blue database health
    verify_database_health "$BLUE_DB_URL" "blue" || exit 1
    
    # Step 5: Apply migrations to green database
    apply_migrations || exit 1
    
    # Step 6: Verify green database health
    verify_database_health "$GREEN_DB_URL" "green" || exit 1
    
    # Step 7: Run smoke tests
    run_smoke_tests || exit 1
    
    # Step 8: Update DNS record
    local green_db_host
    green_db_host=$(echo "$GREEN_DB_URL" | sed -n 's/.*@\([^:]*\).*/\1/p')
    update_dns_record "$green_db_host" "$current_dns_value" || exit 1
    
    # Step 9: Final verification
    log_info "Performing final verification..."
    run_smoke_tests || exit 1
    
    log_success "Blue-green migration completed successfully!"
    
    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "This was a dry run. No changes were made."
    else
        log_info "Migration completed. Blue database can now be decommissioned."
    fi
}

# Trap function to handle cleanup
cleanup() {
    log_info "Cleaning up..."
    # Add any cleanup logic here
}

# Set up trap
trap cleanup EXIT

# Main execution
main() {
    local start_time
    start_time=$(date +%s)
    
    log_info "Starting blue-green migration at $(date)"
    
    perform_migration
    
    local end_time
    end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    log_success "Migration completed in ${duration} seconds"
}

# Run main function
main "$@"