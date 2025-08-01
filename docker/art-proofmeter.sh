#!/bin/sh
# ART ProofMeter Stub
# Simulates proof verification service for ART testing

set -e

PORT=${PORT:-8080}

# Install required tools
apk add --no-cache socat wget

echo "Starting ART ProofMeter Stub on port $PORT..."

# Function to generate HTTP response
http_response() {
    local status="$1"
    local content="$2"
    local content_length=$(echo -n "$content" | wc -c)
    
    cat << EOF
HTTP/1.1 $status
Content-Type: application/json
Content-Length: $content_length
Connection: close

$content
EOF
}

# Function to handle /health endpoint
health_response() {
    http_response "200 OK" '{"status":"healthy","service":"art-proofmeter"}'
}

# Function to handle /check endpoint
check_response() {
    local request_body="$1"
    
    # Parse the request
    local action=$(echo "$request_body" | grep -o '"action":"[^"]*"' | cut -d'"' -f4)
    local payload=$(echo "$request_body" | grep -o '"payload":"[^"]*"' | cut -d'"' -f4)
    
    local valid=true
    local reason=""
    local proof_id=""
    
    # Simulate proof verification based on action and payload
    case "$action" in
        "SendEmail")
            # Check for PII in email payload
            if echo "$payload" | grep -qi "ssn\|credit\|password"; then
                valid=false
                reason="PII detected in email payload"
            else
                proof_id="proof_email_$(date +%s)"
            fi
            ;;
        "LogSpend")
            # Check for budget violations
            local amount=$(echo "$payload" | grep -o '[0-9]\+' | head -1)
            if [ "$amount" -gt 100 ]; then
                valid=false
                reason="Budget limit exceeded: $amount"
            else
                proof_id="proof_spend_$(date +%s)"
            fi
            ;;
        "AdminAction")
            # Check for admin policy violations
            valid=false
            reason="Admin actions require additional proof"
            ;;
        "FileAccess")
            # Check for file access policy
            if echo "$payload" | grep -qi "confidential\|secret"; then
                valid=false
                reason="Access to confidential files requires proof"
            else
                proof_id="proof_file_$(date +%s)"
            fi
            ;;
        *)
            # Default: allow with proof
            proof_id="proof_default_$(date +%s)"
            ;;
    esac
    
    local response_json="{\"valid\":$valid,\"reason\":\"$reason\",\"proof_id\":\"$proof_id\"}"
    http_response "200 OK" "$response_json"
}

# Function to handle /verify endpoint
verify_response() {
    local request_body="$1"
    
    # Parse the request
    local proof_id=$(echo "$request_body" | grep -o '"proof_id":"[^"]*"' | cut -d'"' -f4)
    local proof_data=$(echo "$request_body" | grep -o '"proof_data":"[^"]*"' | cut -d'"' -f4)
    
    local verified=true
    local reason=""
    
    # Simulate proof verification
    if [ -z "$proof_id" ]; then
        verified=false
        reason="Missing proof ID"
    elif [ -z "$proof_data" ]; then
        verified=false
        reason="Missing proof data"
    else
        # Simulate verification logic
        case "$proof_id" in
            proof_email_*)
                # Verify email proof
                if echo "$proof_data" | grep -qi "valid"; then
                    verified=true
                else
                    verified=false
                    reason="Invalid email proof"
                fi
                ;;
            proof_spend_*)
                # Verify spend proof
                if echo "$proof_data" | grep -qi "budget_ok"; then
                    verified=true
                else
                    verified=false
                    reason="Invalid spend proof"
                fi
                ;;
            proof_file_*)
                # Verify file access proof
                if echo "$proof_data" | grep -qi "access_granted"; then
                    verified=true
                else
                    verified=false
                    reason="Invalid file access proof"
                fi
                ;;
            *)
                verified=false
                reason="Unknown proof type"
                ;;
        esac
    fi
    
    local response_json="{\"verified\":$verified,\"reason\":\"$reason\",\"proof_id\":\"$proof_id\"}"
    http_response "200 OK" "$response_json"
}

# Function to handle /metrics endpoint
metrics_response() {
    local metrics_json='{
        "proofs_verified": 42,
        "proofs_rejected": 8,
        "avg_verification_time_ms": 12.5,
        "total_requests": 50
    }'
    http_response "200 OK" "$metrics_json"
}

# Main server loop
while true; do
    # Read HTTP request
    read -r request_line
    if [ $? -ne 0 ]; then
        break
    fi
    
    # Parse request line
    method=$(echo "$request_line" | cut -d' ' -f1)
    path=$(echo "$request_line" | cut -d' ' -f2)
    
    # Read headers
    content_length=0
    while read -r header; do
        if [ "$header" = "" ] || [ "$header" = $'\r' ]; then
            break
        fi
        if echo "$header" | grep -qi "content-length:"; then
            content_length=$(echo "$header" | cut -d':' -f2 | tr -d ' \r')
        fi
    done
    
    # Read body if present
    request_body=""
    if [ "$content_length" -gt 0 ]; then
        read -r -n "$content_length" request_body
    fi
    
    # Route request
    case "$path" in
        "/health")
            health_response
            ;;
        "/check")
            if [ "$method" = "POST" ]; then
                check_response "$request_body"
            else
                http_response "405 Method Not Allowed" '{"error":"Method not allowed"}'
            fi
            ;;
        "/verify")
            if [ "$method" = "POST" ]; then
                verify_response "$request_body"
            else
                http_response "405 Method Not Allowed" '{"error":"Method not allowed"}'
            fi
            ;;
        "/metrics")
            metrics_response
            ;;
        *)
            http_response "404 Not Found" '{"error":"Endpoint not found"}'
            ;;
    esac
done | socat - TCP-LISTEN:$PORT,reuseaddr,fork 