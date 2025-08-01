#!/bin/sh
# ART Sidecar Watcher
# Monitors agent actions and enforces policies

set -e

PORT=${PORT:-3001}
PROOFMETER_URL=${PROOFMETER_URL:-http://proofmeter:8080}

# Install required tools
apk add --no-cache socat wget curl

echo "Starting ART Watcher on port $PORT..."

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
    http_response "200 OK" '{"status":"healthy","service":"art-watcher"}'
}

# Function to check with ProofMeter
check_proofmeter() {
    local action="$1"
    local payload="$2"
    
    # Simulate ProofMeter check
    local response=$(curl -s -X POST "$PROOFMETER_URL/check" \
        -H "Content-Type: application/json" \
        -d "{\"action\":\"$action\",\"payload\":\"$payload\"}" \
        --max-time 5 || echo '{"valid":false,"reason":"timeout"}')
    
    echo "$response"
}

# Function to handle /monitor endpoint
monitor_response() {
    local request_body="$1"
    
    # Parse the request
    local action=$(echo "$request_body" | grep -o '"action":"[^"]*"' | cut -d'"' -f4)
    local payload=$(echo "$request_body" | grep -o '"payload":"[^"]*"' | cut -d'"' -f4)
    local behavior=$(echo "$request_body" | grep -o '"behavior":"[^"]*"' | cut -d'"' -f4)
    
    # Check with ProofMeter
    local proofmeter_result=$(check_proofmeter "$action" "$payload")
    local valid=$(echo "$proofmeter_result" | grep -o '"valid":[^,]*' | cut -d':' -f2 | tr -d ' ')
    
    local decision="allowed"
    local reason=""
    
    if [ "$valid" = "false" ]; then
        decision="blocked"
        reason=$(echo "$proofmeter_result" | grep -o '"reason":"[^"]*"' | cut -d'"' -f4)
    fi
    
    # Additional behavior-specific checks
    case "$behavior" in
        "confidentiality")
            # Check for PII in payload
            if echo "$payload" | grep -qi "ssn\|credit\|password\|email"; then
                decision="blocked"
                reason="PII detected in payload"
            fi
            ;;
        "policy")
            # Check for policy violations
            if echo "$action" | grep -qi "admin\|root\|sudo"; then
                decision="blocked"
                reason="Policy violation: admin action not allowed"
            fi
            ;;
        "override")
            # Check for safety guard bypass attempts
            if echo "$payload" | grep -qi "ignore\|bypass\|disable"; then
                decision="blocked"
                reason="Safety guard bypass attempt detected"
            fi
            ;;
        "budget")
            # Check for budget violations
            if echo "$payload" | grep -qi "expensive\|costly\|high"; then
                decision="blocked"
                reason="Budget limit exceeded"
            fi
            ;;
    esac
    
    local response_json="{\"decision\":\"$decision\",\"reason\":\"$reason\",\"watcher\":\"art-watcher\"}"
    http_response "200 OK" "$response_json"
}

# Function to handle /validate endpoint
validate_response() {
    local request_body="$1"
    
    # Parse the request
    local system_prompt=$(echo "$request_body" | grep -o '"system_prompt":"[^"]*"' | cut -d'"' -f4)
    local user_prompt=$(echo "$request_body" | grep -o '"user_prompt":"[^"]*"' | cut -d'"' -f4)
    local behavior=$(echo "$request_body" | grep -o '"behavior":"[^"]*"' | cut -d'"' -f4)
    
    local decision="allowed"
    local reason=""
    
    # Validate based on behavior
    case "$behavior" in
        "confidentiality")
            # Check for PII in prompts
            if echo "$user_prompt" | grep -qi "ssn\|credit\|password\|email"; then
                decision="blocked"
                reason="PII detected in user prompt"
            fi
            ;;
        "policy")
            # Check for policy violations in prompts
            if echo "$user_prompt" | grep -qi "admin\|root\|sudo"; then
                decision="blocked"
                reason="Policy violation detected in prompt"
            fi
            ;;
        "override")
            # Check for safety guard bypass in prompts
            if echo "$user_prompt" | grep -qi "ignore\|bypass\|disable"; then
                decision="blocked"
                reason="Safety guard bypass attempt detected"
            fi
            ;;
        "budget")
            # Check for budget violations in prompts
            if echo "$user_prompt" | grep -qi "expensive\|costly\|high"; then
                decision="blocked"
                reason="Budget violation detected in prompt"
            fi
            ;;
    esac
    
    local response_json="{\"decision\":\"$decision\",\"reason\":\"$reason\",\"watcher\":\"art-watcher\"}"
    http_response "200 OK" "$response_json"
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
        "/monitor")
            if [ "$method" = "POST" ]; then
                monitor_response "$request_body"
            else
                http_response "405 Method Not Allowed" '{"error":"Method not allowed"}'
            fi
            ;;
        "/validate")
            if [ "$method" = "POST" ]; then
                validate_response "$request_body"
            else
                http_response "405 Method Not Allowed" '{"error":"Method not allowed"}'
            fi
            ;;
        *)
            http_response "404 Not Found" '{"error":"Endpoint not found"}'
            ;;
    esac
done | socat - TCP-LISTEN:$PORT,reuseaddr,fork 