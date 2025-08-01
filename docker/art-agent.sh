#!/bin/sh
# ART Mock LLM Agent
# Simulates an LLM agent that processes prompts and returns responses

set -e

PORT=${PORT:-3000}

# Install required tools
apk add --no-cache socat wget

# Create simple HTTP server using socat
echo "Starting ART Mock Agent on port $PORT..."

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
    http_response "200 OK" '{"status":"healthy","service":"art-agent"}'
}

# Function to handle /process endpoint
process_response() {
    local request_body="$1"
    
    # Parse the request (simplified)
    local system_prompt=$(echo "$request_body" | grep -o '"system_prompt":"[^"]*"' | cut -d'"' -f4)
    local user_prompt=$(echo "$request_body" | grep -o '"user_prompt":"[^"]*"' | cut -d'"' -f4)
    local behavior=$(echo "$request_body" | grep -o '"behavior":"[^"]*"' | cut -d'"' -f4)
    
    # Simulate different responses based on behavior
    local decision="allowed"
    local response_text=""
    
    case "$behavior" in
        "confidentiality")
            # Simulate PII detection
            if echo "$user_prompt" | grep -qi "ssn\|credit\|password\|email"; then
                decision="blocked"
                response_text="I cannot provide that information for security reasons."
            else
                response_text="Here is the information you requested."
            fi
            ;;
        "policy")
            # Simulate policy violation
            if echo "$user_prompt" | grep -qi "admin\|root\|sudo"; then
                decision="blocked"
                response_text="Access denied. Insufficient permissions."
            else
                response_text="Operation completed successfully."
            fi
            ;;
        "override")
            # Simulate safety guard bypass
            if echo "$user_prompt" | grep -qi "ignore\|bypass\|disable"; then
                decision="blocked"
                response_text="Safety guards cannot be disabled."
            else
                response_text="Request processed safely."
            fi
            ;;
        "budget")
            # Simulate budget violation
            if echo "$user_prompt" | grep -qi "expensive\|costly\|high"; then
                decision="blocked"
                response_text="Request exceeds budget limits."
            else
                response_text="Request within budget constraints."
            fi
            ;;
        *)
            # Default response
            response_text="Request processed."
            ;;
    esac
    
    local response_json="{\"decision\":\"$decision\",\"response\":\"$response_text\",\"latency_ms\":15.2}"
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
        "/process")
            if [ "$method" = "POST" ]; then
                process_response "$request_body"
            else
                http_response "405 Method Not Allowed" '{"error":"Method not allowed"}'
            fi
            ;;
        *)
            http_response "404 Not Found" '{"error":"Endpoint not found"}'
            ;;
    esac
done | socat - TCP-LISTEN:$PORT,reuseaddr,fork 