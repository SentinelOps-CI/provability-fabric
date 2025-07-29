#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

# Usage: ./adapter.sh model.sim config.json out_polytope.json

if [ $# -ne 3 ]; then
    echo "Usage: $0 <model.sim> <config.json> <out_polytope.json>"
    exit 1
fi

MODEL_SIM="$1"
CONFIG_JSON="$2"
OUTPUT_JSON="$3"

# Validate input files exist
if [ ! -f "$MODEL_SIM" ]; then
    echo "Error: Model file '$MODEL_SIM' not found"
    exit 1
fi

if [ ! -f "$CONFIG_JSON" ]; then
    echo "Error: Config file '$CONFIG_JSON' not found"
    exit 1
fi

# Create temporary directory for DryVR output
TEMP_DIR=$(mktemp -d)
trap 'rm -rf "$TEMP_DIR"' EXIT

echo "Running DryVR verification..."

# Run DryVR docker container
docker run --rm \
    -v "$(realpath "$MODEL_SIM"):/input/model.sim" \
    -v "$(realpath "$CONFIG_JSON"):/input/config.json" \
    -v "$TEMP_DIR:/output" \
    dryvr:2.0rc \
    dryvr /input/model.sim /input/config.json /output

# Check if DryVR succeeded
if [ $? -ne 0 ]; then
    echo "Error: DryVR execution failed"
    exit 1
fi

# Look for DryVR output files
DRYVR_OUTPUT=""
for file in "$TEMP_DIR"/*; do
    if [ -f "$file" ] && [[ "$file" == *.txt || "$file" == *.out ]]; then
        DRYVR_OUTPUT="$file"
        break
    fi
done

if [ -z "$DRYVR_OUTPUT" ]; then
    echo "Error: No DryVR output file found"
    exit 1
fi

echo "Converting DryVR output to JSON format..."

# Parse DryVR output and convert to polytope format
# This is a simplified conversion - actual implementation would parse DryVR's specific output format
{
    echo "{"
    echo '  "A": ['
    
    # Extract matrix A from DryVR output
    # This is a placeholder - actual parsing would depend on DryVR's output format
    grep -E "[-+]?[0-9]*\.?[0-9]+" "$DRYVR_OUTPUT" | head -5 | while read -r line; do
        # Convert line to array format
        echo "    [$(echo "$line" | tr ' ' ',')],"
    done | sed '$ s/,$//'
    
    echo "  ],"
    echo '  "b": ['
    
    # Extract vector b from DryVR output
    # This is a placeholder - actual parsing would depend on DryVR's output format
    grep -E "[-+]?[0-9]*\.?[0-9]+" "$DRYVR_OUTPUT" | tail -3 | while read -r line; do
        # Convert line to array format
        echo "    [$(echo "$line" | tr ' ' ',')],"
    done | sed '$ s/,$//'
    
    echo "  ]"
    echo "}"
} > "$OUTPUT_JSON"

# Validate JSON output
if ! python3 -m json.tool "$OUTPUT_JSON" > /dev/null 2>&1; then
    echo "Error: Generated JSON is invalid"
    exit 1
fi

echo "Polytope written to: $OUTPUT_JSON"

# Clean up temporary files
rm -rf "$TEMP_DIR"

echo "DryVR adapter completed successfully" 