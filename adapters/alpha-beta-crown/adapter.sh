#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

# Usage: ./adapter.sh model.pt property.json witness.json [--gpu] [--timeout 600]

MODEL_FILE="$1"
PROPERTY_FILE="$2"
OUTPUT_FILE="$3"
GPU_FLAG="--gpu"
TIMEOUT="600"

# Parse additional arguments
shift 3
while [[ $# -gt 0 ]]; do
    case $1 in
        --gpu)
            GPU_FLAG="--gpu"
            shift
            ;;
        --no-gpu)
            GPU_FLAG="--no-gpu"
            shift
            ;;
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Validate input files exist
if [ ! -f "$MODEL_FILE" ]; then
    echo "Error: Model file '$MODEL_FILE' not found"
    exit 1
fi

if [ ! -f "$PROPERTY_FILE" ]; then
    echo "Error: Property file '$PROPERTY_FILE' not found"
    exit 1
fi

echo "Running α-β-CROWN verification..."

# Run α-β-CROWN docker container
docker run --rm \
    --gpus all \
    -v "$(realpath "$MODEL_FILE"):/input/model.pt" \
    -v "$(realpath "$PROPERTY_FILE"):/input/property.json" \
    -v "$(realpath "$(dirname "$OUTPUT_FILE")"):/output" \
    alpha-beta-crown:latest \
    python3 /opt/adapter.py \
    /input/model.pt \
    /input/property.json \
    --out "/output/$(basename "$OUTPUT_FILE")" \
    $GPU_FLAG \
    --timeout "$TIMEOUT"

# Check if α-β-CROWN succeeded
if [ $? -ne 0 ]; then
    echo "Error: α-β-CROWN execution failed"
    exit 1
fi

echo "α-β-CROWN adapter completed successfully"
