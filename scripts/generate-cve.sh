#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

# Usage: ./generate-cve.sh <CVE-ID> <description> <severity>

if [ $# -ne 3 ]; then
    echo "Usage: $0 <CVE-ID> <description> <severity>"
    echo "Example: $0 CVE-2025-0001 'Buffer overflow in sidecar watcher' HIGH"
    exit 1
fi

CVE_ID="$1"
DESCRIPTION="$2"
SEVERITY="$3"

# Validate severity
case "$SEVERITY" in
    CRITICAL|HIGH|MEDIUM|LOW)
        ;;
    *)
        echo "Error: Severity must be CRITICAL, HIGH, MEDIUM, or LOW"
        exit 1
        ;;
esac

# Generate CVE JSON 5.0 format
cat > "cves/${CVE_ID}.json" << EOF
{
  "dataType": "CVE_RECORD",
  "dataVersion": "5.0",
  "cveMetadata": {
    "cveId": "${CVE_ID}",
    "assignerOrgId": "provability-fabric",
    "requesterUserId": "security-team",
    "dateReserved": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "datePublished": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "dateUpdated": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "state": "PUBLISHED"
  },
  "containers": {
    "cna": {
      "providerMetadata": {
        "orgId": "provability-fabric",
        "shortName": "ProvabilityFabric",
        "dateUpdated": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
      },
      "title": "${DESCRIPTION}",
      "descriptions": [
        {
          "lang": "en",
          "value": "${DESCRIPTION}",
          "supportingMedia": [
            {
              "type": "text/html",
              "base64": false,
              "value": "<p>${DESCRIPTION}</p>"
            }
          ]
        }
      ],
      "problemTypes": [
        {
          "descriptions": [
            {
              "lang": "en",
              "type": "CWE",
              "cweId": "CWE-119",
              "description": "Improper Restriction of Operations within the Bounds of a Memory Buffer"
            }
          ]
        }
      ],
      "affected": [
        {
          "vendor": "ProvabilityFabric",
          "product": "provability-fabric",
          "versions": [
            {
              "version": "0.1.0",
              "status": "affected"
            },
            {
              "version": "0.2.0",
              "status": "affected"
            }
          ],
          "defaultStatus": "unaffected"
        }
      ],
      "metrics": [
        {
          "cvssV3_1": {
            "version": "3.1",
            "vectorString": "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H",
            "attackVector": "NETWORK",
            "attackComplexity": "LOW",
            "privilegesRequired": "NONE",
            "userInteraction": "NONE",
            "scope": "UNCHANGED",
            "confidentialityImpact": "HIGH",
            "integrityImpact": "HIGH",
            "availabilityImpact": "HIGH",
            "baseScore": 9.8,
            "baseSeverity": "${SEVERITY}"
          }
        }
      ],
      "references": [
        {
          "url": "https://github.com/provability-fabric/provability-fabric/security/advisories",
          "name": "Security Advisory",
          "refsource": "MISC"
        }
      ],
      "x_remediations": {
        "remediation": "Update to version 0.2.1 or later",
        "impact": "High severity vulnerability requiring immediate attention"
      }
    }
  }
}
EOF

echo "Generated CVE JSON: cves/${CVE_ID}.json"
echo "Please review and submit to CVE database" 