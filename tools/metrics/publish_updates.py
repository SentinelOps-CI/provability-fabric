#!/usr/bin/env python3
"""
Publish Updates Script

This script pulls metrics from Prometheus/Pushgateway and GitHub Actions
artifacts to generate an auto-updated docs/updates.md file.
"""

import os
import sys
import json
import requests
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Optional

# Metrics configuration
METRICS_CONFIG = {
    "pii_memorization": {
        "source": "prometheus",
        "query": 'pii_detected_total{job="egress-firewall"}',
        "threshold": 50000,
        "critical": True,
    },
    "abac_fuzz": {
        "source": "prometheus",
        "query": 'abac_violations_total{job="policy-kernel"}',
        "threshold": 100000,
        "critical": True,
    },
    "injection_corpus": {
        "source": "github_actions",
        "workflow": "injection-test",
        "artifact": "block_rate.json",
        "threshold": 0.95,
        "critical": False,
    },
    "latency_p95": {
        "source": "github_actions",
        "workflow": "slo-gates",
        "artifact": "latency_metrics.json",
        "field": "p95",
        "threshold": 2.0,
        "critical": False,
    },
    "latency_p99": {
        "source": "github_actions",
        "workflow": "slo-gates",
        "artifact": "latency_metrics.json",
        "field": "p99",
        "threshold": 4.0,
        "critical": False,
    },
}


class MetricsCollector:
    """Collects metrics from various sources."""

    def __init__(self, prometheus_url: str = "http://localhost:9090"):
        self.prometheus_url = prometheus_url
        self.github_token = os.getenv("GITHUB_TOKEN")

    def get_prometheus_metric(self, query: str) -> Optional[float]:
        """Get metric from Prometheus."""
        try:
            response = requests.get(
                f"{self.prometheus_url}/api/v1/query",
                params={"query": query},
                timeout=10,
            )
            response.raise_for_status()

            data = response.json()
            if data["status"] == "success" and data["data"]["result"]:
                return float(data["data"]["result"][0]["value"][1])
            return None
        except Exception as e:
            print(f"Error querying Prometheus: {e}")
            return None

    def get_github_artifact(self, workflow: str, artifact: str) -> Optional[Dict]:
        """Get artifact from GitHub Actions."""
        if not self.github_token:
            print("Warning: GITHUB_TOKEN not set, skipping GitHub artifacts")
            return None

        try:
            # Get latest workflow run
            headers = {"Authorization": f"token {self.github_token}"}
            response = requests.get(
                f"https://api.github.com/repos/your-org/provability-fabric/actions/workflows/{workflow}/runs",
                headers=headers,
                params={"per_page": 1},
            )
            response.raise_for_status()

            runs = response.json()["workflow_runs"]
            if not runs:
                return None

            run_id = runs[0]["id"]

            # Get artifacts for this run
            response = requests.get(
                f"https://api.github.com/repos/your-org/provability-fabric/actions/runs/{run_id}/artifacts",
                headers=headers,
            )
            response.raise_for_status()

            artifacts = response.json()["artifacts"]
            for artifact_info in artifacts:
                if artifact_info["name"] == artifact:
                    # Download artifact
                    download_url = artifact_info["archive_download_url"]
                    response = requests.get(download_url, headers=headers)
                    response.raise_for_status()

                    # Parse artifact content
                    import zipfile
                    import io

                    with zipfile.ZipFile(io.BytesIO(response.content)) as z:
                        for filename in z.namelist():
                            if filename.endswith(".json"):
                                with z.open(filename) as f:
                                    return json.load(f)

            return None
        except Exception as e:
            print(f"Error getting GitHub artifact: {e}")
            return None


def collect_metrics() -> Dict[str, Dict]:
    """Collect all metrics."""
    collector = MetricsCollector()
    metrics = {}

    for metric_name, config in METRICS_CONFIG.items():
        print(f"Collecting {metric_name}...")

        if config["source"] == "prometheus":
            value = collector.get_prometheus_metric(config["query"])
            if value is not None:
                metrics[metric_name] = {
                    "value": value,
                    "threshold": config["threshold"],
                    "critical": config["critical"],
                    "status": "PASS" if value <= config["threshold"] else "FAIL",
                }

        elif config["source"] == "github_actions":
            artifact_data = collector.get_github_artifact(
                config["workflow"], config["artifact"]
            )
            if artifact_data:
                if "field" in config:
                    value = artifact_data.get(config["field"])
                else:
                    value = artifact_data.get("value", artifact_data.get("rate"))

                if value is not None:
                    metrics[metric_name] = {
                        "value": value,
                        "threshold": config["threshold"],
                        "critical": config["critical"],
                        "status": "PASS" if value >= config["threshold"] else "FAIL",
                    }

    return metrics


def generate_updates_md(metrics: Dict[str, Dict]) -> str:
    """Generate the updates.md content."""
    now = datetime.utcnow()

    content = f"""# Recent Updates

*Last updated: {now.strftime('%Y-%m-%d %H:%M:%S')} UTC*

## Security Metrics

### PII/Memorization Detection
- **Current**: {metrics.get('pii_memorization', {}).get('value', 'N/A')} / {metrics.get('pii_memorization', {}).get('threshold', 'N/A')} critical
- **Status**: {metrics.get('pii_memorization', {}).get('status', 'UNKNOWN')}
- **Critical**: {metrics.get('pii_memorization', {}).get('critical', False)}

### ABAC Fuzz Testing
- **Current**: {metrics.get('abac_fuzz', {}).get('value', 'N/A')} / {metrics.get('abac_fuzz', {}).get('threshold', 'N/A')} cross-tenant violations
- **Status**: {metrics.get('abac_fuzz', {}).get('status', 'UNKNOWN')}
- **Critical**: {metrics.get('abac_fuzz', {}).get('critical', False)}

### Injection Corpus
- **Current**: {metrics.get('injection_corpus', {}).get('value', 'N/A')} blocked
- **Threshold**: ≥{metrics.get('injection_corpus', {}).get('threshold', 'N/A')}%
- **Status**: {metrics.get('injection_corpus', {}).get('status', 'UNKNOWN')}

## Performance Metrics

### Latency (p95)
- **Current**: {metrics.get('latency_p95', {}).get('value', 'N/A')}s
- **Threshold**: ≤{metrics.get('latency_p95', {}).get('threshold', 'N/A')}s
- **Status**: {metrics.get('latency_p95', {}).get('status', 'UNKNOWN')}

### Latency (p99)
- **Current**: {metrics.get('latency_p99', {}).get('value', 'N/A')}s
- **Threshold**: ≤{metrics.get('latency_p99', {}).get('threshold', 'N/A')}s
- **Status**: {metrics.get('latency_p99', {}).get('status', 'UNKNOWN')}

## Overall Status

"""

    # Calculate overall status
    critical_failures = sum(
        1
        for metric in metrics.values()
        if metric.get("critical") and metric.get("status") == "FAIL"
    )

    total_critical = sum(1 for metric in metrics.values() if metric.get("critical"))

    if critical_failures == 0:
        content += "🟢 **All critical metrics passing**\n"
    elif critical_failures < total_critical:
        content += (
            f"🟡 **{critical_failures}/{total_critical} critical metrics failing**\n"
        )
    else:
        content += (
            f"🔴 **{critical_failures}/{total_critical} critical metrics failing**\n"
        )

    content += (
        f"\n*Generated by [publish_updates.py](/tools/metrics/publish_updates.py)*\n"
    )

    return content


def main():
    """Main function."""
    print("📊 Collecting metrics...")

    # Collect metrics
    metrics = collect_metrics()

    if not metrics:
        print("❌ No metrics collected")
        return 1

    print(f"✅ Collected {len(metrics)} metrics")

    # Generate updates.md
    content = generate_updates_md(metrics)

    # Write to docs/updates.md
    output_path = Path("docs/updates.md")
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, "w", encoding="utf-8") as f:
        f.write(content)

    print(f"✅ Updated {output_path}")

    # Check for failures
    critical_failures = [
        name
        for name, metric in metrics.items()
        if metric.get("critical") and metric.get("status") == "FAIL"
    ]

    if critical_failures:
        print(f"⚠️  Critical failures: {', '.join(critical_failures)}")
        return 1

    print("🎉 All metrics passing!")
    return 0


if __name__ == "__main__":
    sys.exit(main())
