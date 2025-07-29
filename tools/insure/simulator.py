#!/usr/bin/env python3
"""
Insurance Premium Simulator for Provability-Fabric

This tool analyzes ledger data to simulate insurance premiums and generate
risk vs premium charts for AI agent deployments.
"""

import argparse
import json
import requests
import matplotlib.pyplot as plt
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, List, Optional
import pandas as pd
from pathlib import Path


class InsuranceSimulator:
    def __init__(self, ledger_url: str = "http://localhost:4000"):
        self.ledger_url = ledger_url
        self.base_rate = 1000.0  # Base annual premium rate

    def fetch_ledger_data(self, days: int = 30) -> List[Dict]:
        """Fetch ledger data from the last N days"""
        try:
            # Query GraphQL for capsules with premium quotes
            query = """
            query {
                capsules {
                    hash
                    riskScore
                    createdAt
                    premiumQuotes {
                        annualUsd
                        createdAt
                    }
                }
            }
            """

            response = requests.post(
                f"{self.ledger_url}/graphql",
                json={"query": query},
                headers={"Content-Type": "application/json"},
            )

            if response.status_code != 200:
                print(f"❌ Failed to fetch ledger data: {response.status_code}")
                return []

            data = response.json()
            capsules = data.get("data", {}).get("capsules", [])

            # Filter by date range
            cutoff_date = datetime.now() - timedelta(days=days)
            filtered_capsules = []

            for capsule in capsules:
                created_at = datetime.fromisoformat(
                    capsule["createdAt"].replace("Z", "+00:00")
                )
                if created_at >= cutoff_date:
                    filtered_capsules.append(capsule)

            return filtered_capsules

        except Exception as e:
            print(f"❌ Error fetching ledger data: {e}")
            return []

    def calculate_premium(self, risk_score: float) -> float:
        """Calculate annual premium based on risk score"""
        return risk_score * self.base_rate

    def generate_risk_premium_data(self, capsules: List[Dict]) -> Dict:
        """Generate risk vs premium data for analysis"""
        risk_scores = []
        premiums = []
        capsule_hashes = []

        for capsule in capsules:
            risk_score = capsule["riskScore"]
            premium = self.calculate_premium(risk_score)

            risk_scores.append(risk_score)
            premiums.append(premium)
            capsule_hashes.append(capsule["hash"])

        return {
            "risk_scores": risk_scores,
            "premiums": premiums,
            "capsule_hashes": capsule_hashes,
            "count": len(capsules),
        }

    def generate_charts(self, data: Dict, output_dir: str = "docs/insights"):
        """Generate risk vs premium charts"""
        Path(output_dir).mkdir(parents=True, exist_ok=True)

        # Create scatter plot
        plt.figure(figsize=(12, 8))

        # Main scatter plot
        plt.scatter(
            data["risk_scores"],
            data["premiums"],
            alpha=0.6,
            s=100,
            c="blue",
            label="Capsules",
        )

        # Add trend line
        if len(data["risk_scores"]) > 1:
            z = np.polyfit(data["risk_scores"], data["premiums"], 1)
            p = np.poly1d(z)
            plt.plot(
                data["risk_scores"],
                p(data["risk_scores"]),
                "r--",
                alpha=0.8,
                label=f"Trend (y={z[0]:.0f}x+{z[1]:.0f})",
            )

        plt.xlabel("Risk Score")
        plt.ylabel("Annual Premium (USD)")
        plt.title("Risk Score vs Annual Premium")
        plt.legend()
        plt.grid(True, alpha=0.3)

        # Add statistics
        stats_text = f"""
        Total Capsules: {data['count']}
        Avg Risk Score: {np.mean(data['risk_scores']):.3f}
        Avg Premium: ${np.mean(data['premiums']):.0f}
        Max Premium: ${np.max(data['premiums']):.0f}
        Min Premium: ${np.min(data['premiums']):.0f}
        """
        plt.text(
            0.02,
            0.98,
            stats_text,
            transform=plt.gca().transAxes,
            verticalalignment="top",
            bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.8),
        )

        plt.tight_layout()
        chart_path = f"{output_dir}/risk_premium_chart.png"
        plt.savefig(chart_path, dpi=300, bbox_inches="tight")
        plt.close()

        print(f"✅ Chart saved: {chart_path}")

        # Create premium distribution histogram
        plt.figure(figsize=(10, 6))
        plt.hist(data["premiums"], bins=20, alpha=0.7, color="green", edgecolor="black")
        plt.xlabel("Annual Premium (USD)")
        plt.ylabel("Frequency")
        plt.title("Premium Distribution")
        plt.grid(True, alpha=0.3)

        hist_path = f"{output_dir}/premium_distribution.png"
        plt.savefig(hist_path, dpi=300, bbox_inches="tight")
        plt.close()

        print(f"✅ Histogram saved: {hist_path}")

    def generate_report(self, data: Dict, output_dir: str = "docs/insights") -> str:
        """Generate comprehensive insurance report"""
        Path(output_dir).mkdir(parents=True, exist_ok=True)

        report = f"""
# Insurance Premium Analysis Report

**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S UTC')}
**Data Period:** Last 30 days
**Total Capsules Analyzed:** {data['count']}

## Summary Statistics

- **Average Risk Score:** {np.mean(data['risk_scores']):.3f}
- **Average Annual Premium:** ${np.mean(data['premiums']):.0f}
- **Maximum Premium:** ${np.max(data['premiums']):.0f}
- **Minimum Premium:** ${np.min(data['premiums']):.0f}
- **Premium Standard Deviation:** ${np.std(data['premiums']):.0f}

## Risk Categories

- **Low Risk (0.0-0.3):** {len([r for r in data['risk_scores'] if 0 <= r <= 0.3])} capsules
- **Medium Risk (0.3-0.7):** {len([r for r in data['risk_scores'] if 0.3 < r <= 0.7])} capsules  
- **High Risk (0.7-1.0):** {len([r for r in data['risk_scores'] if 0.7 < r <= 1.0])} capsules

## Premium Ranges

- **$0-$1,000:** {len([p for p in data['premiums'] if p <= 1000])} capsules
- **$1,000-$5,000:** {len([p for p in data['premiums'] if 1000 < p <= 5000])} capsules
- **$5,000-$10,000:** {len([p for p in data['premiums'] if 5000 < p <= 10000])} capsules
- **$10,000+:** {len([p for p in data['premiums'] if p > 10000])} capsules

## Top 5 Highest Risk Capsules

"""

        # Sort by risk score
        sorted_data = sorted(
            zip(data["capsule_hashes"], data["risk_scores"], data["premiums"]),
            key=lambda x: x[1],
            reverse=True,
        )

        for i, (hash_val, risk, premium) in enumerate(sorted_data[:5], 1):
            report += f"{i}. **{hash_val[:8]}...** - Risk: {risk:.3f}, Premium: ${premium:.0f}\n"

        report += f"""
## Charts Generated

- `risk_premium_chart.png` - Scatter plot of risk vs premium
- `premium_distribution.png` - Histogram of premium distribution

## Methodology

Premiums are calculated using the formula:
```
Annual Premium = Risk Score × Base Rate (${self.base_rate})
```

This provides a linear relationship between risk and premium, suitable for
insurance-grade risk assessment of AI agent deployments.

## Compliance Notes

This analysis supports:
- EU AI Act Annex VIII requirements
- Insurance industry risk assessment standards
- Regulatory transparency requirements
"""

        report_path = f"{output_dir}/insurance_report.md"
        with open(report_path, "w") as f:
            f.write(report)

        print(f"✅ Report saved: {report_path}")
        return report_path

    def run_simulation(self, days: int = 30, output_dir: str = "docs/insights") -> bool:
        """Run the complete insurance simulation"""
        print(f"🔍 Fetching ledger data for the last {days} days...")

        capsules = self.fetch_ledger_data(days)
        if not capsules:
            print("❌ No data available for analysis")
            return False

        print(f"✅ Found {len(capsules)} capsules for analysis")

        # Generate data
        data = self.generate_risk_premium_data(capsules)

        # Generate charts
        print("📊 Generating charts...")
        self.generate_charts(data, output_dir)

        # Generate report
        print("📝 Generating report...")
        self.generate_report(data, output_dir)

        print("✅ Insurance simulation completed successfully!")
        return True


def main():
    parser = argparse.ArgumentParser(description="Insurance Premium Simulator")
    parser.add_argument(
        "--ledger-url", default="http://localhost:4000", help="Ledger service URL"
    )
    parser.add_argument(
        "--days", type=int, default=30, help="Number of days to analyze"
    )
    parser.add_argument(
        "--output-dir",
        default="docs/insights",
        help="Output directory for reports and charts",
    )

    args = parser.parse_args()

    simulator = InsuranceSimulator(args.ledger_url)
    success = simulator.run_simulation(args.days, args.output_dir)

    exit(0 if success else 1)


if __name__ == "__main__":
    main()
