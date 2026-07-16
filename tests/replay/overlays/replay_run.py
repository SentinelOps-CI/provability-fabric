#!/usr/bin/env python3
"""
TRACE-REPLAY-KIT Replay Runner (PF overlay)

Identical to external/TRACE-REPLAY-KIT/runner/replay_run.py except schema
loading prefers CERT_V1_SCHEMA_PATH / the in-repo fixture. The upstream
raw.githubusercontent.com CERT-V1 URL 404s (private repo + wrong filename).
"""

import argparse
import json
import os
import sys
import hashlib
from datetime import datetime
import jsonschema
import requests
from typing import Dict, Any, List


# Upstream URL (kept as last-resort fallback; currently 404 for private CERT-V1)
CERT_V1_SCHEMA_URL = (
    "https://raw.githubusercontent.com/verifiable-ai-ci/"
    "CERT-V1/v1.0.0/schema/cert-v1.json"
)

LOCAL_SCHEMA_CANDIDATES = [
    "/work/tests/replay/schema/trace-replay-cert.schema.json",
    os.path.join(
        os.path.dirname(__file__),
        "..",
        "..",
        "..",
        "tests",
        "replay",
        "schema",
        "trace-replay-cert.schema.json",
    ),
]


class ReplayRunner:
    """Main replay runner class."""

    def __init__(self):
        self.cert_schema = None
        self.load_cert_schema()

    def load_cert_schema(self):
        """Load schema: env/local fixture first, then pinned URL."""
        candidates: List[str] = []
        env_path = os.environ.get("CERT_V1_SCHEMA_PATH")
        if env_path:
            candidates.append(env_path)
        candidates.extend(LOCAL_SCHEMA_CANDIDATES)

        for path in candidates:
            if not path:
                continue
            try:
                if os.path.isfile(path):
                    with open(path, "r", encoding="utf-8") as f:
                        self.cert_schema = json.load(f)
                    print(f"Loaded CERT schema from: {path}")
                    return
            except Exception as e:
                print(f"Warning: Could not load CERT schema from {path}: {e}")

        try:
            response = requests.get(CERT_V1_SCHEMA_URL, timeout=30)
            response.raise_for_status()
            self.cert_schema = response.json()
            print(f"Loaded CERT schema from URL: {CERT_V1_SCHEMA_URL}")
            return
        except Exception as e:
            print(f"Warning: Could not load CERT-V1 schema: {e}")
            self.cert_schema = None

        if os.environ.get("CERT_V1_SCHEMA_REQUIRED") == "1":
            raise RuntimeError(
                "CERT schema required (CERT_V1_SCHEMA_REQUIRED=1) but none loaded"
            )

    def validate_trace(self, trace_path: str) -> Dict[str, Any]:
        """Validate and load trace file."""
        try:
            with open(trace_path, "r") as f:
                trace_data = json.load(f)

            if "events" not in trace_data:
                raise ValueError("Trace must contain 'events' array")

            if "metadata" not in trace_data:
                raise ValueError("Trace must contain 'metadata'")

            return trace_data
        except Exception as e:
            raise ValueError(f"Invalid trace file: {e}")

    def validate_env(self, env_path: str) -> Dict[str, Any]:
        """Validate and load environment configuration."""
        try:
            with open(env_path, "r") as f:
                env_data = json.load(f)

            required_fields = ["locale", "timezone", "seed", "versions"]
            for field in required_fields:
                if field not in env_data:
                    raise ValueError(f"Environment must contain '{field}'")

            return env_data
        except Exception as e:
            raise ValueError(f"Invalid environment file: {e}")

    def execute_replay(
        self, trace_data: Dict[str, Any], env_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Execute the replay based on trace and environment."""
        os.environ["LC_ALL"] = env_data["locale"]
        os.environ["TZ"] = env_data["timezone"]
        os.environ["PYTHONHASHSEED"] = str(env_data["seed"])

        results = []
        for event in trace_data["events"]:
            result = self.process_event(event, env_data)
            results.append(result)

        return {
            "replay_id": hashlib.sha256(
                json.dumps(trace_data, sort_keys=True).encode()
            ).hexdigest()[:16],
            "timestamp": datetime.utcnow().isoformat() + "Z",
            "environment": env_data,
            "results": results,
            "summary": {
                "total_events": len(results),
                "successful_events": len(
                    [r for r in results if r["status"] == "success"]
                ),
                "failed_events": len([r for r in results if r["status"] == "failed"]),
            },
        }

    def process_event(
        self, event: Dict[str, Any], env_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Process a single event from the trace."""
        try:
            event_type = event.get("type", "unknown")

            if event_type == "function_call":
                return self.process_function_call(event, env_data)
            elif event_type == "streaming_egress":
                return self.process_streaming_egress(event, env_data)
            elif event_type == "declassification":
                return self.process_declassification(event, env_data)
            elif event_type == "epoch_revocation":
                return self.process_epoch_revocation(event, env_data)
            else:
                return {
                    "event_id": event.get("id", "unknown"),
                    "status": "skipped",
                    "message": f"Unknown event type: {event_type}",
                }
        except Exception as e:
            return {
                "event_id": event.get("id", "unknown"),
                "status": "failed",
                "error": str(e),
            }

    def process_function_call(
        self, event: Dict[str, Any], env_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Process a function call event."""
        return {
            "event_id": event.get("id"),
            "status": "success",
            "type": "function_call",
            "result": f"Executed {event.get('payload', {}).get('function', 'unknown')}",
        }

    def process_streaming_egress(
        self, event: Dict[str, Any], env_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Process a streaming egress event."""
        return {
            "event_id": event.get("id"),
            "status": "success",
            "type": "streaming_egress",
            "result": "Stream processed successfully",
        }

    def process_declassification(
        self, event: Dict[str, Any], env_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Process a declassification event."""
        return {
            "event_id": event.get("id"),
            "status": "success",
            "type": "declassification",
            "result": "Security level changed",
        }

    def process_epoch_revocation(
        self, event: Dict[str, Any], env_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Process an epoch revocation event."""
        return {
            "event_id": event.get("id"),
            "status": "success",
            "type": "epoch_revocation",
            "result": "Epoch access revoked",
        }

    def generate_cert_v1(
        self, replay_result: Dict[str, Any], trace_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Generate a CERT-V1 certificate."""
        schema_ref = os.environ.get(
            "CERT_V1_SCHEMA_PATH",
            "https://provability-fabric.local/schemas/trace-replay-cert.schema.json",
        )
        cert = {
            "$schema": schema_ref,
            "cert_type": "trace_replay",
            "version": "1.0.0",
            "timestamp": replay_result["timestamp"],
            "replay_id": replay_result["replay_id"],
            "trace_metadata": trace_data.get("metadata", {}),
            "environment": replay_result["environment"],
            "results": replay_result["results"],
            "summary": replay_result["summary"],
            "signature": {
                "algorithm": "sha256",
                "hash": hashlib.sha256(
                    json.dumps(replay_result, sort_keys=True).encode()
                ).hexdigest(),
            },
        }

        if self.cert_schema:
            try:
                jsonschema.validate(cert, self.cert_schema)
            except jsonschema.ValidationError as e:
                print(
                    f"Warning: Generated certificate does not validate against schema: {e}"
                )
                if os.environ.get("CERT_V1_SCHEMA_REQUIRED") == "1":
                    raise

        return cert

    def run(self, args):
        """Main execution method."""
        try:
            trace_data = self.validate_trace(args.trace)
            env_data = self.validate_env(args.fixtures + "/env.json")

            replay_result = self.execute_replay(trace_data, env_data)

            cert = self.generate_cert_v1(replay_result, trace_data)

            if args.cert_out:
                with open(args.cert_out, "w") as f:
                    json.dump(cert, f, indent=2)
                print(f"Certificate written to: {args.cert_out}")
            else:
                print(json.dumps(cert, indent=2))

            if replay_result["summary"]["failed_events"] > 0:
                sys.exit(1)

        except Exception as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="TRACE-REPLAY-KIT Replay Runner")
    parser.add_argument("--bundle", help="Path to bundle directory")
    parser.add_argument("--trace", required=True, help="Path to trace.json file")
    parser.add_argument("--fixtures", required=True, help="Path to fixtures directory")
    parser.add_argument("--cert-out", help="Output path for CERT-V1 certificate")
    parser.add_argument(
        "--validate-env", help="Validate environment configuration file"
    )

    args = parser.parse_args()

    runner = ReplayRunner()

    if args.validate_env:
        try:
            env_data = runner.validate_env(args.validate_env)
            print("Environment configuration is valid")
            print(json.dumps(env_data, indent=2))
        except Exception as e:
            print(f"Environment validation failed: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        runner.run(args)


if __name__ == "__main__":
    main()
