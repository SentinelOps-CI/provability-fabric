# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Run configuration dataclass for SWE-bench runner.

from __future__ import annotations

import json
import platform
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

try:
    from engines.openhands_engine import OpenHandsConfig
except ImportError:
    OpenHandsConfig = None


@dataclass
class RunConfig:
    """Configuration for a SWE-bench run, extracted from argparse arguments."""

    # Dataset and instance selection
    dataset: str = "Lite"
    split: str = "test"
    instance_ids: str = ""
    instance_ids_file: str = ""
    max_instances: Optional[int] = None
    instances_file: str = ""

    # Experiment configuration
    experiment_dir: str = ""
    mode: str = "default"  # default, baseline, deterministic, pf_guarded
    seed: Optional[int] = None

    # Output paths
    out: str = "predictions.jsonl"
    runs_dir: str = "runs"
    run_id: str = ""
    workspaces_dir: str = "workspaces"
    dataset_cache_dir: str = ""

    # Engine configuration
    engine: str = "openhands"
    openhands_model: str = "gpt-4o-mini"
    openhands_max_iterations: int = 25
    openhands_timeout: int = 1200

    # PF-guarded configuration
    guarded: bool = False
    policy: str = ""

    # Proof configuration
    prove: bool = False
    proofs_dir: str = ""

    # Operational flags
    no_workspace: bool = False
    skip_existing: bool = False
    preflight: bool = False
    verbose_instance_logs: bool = False

    # Computed/effective values (set after validation)
    effective_guarded: bool = False
    effective_model_name: str = ""
    openhands_config: Optional[Any] = None
    instance_id_list: Optional[list[str]] = None
    # If set, used instead of sys.argv for manifest budget override checks (tests / tooling).
    manifest_argv: Optional[list[str]] = field(default=None, repr=False)

    def __post_init__(self) -> None:
        """Apply manifest budgets and compute effective values."""
        # Apply manifest budgets if experiment_dir is set (respect explicit CLI flags)
        if self.experiment_dir:
            self._apply_manifest_budgets(argv=self.manifest_argv or sys.argv)

        # Compute effective_guarded
        self.effective_guarded = self.guarded or (self.mode == "pf_guarded")

        # Default policy for pf_guarded mode
        if self.mode == "pf_guarded" and not self.policy:
            self.policy = "swebench_safe_v1"

        # Load instance_id_list from file if specified
        if self.instance_ids_file:
            p = Path(self.instance_ids_file)
            if p.exists():
                self.instance_id_list = [
                    s.strip() for s in p.read_text(encoding="utf-8").splitlines() if s.strip()
                ]
            else:
                raise ValueError(f"--instance-ids-file not found: {self.instance_ids_file}")
        elif self.instance_ids:
            self.instance_id_list = [s.strip() for s in self.instance_ids.split(",") if s.strip()]

        # Normalize dataset name
        dataset_map = {"lite": "Lite", "verified": "Verified", "full": "Full"}
        if self.dataset.lower() in dataset_map:
            self.dataset = dataset_map[self.dataset.lower()]

        # Set effective_model_name
        self.effective_model_name = self.openhands_model

        # Create OpenHandsConfig if available
        if OpenHandsConfig is not None:
            self.openhands_config = OpenHandsConfig(
                model_name=self.openhands_model,
                max_iterations=self.openhands_max_iterations,
                timeout_seconds=self.openhands_timeout,
            )

    def _apply_manifest_budgets(self, argv: Optional[list[str]] = None) -> None:
        """Apply budgets from manifest.json if experiment_dir is set and flags weren't explicitly passed."""
        if not self.experiment_dir:
            return

        manifest_path = Path(self.experiment_dir) / "manifest.json"
        if not manifest_path.exists():
            return

        argv = argv or sys.argv

        def _arg_passed(flag: str) -> bool:
            return any(a == flag or a.startswith(flag + "=") for a in argv)

        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            budgets = manifest.get("budgets") or {}

            if not _arg_passed("--openhands-max-iterations") and budgets.get("max_steps") is not None:
                self.openhands_max_iterations = int(budgets.get("max_steps", 25))
            if not _arg_passed("--openhands-timeout") and budgets.get("timeout_sec") is not None:
                self.openhands_timeout = int(budgets.get("timeout_sec", 1200))
            if not _arg_passed("--openhands-model"):
                mid = (manifest.get("model") or {}).get("id")
                if mid:
                    self.openhands_model = str(mid).strip()
        except (json.JSONDecodeError, OSError, ValueError, KeyError):
            pass  # Best-effort; use defaults

    def validate(self) -> list[str]:
        """Validate configuration and return list of error messages (empty if valid)."""
        errors: list[str] = []

        # Validate dataset
        valid_datasets = {"Lite", "Verified", "Full"}
        if self.dataset not in valid_datasets:
            errors.append(f"Unknown dataset: {self.dataset}. Must be one of {valid_datasets}")

        # Validate mode
        valid_modes = {"default", "baseline", "deterministic", "pf_guarded"}
        if self.mode not in valid_modes:
            errors.append(f"Unknown mode: {self.mode}. Must be one of {valid_modes}")

        # Validate engine
        valid_engines = {"openhands", "direct_agent", "mock"}
        if self.engine not in valid_engines:
            errors.append(f"Unknown engine: {self.engine}. Must be one of {valid_engines}")

        # Windows platform check
        if platform.system() == "Windows":
            if self.engine != "mock" and self.mode != "deterministic":
                errors.append(
                    "OpenHands requires fcntl (Unix). On Windows, use --engine mock or --mode deterministic only."
                )

        # Validate paths
        if self.instance_ids_file and not Path(self.instance_ids_file).exists():
            errors.append(f"--instance-ids-file not found: {self.instance_ids_file}")

        if self.instances_file and not Path(self.instances_file).exists():
            errors.append(f"--instances-file not found: {self.instances_file}")

        return errors

    @classmethod
    def from_args(cls, args: Any) -> RunConfig:
        """Create RunConfig from argparse.Namespace."""
        skip = frozenset(
            {
                "effective_guarded",
                "effective_model_name",
                "openhands_config",
                "instance_id_list",
                "manifest_argv",
            }
        )
        config_dict: dict[str, Any] = {}
        for field_name in cls.__dataclass_fields__:
            if field_name in skip:
                continue
            if hasattr(args, field_name):
                config_dict[field_name] = getattr(args, field_name)

        return cls(**config_dict)

    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary (excluding computed fields for serialization)."""
        return {
            "dataset": self.dataset,
            "split": self.split,
            "instance_ids": self.instance_ids,
            "instance_ids_file": self.instance_ids_file,
            "max_instances": self.max_instances,
            "instances_file": self.instances_file,
            "experiment_dir": self.experiment_dir,
            "mode": self.mode,
            "seed": self.seed,
            "out": self.out,
            "runs_dir": self.runs_dir,
            "run_id": self.run_id,
            "workspaces_dir": self.workspaces_dir,
            "dataset_cache_dir": self.dataset_cache_dir,
            "engine": self.engine,
            "openhands_model": self.openhands_model,
            "openhands_max_iterations": self.openhands_max_iterations,
            "openhands_timeout": self.openhands_timeout,
            "guarded": self.guarded,
            "policy": self.policy,
            "prove": self.prove,
            "proofs_dir": self.proofs_dir,
            "no_workspace": self.no_workspace,
            "skip_existing": self.skip_existing,
            "preflight": self.preflight,
            "verbose_instance_logs": self.verbose_instance_logs,
        }


def build_argument_parser() -> Any:
    """CLI parser for SWE-bench runner (shared with main for a thinner entrypoint)."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Run SWE-bench instances and emit predictions.jsonl + PF evidence.",
    )
    parser.add_argument(
        "--dataset",
        type=str,
        default="Lite",
        help="SWE-bench dataset: Lite/lite, Verified/verified, or Full/full",
    )
    parser.add_argument(
        "--split",
        default="test",
        help="Dataset split (e.g. test, dev)",
    )
    parser.add_argument(
        "--instance_ids",
        type=str,
        default="",
        help="Comma-separated instance IDs to run (optional filter)",
    )
    parser.add_argument(
        "--max_instances",
        type=int,
        default=None,
        help="Maximum number of instances to run (optional cap)",
    )
    parser.add_argument(
        "--instances-file",
        type=str,
        default="",
        help="Load instances from local JSON/JSONL file instead of HuggingFace",
    )
    parser.add_argument(
        "--instance-ids-file",
        type=str,
        default="",
        help="Path to file with one instance_id per line (used as instance filter with dataset)",
    )
    parser.add_argument(
        "--experiment-dir",
        type=str,
        default="",
        help="Experiment directory containing manifest.json; budgets (max_steps, timeout_sec) are used as defaults for --openhands-max-iterations and --openhands-timeout when not explicitly set",
    )
    parser.add_argument(
        "--mode",
        type=str,
        default="default",
        choices=["default", "baseline", "deterministic", "pf_guarded"],
        help="default/baseline: run engine (baseline = no PF enforcement); deterministic: gold patch only; pf_guarded: PF policy + sidecar enforcement (requires --policy or defaults to swebench_safe_v1)",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=None,
        help="Random seed for reproducibility (e.g. 42); passed to engine when supported",
    )
    parser.add_argument(
        "--out",
        type=str,
        default="predictions.jsonl",
        help="Output path for predictions.jsonl",
    )
    parser.add_argument(
        "--skip-existing",
        action="store_true",
        help="Resume: skip instances already present in --out; copy their lines and pfmeta from existing files.",
    )
    parser.add_argument(
        "--engine",
        type=str,
        default="openhands",
        help="Engine to use (openhands, direct_agent, mock). direct_agent: native OpenAI-compatible loop; mock: no OpenHands, for CI smoke tests.",
    )
    parser.add_argument(
        "--runs-dir",
        type=str,
        default="runs",
        help="Base directory for PF evidence (runs/<run_id>/<instance_id>/...)",
    )
    parser.add_argument(
        "--run-id",
        type=str,
        default="",
        help="Run ID for this execution (default: auto-generated)",
    )
    parser.add_argument(
        "--workspaces-dir",
        type=str,
        default="workspaces",
        help="Base directory for materialized workspaces (repo + task prompt + scratch)",
    )
    parser.add_argument(
        "--dataset-cache-dir",
        type=str,
        default="",
        help="HuggingFace dataset cache dir (speeds repeated runs; default uses HF cache)",
    )
    parser.add_argument(
        "--no-workspace",
        action="store_true",
        help="Skip workspace materialization (no clone/checkout; use for instances-file-only runs)",
    )
    parser.add_argument(
        "--openhands-model",
        type=str,
        default="gpt-4o-mini",
        help="OpenHands model name (default: gpt-4o-mini)",
    )
    parser.add_argument(
        "--openhands-max-iterations",
        type=int,
        default=25,
        help="OpenHands max iterations (default: 25)",
    )
    parser.add_argument(
        "--openhands-timeout",
        type=int,
        default=1200,
        help="OpenHands timeout in seconds (default: 1200; use manifest budgets.timeout_sec when --experiment-dir is set)",
    )
    parser.add_argument(
        "--guarded",
        action="store_true",
        help="Run OpenHands through PF-Guarded Runtime (tool gateway, ledger, compliance)",
    )
    parser.add_argument(
        "--policy",
        type=str,
        default="",
        help="Policy pack name (e.g. swebench_safe_v1). Policy hash is included in evidence bundle.",
    )
    parser.add_argument(
        "--prove",
        action="store_true",
        help="Run proof step: build policy-trace Lean proof; write proof.ok + proof_artifact_hash on success, proof_failure.json on failure.",
    )
    parser.add_argument(
        "--proofs-dir",
        type=str,
        default="",
        help="Path to Lean proofs dir (default: repo/spec-templates/v1/proofs). Used when --prove is set.",
    )
    parser.add_argument(
        "--preflight",
        action="store_true",
        help="Only materialize workspaces, ensure clean, and report repo stats (no OpenHands run). Use before long runs to see which instances are large or dirty.",
    )
    parser.add_argument(
        "--verbose-instance-logs",
        action="store_true",
        help="Print detailed per-instance phase timings and trace diagnostics.",
    )
    return parser
