#!/usr/bin/env python3
"""Materialize benchmarks/admission case JSON from PF fixtures."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import pathlib
import shutil
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def file_digest(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def write_case(base: pathlib.Path, kind: str, name: str, body: dict) -> None:
    d = base / kind
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{name}.json").write_text(json.dumps(body, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Materialize benchmarks/admission case JSON from PF fixtures.")
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Only print the OK line (for benchmark shell scripts).",
    )
    args = parser.parse_args()
    quiet = args.quiet or bool(os.environ.get("PCS_BENCHMARK_QUIET"))

    lt = ROOT / "tests/pcs/fixtures/labtrust-release"
    bench_lt = ROOT / "benchmarks/admission/labtrust_qc_release"
    support = bench_lt / "support"
    support.mkdir(parents=True, exist_ok=True)

    workflow = {
        "workflow_id": "labtrust_qc_release",
        "profile_id": "labtrust_qc_release",
        "fixture_root": "${repo}/tests/pcs/fixtures/labtrust-release",
        "defaults": {
            "bundle": "science_claim_bundle.certified.json",
            "handoff": "handoff_to_pf.json",
            "registry": "artifact_registry.json",
            "manifest": "release_manifest.v0.json",
            "artifact_dir": ".",
            "proof_obligations": "proof_obligation.v0.json",
            "lean_check_result": "lean_check_result.v0.json",
        },
    }
    (bench_lt / "workflow.json").write_text(json.dumps(workflow, indent=2) + "\n", encoding="utf-8")

    explain_full = {
        "failure_code": True,
        "artifact_path": True,
        "expected": True,
        "actual": True,
        "responsible_component": True,
        "repair_hint": True,
    }
    explain_science = {
        "failure_code": True,
        "expected": True,
        "actual": True,
        "responsible_component": True,
        "repair_hint": True,
    }
    explain_formal = {
        **explain_full,
        "registry_check_ref": True,
        "formal_theorem": True,
    }

    reg = json.loads((lt / "artifact_registry.json").read_text(encoding="utf-8"))
    reg_bad_prod = copy.deepcopy(reg)
    reg_bad_prod["entries"]["TraceCertificate.v0"]["producer"] = "wrong-producer"
    (support / "registry_wrong_producer.json").write_text(
        json.dumps(reg_bad_prod, indent=2) + "\n", encoding="utf-8"
    )

    reg_bad_status = copy.deepcopy(reg)
    reg_bad_status["entries"]["RuntimeReceipt.v0"]["allowed_statuses"] = ["Stale"]
    (support / "registry_disallowed_status.json").write_text(
        json.dumps(reg_bad_status, indent=2) + "\n", encoding="utf-8"
    )

    lean_fail = json.loads((lt / "lean_check_result.v0.json").read_text(encoding="utf-8"))
    lean_fail["status"] = "Rejected"
    lean_fail["obligation_results"][0]["status"] = "failed"
    (support / "lean_check_failed.v0.json").write_text(json.dumps(lean_fail, indent=2) + "\n", encoding="utf-8")

    lean_bad_thm = json.loads((lt / "lean_check_result.v0.json").read_text(encoding="utf-8"))
    lean_bad_thm["lean_theorem"] = "not_a_real_theorem"
    lean_bad_thm["obligation_results"][0]["lean_theorem"] = "not_a_real_theorem"
    (support / "lean_unauthorized_theorem.v0.json").write_text(
        json.dumps(lean_bad_thm, indent=2) + "\n", encoding="utf-8"
    )

    po = json.loads((lt / "proof_obligation.v0.json").read_text(encoding="utf-8"))
    po_bad_rel = copy.deepcopy(po)
    po_bad_rel["release_id"] = "release-wrong-id"
    (support / "proof_obligation_release_mismatch.v0.json").write_text(
        json.dumps(po_bad_rel, indent=2) + "\n", encoding="utf-8"
    )

    release_hash_dir = support / "release_bundle_hash_mismatch"
    if release_hash_dir.exists():
        shutil.rmtree(release_hash_dir)
    release_hash_dir.mkdir(parents=True)
    for name in (
        "science_claim_bundle.certified.json",
        "signed_science_claim_bundle.json",
        "release_manifest.v0.json",
        "handoff_to_pf.json",
        "artifact_registry.json",
        "proof_obligation.v0.json",
        "lean_check_result.v0.json",
        "scientific_memory_import_report.json",
        "verification_result.json",
    ):
        shutil.copy2(lt / name, release_hash_dir / name)
    signed_bad = json.loads((lt / "signed_science_claim_bundle.json").read_text(encoding="utf-8"))
    signed_bad["signed_input_bundle_hash"] = (
        "sha256:0000000000000000000000000000000000000000000000000000000000000000"
    )
    signed_path = release_hash_dir / "signed_science_claim_bundle.json"
    signed_path.write_text(json.dumps(signed_bad, indent=2) + "\n", encoding="utf-8")
    signed_on_disk = file_digest(signed_path)
    manifest = json.loads((release_hash_dir / "release_manifest.v0.json").read_text(encoding="utf-8"))
    manifest["artifacts"]["signed_science_claim_bundle.json"]["sha256"] = signed_on_disk
    manifest["canonical_signed_bundle"]["sha256"] = signed_on_disk
    (release_hash_dir / "release_manifest.v0.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )

    sm_fail_dir = support / "scientific_memory_import_failed"
    if sm_fail_dir.exists():
        shutil.rmtree(sm_fail_dir)
    sm_fail_dir.mkdir(parents=True)
    for name in (
        "science_claim_bundle.certified.json",
        "signed_science_claim_bundle.json",
        "release_manifest.v0.json",
        "handoff_to_pf.json",
        "artifact_registry.json",
        "proof_obligation.v0.json",
        "lean_check_result.v0.json",
        "scientific_memory_import_report.json",
        "verification_result.json",
    ):
        shutil.copy2(lt / name, sm_fail_dir / name)
    sm_fail = json.loads((sm_fail_dir / "scientific_memory_import_report.json").read_text(encoding="utf-8"))
    sm_fail["verification_status"] = "failed"
    sm_path = sm_fail_dir / "scientific_memory_import_report.json"
    sm_path.write_text(json.dumps(sm_fail, indent=2) + "\n", encoding="utf-8")
    sm_manifest = json.loads((sm_fail_dir / "release_manifest.v0.json").read_text(encoding="utf-8"))
    sm_digest = file_digest(sm_path)
    sm_manifest["artifacts"]["scientific_memory_import_report.json"]["sha256"] = sm_digest
    (sm_fail_dir / "release_manifest.v0.json").write_text(
        json.dumps(sm_manifest, indent=2) + "\n", encoding="utf-8"
    )

    write_case(bench_lt, "valid", "release_admission", {"case_id": "release_admission", "expect": "admit", "verify_mode": "science_claim"})
    write_case(bench_lt, "valid", "release_chain", {"case_id": "release_chain", "expect": "admit", "verify_mode": "release_chain"})

    invalid_cases = [
        ("missing_handoff", {"omit_handoff": True}, ["release_mode_handoff_required"], "science_claim", None, None),
        ("legacy_handoff_in_release_mode", {"handoff": "pf_handoff.json"}, ["legacy_handoff_forbidden_in_release_mode"], "science_claim", None, None),
        ("missing_registry", {"omit_registry": True}, ["release_mode_registry_required"], "science_claim", None, None),
        ("wrong_admission_profile", {}, ["admission_profile_workflow_mismatch"], "science_claim", None, {"profile_id": "agent_tool_use_safety"}),
        (
            "certificate_status_rejected",
            {"bundle": "invalid_rejected_certificate.json", "omit_handoff": True},
            ["PCS_CERTIFICATE_REJECTED"],
            "science_claim",
            None,
            None,
        ),
        (
            "rejected_certificate",
            {"bundle": "invalid_rejected_certificate.json", "omit_handoff": True},
            ["PCS_CERTIFICATE_REJECTED"],
            "science_claim",
            None,
            None,
        ),
        (
            "trace_hash_mismatch",
            {"bundle": "invalid_mismatched_trace_hash.json", "omit_handoff": True},
            ["PCS_TRACE_HASH_MISMATCH"],
            "science_claim",
            None,
            None,
        ),
        (
            "bundle_hash_mismatch",
            {"artifact_dir": "support/release_bundle_hash_mismatch"},
            ["signed_input_bundle_hash_match"],
            "release_chain",
            {"check_id": "signed_input_bundle_hash_match", "artifact_path": "signed_science_claim_bundle.json"},
            None,
        ),
        (
            "scientific_memory_import_failure",
            {
                "artifact_dir": "support/scientific_memory_import_failed",
                "manifest": "support/scientific_memory_import_failed/release_manifest.v0.json",
            },
            ["scientific_memory_import_failed"],
            "release_chain",
            {"check_id": "scientific_memory_import_passed", "artifact_path": "scientific_memory_import_report.json"},
            None,
        ),
        ("registry_wrong_producer", {"registry": "support/registry_wrong_producer.json"}, ["PCS_REGISTRY_ADMISSION_FAILED"], "science_claim", None, None),
        ("registry_disallowed_status", {"registry": "support/registry_disallowed_status.json"}, ["PCS_REGISTRY_ADMISSION_FAILED"], "science_claim", None, None),
        ("missing_formal_check", {"omit_formal": True}, ["missing_lean_check_result"], "science_claim", None, None),
        ("missing_proof_obligation", {"omit_proof_obligations": True}, ["missing_lean_check_result"], "science_claim", None, None),
        ("missing_lean_check_result", {"omit_lean_check_result": True}, ["missing_lean_check_result"], "science_claim", None, None),
        ("failed_lean_check", {"lean_check_result": "support/lean_check_failed.v0.json"}, ["lean_check_failed"], "science_claim", None, None),
        ("failed_lean_theorem", {"lean_check_result": "support/lean_check_failed.v0.json"}, ["lean_check_failed"], "science_claim", None, None),
        ("lean_release_id_mismatch", {"proof_obligations": "support/proof_obligation_release_mismatch.v0.json"}, ["lean_release_id_mismatch"], "science_claim", None, None),
        ("unauthorized_lean_theorem", {"lean_check_result": "support/lean_unauthorized_theorem.v0.json"}, ["unauthorized_lean_theorem"], "science_claim", None, None),
    ]
    for name, inp, codes, mode, loc, top in invalid_cases:
        body = {
            "case_id": name,
            "expect": "reject",
            "verify_mode": mode,
            "expect_failure_codes": codes,
            "inputs": inp,
        }
        if top:
            body.update(top)
        if loc:
            body["localization"] = loc
        if mode == "release_chain":
            body["explain_requirements"] = explain_full
        elif mode == "science_claim" and name in {
            "missing_handoff",
            "legacy_handoff_in_release_mode",
            "missing_registry",
            "wrong_admission_profile",
            "rejected_certificate",
            "certificate_status_rejected",
            "trace_hash_mismatch",
            "registry_wrong_producer",
            "registry_disallowed_status",
            "missing_proof_obligation",
            "missing_lean_check_result",
            "failed_lean_check",
            "failed_lean_theorem",
            "unauthorized_lean_theorem",
            "lean_release_id_mismatch",
            "missing_formal_check",
        }:
            body["explain_requirements"] = explain_science
            if name in {"missing_proof_obligation", "missing_lean_check_result", "failed_lean_check", "failed_lean_theorem", "unauthorized_lean_theorem", "lean_release_id_mismatch", "missing_formal_check"}:
                body["explain_requirements"] = explain_formal
        write_case(bench_lt, "invalid", name, body)

    bench_formal = ROOT / "benchmarks/admission/formal_trust_kernel"
    bench_formal.mkdir(parents=True, exist_ok=True)
    lt_defaults = {
        "bundle": "${repo}/tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json",
        "handoff": "${repo}/tests/pcs/fixtures/labtrust-release/handoff_to_pf.json",
        "registry": "${repo}/tests/pcs/fixtures/labtrust-release/artifact_registry.json",
        "manifest": "${repo}/tests/pcs/fixtures/labtrust-release/release_manifest.v0.json",
        "artifact_dir": "${repo}/tests/pcs/fixtures/labtrust-release",
        "proof_obligations": "${repo}/tests/pcs/fixtures/labtrust-release/proof_obligation.v0.json",
        "lean_check_result": "${repo}/tests/pcs/fixtures/labtrust-release/lean_check_result.v0.json",
    }
    (bench_formal / "workflow.json").write_text(
        json.dumps(
            {
                "workflow_id": "formal_trust_kernel.enforcement_v0",
                "profile_id": "labtrust_qc_release",
                "fixture_root": "${repo}/benchmarks/admission/labtrust_qc_release",
                "defaults": lt_defaults,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    write_case(
        bench_formal,
        "valid",
        "formal_release_admission",
        {"case_id": "formal_release_admission", "expect": "admit", "verify_mode": "science_claim"},
    )
    support_prefix = "${repo}/benchmarks/admission/labtrust_qc_release/support"
    formal_invalid = [
        ("missing_proof_obligation", {"omit_proof_obligations": True}, ["missing_lean_check_result"]),
        ("missing_lean_check_result", {"omit_lean_check_result": True}, ["missing_lean_check_result"]),
        ("missing_formal_check", {"omit_formal": True}, ["missing_lean_check_result"]),
        ("failed_lean_check", {"lean_check_result": f"{support_prefix}/lean_check_failed.v0.json"}, ["lean_check_failed"]),
        ("failed_lean_theorem", {"lean_check_result": f"{support_prefix}/lean_check_failed.v0.json"}, ["lean_check_failed"]),
        ("unauthorized_lean_theorem", {"lean_check_result": f"{support_prefix}/lean_unauthorized_theorem.v0.json"}, ["unauthorized_lean_theorem"]),
        (
            "lean_release_id_mismatch",
            {"proof_obligations": f"{support_prefix}/proof_obligation_release_mismatch.v0.json"},
            ["lean_release_id_mismatch"],
        ),
    ]
    for name, inp, codes in formal_invalid:
        write_case(
            bench_formal,
            "invalid",
            name,
            {
                "case_id": name,
                "expect": "reject",
                "verify_mode": "science_claim",
                "expect_failure_codes": codes,
                "inputs": inp,
                "explain_requirements": explain_formal,
            },
        )

    bench_tu = ROOT / "benchmarks/admission/tool_use_safety"
    bench_tu.mkdir(parents=True, exist_ok=True)
    (bench_tu / "workflow.json").write_text(
        json.dumps(
            {
                "workflow_id": "agent_tool_use.safety_v0",
                "profile_id": "agent_tool_use_safety",
                "fixture_root": "${repo}/tests/pcs/fixtures/tool-use",
                "defaults": {
                    "bundle": "missing_certificate.json",
                    "registry": "${repo}/tests/pcs/fixtures/labtrust-release/artifact_registry.json",
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    tu_cases = [
        ("valid_profile_shape", "valid_tool_use_profile_shape.json", "admit", "admission_gate", []),
        ("missing_certificate", "missing_certificate.json", "reject", "admission_gate", ["missing_tool_use_certificate"]),
        ("certificate_status_rejected", "rejected_certificate.json", "reject", "admission_gate", ["tool_use_certificate_rejected"]),
        ("trace_hash_mismatch", "trace_hash_mismatch.json", "reject", "admission_gate", ["tool_trace_hash_mismatch"]),
        ("policy_hash_mismatch", "policy_hash_mismatch.json", "reject", "admission_gate", ["policy_hash_mismatch"]),
        ("unauthorized_tool_call", "unauthorized_violation.json", "reject", "admission_gate", ["unauthorized_tool_call_certificate_violation"]),
    ]
    for name, bundle, expect, mode, codes in tu_cases:
        kind = "valid" if expect == "admit" else "invalid"
        body = {"case_id": name, "expect": expect, "verify_mode": mode, "inputs": {"bundle": bundle}}
        if codes:
            body["expect_failure_codes"] = codes
        write_case(bench_tu, kind, name, body)
    write_case(
        bench_tu,
        "invalid",
        "wrong_admission_profile",
        {
            "case_id": "wrong_admission_profile",
            "expect": "reject",
            "verify_mode": "admission_gate",
            "profile_id": "labtrust_qc_release",
            "expect_failure_codes": ["admission_profile_workflow_mismatch"],
            "inputs": {"bundle": "missing_certificate.json"},
        },
    )

    bench_comp = ROOT / "benchmarks/admission/computation_reproducibility"
    bench_comp.mkdir(parents=True, exist_ok=True)
    (bench_comp / "workflow.json").write_text(
        json.dumps(
            {
                "workflow_id": "scientific_computation.reproducibility_v0",
                "profile_id": "scientific_computation_reproducibility",
                "fixture_root": "${repo}/tests/pcs/fixtures/computation-release",
                "defaults": {
                    "bundle": "science_claim_bundle.certified.json",
                    "handoff": "handoff_to_pf.json",
                    "registry": "artifact_registry.json",
                    "manifest": "release_manifest.v0.json",
                    "artifact_dir": ".",
                    "proof_obligations": "proof_obligation.v0.json",
                    "lean_check_result": "lean_check_result.v0.json",
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    write_case(bench_comp, "valid", "release_admission", {"case_id": "release_admission", "expect": "admit", "verify_mode": "science_claim"})
    write_case(bench_comp, "valid", "release_chain", {"case_id": "release_chain", "expect": "admit", "verify_mode": "release_chain"})
    comp_paths = [
        ("missing_dataset_receipt", "${repo}/tests/pcs/fixtures/computation/missing_dataset_receipt.json", ["missing_dataset_receipt"]),
        ("missing_environment_receipt", "${repo}/tests/pcs/fixtures/computation/missing_environment_receipt.json", ["missing_environment_receipt"]),
        ("result_hash_mismatch", "${repo}/tests/pcs/fixtures/computation/result_hash_mismatch.json", ["result_hash_mismatch"]),
        ("missing_code_commit", "${repo}/tests/pcs/fixtures/computation/missing_code_commit.json", ["missing_code_commit"]),
        ("nonzero_exit_code", "${repo}/tests/pcs/fixtures/computation/nonzero_exit_code.json", ["nonzero_exit_code"]),
        ("missing_formal_check", None, ["missing_lean_check_result"]),
    ]
    for name, bundle, codes in comp_paths:
        inp: dict = {"omit_formal": True} if bundle is None else {"bundle": bundle}
        write_case(
            bench_comp,
            "invalid",
            name,
            {
                "case_id": name,
                "expect": "reject",
                "verify_mode": "science_claim",
                "expect_failure_codes": codes,
                "inputs": inp,
            },
        )

    print("OK: benchmark admission cases materialized")
    if quiet:
        return 0
    reg = "tests/pcs/fixtures/labtrust-release/artifact_registry.json"
    print()
    print("pf is not on PATH by default. From repo root, use one of:")
    print('  export PATH="$PWD/scripts:$PATH"   # then: pf benchmark admission ...')
    print("  bash scripts/pf.sh benchmark admission \\")
    print("    --cases benchmarks/admission/labtrust_qc_release \\")
    print(f"    --registry {reg} \\")
    print("    --out benchmark_runs/labtrust_admission --validate")
    print("  bash scripts/pf.sh validate benchmark-bundle benchmark_runs/labtrust_admission")
    print()
    print("Or run the full gate (from repo root):")
    print("  make test-pcs-benchmark")
    print("  bash scripts/pcs-validate-benchmark-bundle.sh")
    print("  cd adapters/pcs && go test . -run TestAdmissionBenchmark -count=1 -timeout 3m")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
