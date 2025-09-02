# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

from typing import List, Optional, Dict, Any, Union
from pydantic import BaseModel
from datetime import datetime

class PolicyCompileRequest(BaseModel):
    english: str
    policy_id: Optional[str] = None
    version: Optional[str] = "1.0.0"
    metadata: Optional[Dict[str, str]] = None

class Diagnostic(BaseModel):
    level: str  # "error" | "warning" | "info"
    message: str
    file: Optional[str] = None
    line: Optional[int] = None
    column: Optional[int] = None

class PolicyCompileResponse(BaseModel):
    actionDsl: Dict[str, Any]
    diagnostics: List[Diagnostic]
    policy_hash: str
    timestamp: datetime

class PolicyBuildRequest(BaseModel):
    policy_hash: str
    action_dsl: Dict[str, Any]
    proof_hash: str
    metadata: Optional[Dict[str, str]] = None
    signing_key: Optional[str] = None

class PolicyBuildResponse(BaseModel):
    build_id: str
    dfa_hash: str
    automata_hash: str
    labeler_hash: str
    proof_inputs: Dict[str, Any]
    artifacts: List[str]
    signature: Optional[str] = None
    status: str
    timestamp: datetime
    execution_time_ms: int

class ProofShard(BaseModel):
    shard_id: str
    status: str
    morphvm_id: Optional[str] = None
    env_snapshot: Optional[str] = None
    proof_hash: Optional[str] = None
    execution_time_ms: int

class ProofRunRequest(BaseModel):
    policy_hash: str
    action_dsl: Any
    proof_inputs: Optional[Dict[str, Any]] = None
    use_morph: Optional[bool] = False
    morph_shards: Optional[int] = None
    metadata: Optional[Dict[str, str]] = None

class ProofRunResponse(BaseModel):
    proof_hash: str
    status: str
    shards: Optional[List[ProofShard]] = None
    artifacts: List[str]
    diagnostics: List[Diagnostic]
    timestamp: datetime
    execution_time_ms: int

class DeployRequest(BaseModel):
    policy_hash: str
    automata_hash: str
    epoch: int

class MorphInfo(BaseModel):
    env_snapshot_digest: str
    branch_id: str
    base_image: str
    morphvm_id: Optional[str] = None

class CertV1(BaseModel):
    bundle_id: str
    policy_hash: str
    proof_hash: str
    automata_hash: str
    labeler_hash: str
    ni_claim: str
    ni_monitor: str  # "inapplicable" | "accept" | "reject" | "error"
    sidecar_build: str
    attestation_ref: Optional[str] = None
    extensions: Optional[Dict[str, Any]] = None
    timestamp: datetime
    tenant_id: str
    session_id: str
    morph: Optional[MorphInfo] = None

class CertSearchRequest(BaseModel):
    tenant_id: Optional[str] = None
    policy_hash: Optional[str] = None
    session_id: Optional[str] = None
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None
    ni_monitor: Optional[str] = None
    limit: Optional[int] = 100
    offset: Optional[int] = 0

class CertSearchResponse(BaseModel):
    certificates: List[CertV1]
    total: int
    limit: int
    offset: int

class ReplayConfig(BaseModel):
    seed: Optional[int] = 42
    locale: Optional[str] = "C"
    timezone: Optional[str] = "UTC"
    chunk_size: Optional[int] = 4096
    flush_cadence_ms: Optional[int] = 100
    padding_policy: Optional[str] = "fixed"
    drift_threshold: Optional[float] = 0.001

class ReplayRequest(BaseModel):
    decision_id: str
    trace_file: Optional[str] = None
    config: Optional[ReplayConfig] = None
    use_morph: Optional[bool] = False
    metadata: Optional[Dict[str, str]] = None

class ReplayResponse(BaseModel):
    job_id: str
    status: str
    started_at: datetime

class ReplayStatus(BaseModel):
    job_id: str
    status: str  # "running" | "completed" | "failed"
    progress: float
    low_view_match_pct: float
    outputs: List[str]
    artifacts: List[str]
    started_at: datetime
    completed_at: Optional[datetime] = None
    execution_time_ms: int
    drift_detected: bool
    error_message: Optional[str] = None

class CompliancePacket(BaseModel):
    packet_id: str
    generated_at: datetime
    tenant_id: str
    policy_hash: str
    start_time: datetime
    end_time: datetime
    certificates: List[CertV1]
    audit_proof: str
    replay_results: List[str]
    conformance: str

class PlatformHealth(BaseModel):
    status: str
    service: str
    version: str
    timestamp: datetime
    services: Dict[str, Any]

class SLOMetrics(BaseModel):
    latency: Dict[str, float]  # p50, p95, p99
    tps: float
    error_rate: float
    cert_validation_failures: int
    sidecar_decision_latency: float
    egress_write_latency: float
    timestamp: datetime