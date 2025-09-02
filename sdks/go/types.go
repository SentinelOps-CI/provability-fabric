// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package sentinelops

import (
	"time"
)

// Policy types
type PolicyCompileRequest struct {
	English   string            `json:"english"`
	PolicyID  string            `json:"policy_id,omitempty"`
	Version   string            `json:"version,omitempty"`
	Metadata  map[string]string `json:"metadata,omitempty"`
}

type PolicyCompileResponse struct {
	ActionDSL   interface{}  `json:"actionDsl"`
	Diagnostics []Diagnostic `json:"diagnostics"`
	PolicyHash  string       `json:"policy_hash"`
	Timestamp   time.Time    `json:"timestamp"`
}

type PolicyBuildRequest struct {
	PolicyHash  string                 `json:"policy_hash"`
	ActionDSL   map[string]interface{} `json:"action_dsl"`
	ProofHash   string                 `json:"proof_hash"`
	Metadata    map[string]string      `json:"metadata,omitempty"`
	SigningKey  string                 `json:"signing_key,omitempty"`
}

type PolicyBuildResponse struct {
	BuildID       string                 `json:"build_id"`
	DFAHash       string                 `json:"dfa_hash"`
	AutomataHash  string                 `json:"automata_hash"`
	LabelerHash   string                 `json:"labeler_hash"`
	ProofInputs   map[string]interface{} `json:"proof_inputs"`
	Artifacts     []string               `json:"artifacts"`
	Signature     string                 `json:"signature,omitempty"`
	Status        string                 `json:"status"`
	Timestamp     time.Time              `json:"timestamp"`
	ExecutionTime int                    `json:"execution_time_ms"`
}

type ProofRunRequest struct {
	PolicyHash   string                 `json:"policy_hash"`
	ActionDSL    interface{}            `json:"action_dsl"`
	ProofInputs  map[string]interface{} `json:"proof_inputs,omitempty"`
	UseMorph     bool                   `json:"use_morph,omitempty"`
	MorphShards  int                    `json:"morph_shards,omitempty"`
	Metadata     map[string]string      `json:"metadata,omitempty"`
}

type ProofRunResponse struct {
	ProofHash     string       `json:"proof_hash"`
	Status        string       `json:"status"`
	Shards        []ProofShard `json:"shards,omitempty"`
	Artifacts     []string     `json:"artifacts"`
	Diagnostics   []Diagnostic `json:"diagnostics"`
	Timestamp     time.Time    `json:"timestamp"`
	ExecutionTime int          `json:"execution_time_ms"`
}

type ProofShard struct {
	ShardID       string `json:"shard_id"`
	Status        string `json:"status"`
	MorphVMID     string `json:"morphvm_id,omitempty"`
	EnvSnapshot   string `json:"env_snapshot,omitempty"`
	ProofHash     string `json:"proof_hash,omitempty"`
	ExecutionTime int    `json:"execution_time_ms"`
}

type Diagnostic struct {
	Level   string `json:"level"`
	Message string `json:"message"`
	File    string `json:"file,omitempty"`
	Line    int    `json:"line,omitempty"`
	Column  int    `json:"column,omitempty"`
}

type DeployRequest struct {
	PolicyHash   string `json:"policy_hash"`
	AutomataHash string `json:"automata_hash"`
	Epoch        int    `json:"epoch"`
}

type DeployResponse struct {
	PolicyHash   string    `json:"policy_hash"`
	AutomataHash string    `json:"automata_hash"`
	Epoch        int       `json:"epoch"`
	Status       string    `json:"status"`
	DeployedAt   time.Time `json:"deployed_at"`
}

// Certificate types
type CertV1 struct {
	BundleID       string                 `json:"bundle_id"`
	PolicyHash     string                 `json:"policy_hash"`
	ProofHash      string                 `json:"proof_hash"`
	AutomataHash   string                 `json:"automata_hash"`
	LabelerHash    string                 `json:"labeler_hash"`
	NIClaim        string                 `json:"ni_claim"`
	NIMonitor      string                 `json:"ni_monitor"`
	SidecarBuild   string                 `json:"sidecar_build"`
	AttestationRef string                 `json:"attestation_ref,omitempty"`
	Extensions     map[string]interface{} `json:"extensions,omitempty"`
	Timestamp      time.Time              `json:"timestamp"`
	TenantID       string                 `json:"tenant_id"`
	SessionID      string                 `json:"session_id"`
	Morph          *MorphInfo             `json:"morph,omitempty"`
}

type MorphInfo struct {
	EnvSnapshotDigest string `json:"env_snapshot_digest"`
	BranchID          string `json:"branch_id"`
	BaseImage         string `json:"base_image"`
	MorphVMID         string `json:"morphvm_id,omitempty"`
}

type CertSearchRequest struct {
	TenantID   string     `json:"tenant_id,omitempty"`
	PolicyHash string     `json:"policy_hash,omitempty"`
	SessionID  string     `json:"session_id,omitempty"`
	StartTime  *time.Time `json:"start_time,omitempty"`
	EndTime    *time.Time `json:"end_time,omitempty"`
	NIMonitor  string     `json:"ni_monitor,omitempty"`
	Limit      int        `json:"limit,omitempty"`
	Offset     int        `json:"offset,omitempty"`
}

type CertSearchResponse struct {
	Certificates []CertV1 `json:"certificates"`
	Total        int      `json:"total"`
	Limit        int      `json:"limit"`
	Offset       int      `json:"offset"`
}

// Replay types
type ReplayConfig struct {
	Seed            int     `json:"seed,omitempty"`
	Locale          string  `json:"locale,omitempty"`
	Timezone        string  `json:"timezone,omitempty"`
	ChunkSize       int     `json:"chunk_size,omitempty"`
	FlushCadenceMs  int     `json:"flush_cadence_ms,omitempty"`
	PaddingPolicy   string  `json:"padding_policy,omitempty"`
	DriftThreshold  float64 `json:"drift_threshold,omitempty"`
}

type ReplayRequest struct {
	DecisionID string                 `json:"decision_id"`
	TraceFile  string                 `json:"trace_file,omitempty"`
	Config     *ReplayConfig          `json:"config,omitempty"`
	UseMorph   bool                   `json:"use_morph,omitempty"`
	Metadata   map[string]string      `json:"metadata,omitempty"`
}

type ReplayResponse struct {
	JobID     string    `json:"job_id"`
	Status    string    `json:"status"`
	StartedAt time.Time `json:"started_at"`
}

type ReplayStatus struct {
	JobID           string     `json:"job_id"`
	Status          string     `json:"status"`
	Progress        float64    `json:"progress"`
	LowViewMatchPct float64    `json:"low_view_match_pct"`
	Outputs         []string   `json:"outputs"`
	Artifacts       []string   `json:"artifacts"`
	StartedAt       time.Time  `json:"started_at"`
	CompletedAt     *time.Time `json:"completed_at,omitempty"`
	ExecutionTime   int        `json:"execution_time_ms"`
	DriftDetected   bool       `json:"drift_detected"`
	ErrorMessage    string     `json:"error_message,omitempty"`
}

// Epoch types
type EpochRotateResponse struct {
	OldEpoch   int       `json:"old_epoch"`
	NewEpoch   int       `json:"new_epoch"`
	RotatedAt  time.Time `json:"rotated_at"`
	RotatedBy  string    `json:"rotated_by"`
	Reason     string    `json:"reason,omitempty"`
}

// Health and monitoring types
type HealthResponse struct {
	Status    string                 `json:"status"`
	Service   string                 `json:"service"`
	Version   string                 `json:"version"`
	Timestamp time.Time              `json:"timestamp"`
	Services  map[string]interface{} `json:"services"`
}

type SLOResponse struct {
	Latency                map[string]float64 `json:"latency"`
	TPS                    float64            `json:"tps"`
	ErrorRate              float64            `json:"error_rate"`
	CertValidationFailures int                `json:"cert_validation_failures"`
	SidecarDecisionLatency float64            `json:"sidecar_decision_latency"`
	EgressWriteLatency     float64            `json:"egress_write_latency"`
	Timestamp              time.Time          `json:"timestamp"`
}

// Workflow result
type WorkflowResult struct {
	PolicyHash   string `json:"policy_hash"`
	ProofHash    string `json:"proof_hash"`
	AutomataHash string `json:"automata_hash"`
	Epoch        int    `json:"epoch"`
	Status       string `json:"status"`
}