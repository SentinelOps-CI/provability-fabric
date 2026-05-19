// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
)

// HydrateComputationBundleFromDir loads sidecar computation artifacts and normalizes canonical pcs-core fields.
func HydrateComputationBundleFromDir(bundle *ScienceClaimBundle, artifactDir string) error {
	if bundle == nil {
		return nil
	}
	artifactDir = strings.TrimSpace(artifactDir)
	if artifactDir == "" {
		NormalizeComputationBundle(bundle)
		return nil
	}
	if bundle.DatasetReceipt == nil {
		if ds, err := loadComputationArtifactFile[DatasetReceiptV0](artifactDir, "dataset_receipt.json"); err != nil {
			return err
		} else if ds != nil {
			bundle.DatasetReceipt = ds
		}
	}
	if bundle.EnvironmentReceipt == nil {
		if env, err := loadComputationArtifactFile[EnvironmentReceiptV0](artifactDir, "environment_receipt.json"); err != nil {
			return err
		} else if env != nil {
			bundle.EnvironmentReceipt = env
		}
	}
	if bundle.ComputationRunReceipt == nil {
		if run, err := loadComputationArtifactFile[ComputationRunReceiptV0](artifactDir, "computation_run_receipt.json"); err != nil {
			return err
		} else if run != nil {
			bundle.ComputationRunReceipt = run
		}
	}
	if bundle.ResultArtifact == nil {
		if res, err := loadComputationArtifactFile[ResultArtifactV0](artifactDir, "result_artifact.json"); err != nil {
			return err
		} else if res != nil {
			bundle.ResultArtifact = res
		}
	}
	if bundle.ComputationWitness == nil {
		if witness, err := loadComputationArtifactFile[ComputationWitnessV0](artifactDir, "computation_witness.json"); err != nil {
			return err
		} else if witness != nil {
			bundle.ComputationWitness = witness
		}
	}
	NormalizeComputationBundle(bundle)
	return nil
}

func loadComputationArtifactFile[T any](dir, name string) (*T, error) {
	path := filepath.Join(dir, name)
	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, nil
		}
		return nil, err
	}
	var out T
	if err := json.Unmarshal(data, &out); err != nil {
		return nil, err
	}
	return &out, nil
}

// NormalizeComputationBundle maps pcs-core canonical field names to PF admission projection fields.
func NormalizeComputationBundle(bundle *ScienceClaimBundle) {
	if bundle == nil {
		return
	}
	if strings.TrimSpace(bundle.WorkflowID) == "" && bundle.VerificationPolicy != nil {
		if strings.HasPrefix(strings.TrimSpace(bundle.VerificationPolicy.PolicyID), "scientific_computation") {
			bundle.WorkflowID = workflowScientificComputationRepro
		}
	}
	if ds := bundle.DatasetReceipt; ds != nil {
		if strings.TrimSpace(ds.ReceiptID) == "" {
			ds.ReceiptID = strings.TrimSpace(ds.DatasetID)
		}
	}
	if env := bundle.EnvironmentReceipt; env != nil {
		if strings.TrimSpace(env.Digest) == "" {
			env.Digest = firstNonEmpty(env.SignatureOrDigest, env.EnvironmentID)
		}
		if strings.TrimSpace(env.ReceiptID) == "" {
			env.ReceiptID = strings.TrimSpace(env.EnvironmentID)
		}
	}
	if run := bundle.ComputationRunReceipt; run != nil {
		if bundle.DatasetReceipt != nil && strings.TrimSpace(run.DatasetAggregateHash) == "" {
			run.DatasetAggregateHash = bundle.DatasetReceipt.AggregateHash
		}
		if bundle.EnvironmentReceipt != nil && strings.TrimSpace(run.EnvironmentDigest) == "" {
			run.EnvironmentDigest = bundle.EnvironmentReceipt.Digest
		}
	}
	if res := bundle.ResultArtifact; res != nil {
		if strings.TrimSpace(res.ArtifactID) == "" {
			res.ArtifactID = strings.TrimSpace(res.ResultID)
		}
		if strings.TrimSpace(res.ContentHash) == "" {
			res.ContentHash = strings.TrimSpace(res.SHA256)
		}
	}
	if witness := bundle.ComputationWitness; witness != nil {
		if strings.TrimSpace(witness.CertificateID) == "" {
			witness.CertificateID = strings.TrimSpace(witness.WitnessID)
		}
		if strings.TrimSpace(witness.DatasetAggregateHash) == "" {
			witness.DatasetAggregateHash = strings.TrimSpace(witness.DatasetHash)
		}
		if strings.TrimSpace(witness.EnvironmentDigest) == "" {
			witness.EnvironmentDigest = strings.TrimSpace(witness.EnvironmentHash)
		}
	}
}

func firstNonEmpty(values ...string) string {
	for _, v := range values {
		if strings.TrimSpace(v) != "" {
			return strings.TrimSpace(v)
		}
	}
	return ""
}

func isComputationReleaseBundle(bundle *ScienceClaimBundle) bool {
	if bundle == nil {
		return false
	}
	if strings.TrimSpace(bundle.WorkflowID) == workflowScientificComputationRepro {
		return true
	}
	if bundle.VerificationPolicy != nil &&
		strings.TrimSpace(bundle.VerificationPolicy.PolicyID) == workflowScientificComputationRepro {
		return true
	}
	return inferComputationWorkflow(bundle)
}
