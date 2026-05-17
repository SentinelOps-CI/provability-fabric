// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"os"
	"strings"
)

// VerifiedInput captures the exact ScienceClaimBundle inputs PF verified before signing.
type VerifiedInput struct {
	BundleHash    string `json:"bundle_hash"`
	CertificateID string `json:"certificate_id"`
	TraceHash     string `json:"trace_hash"`
}

// BuildVerifiedInput fingerprints the certified bundle used for verify/sign.
func BuildVerifiedInput(bundle *ScienceClaimBundle, bundlePath string) (VerifiedInput, error) {
	if bundle == nil {
		return VerifiedInput{}, fmt.Errorf("bundle is nil")
	}
	hash, err := bundleInputHash(bundle, bundlePath)
	if err != nil {
		return VerifiedInput{}, err
	}
	certID, traceHash, err := primaryCertAndTrace(bundle)
	if err != nil {
		return VerifiedInput{}, err
	}
	return VerifiedInput{
		BundleHash:    hash,
		CertificateID: certID,
		TraceHash:     traceHash,
	}, nil
}

func bundleInputHash(bundle *ScienceClaimBundle, bundlePath string) (string, error) {
	if strings.TrimSpace(bundlePath) != "" {
		resolved, err := ResolveArtifactPath(bundlePath)
		if err != nil {
			return "", err
		}
		data, err := os.ReadFile(resolved)
		if err != nil {
			return "", err
		}
		return "sha256:" + SHA256Hex(data), nil
	}
	payload, err := CanonicalJSON(bundle)
	if err != nil {
		return "", err
	}
	return "sha256:" + SHA256Hex(payload), nil
}

func primaryCertAndTrace(bundle *ScienceClaimBundle) (certID, traceHash string, err error) {
	if len(bundle.Certificates) == 0 || bundle.Certificates[0] == nil {
		return "", "", fmt.Errorf("certificates[0] is required for release verification")
	}
	certID = strings.TrimSpace(bundle.Certificates[0].CertificateID)
	if certID == "" {
		return "", "", fmt.Errorf("certificates[0].certificate_id is empty")
	}
	receipt := bundle.PrimaryRuntimeReceipt()
	if receipt == nil {
		return "", "", fmt.Errorf("runtime_receipts[0] is required for release verification")
	}
	traceHash = strings.TrimSpace(receipt.TraceHash)
	if traceHash == "" {
		return "", "", fmt.Errorf("runtime_receipts[0].trace_hash is empty")
	}
	return certID, traceHash, nil
}

// CertificateIDFromVerificationResult reads certificate_refs[0] from evidence_refs_complete check details.
func CertificateIDFromVerificationResult(result VerificationResult) (string, error) {
	for _, c := range result.Checks {
		if c.CheckID != "evidence_refs_complete" || c.Status != CheckPassed {
			continue
		}
		refs := stringSliceFromDetails(c.Details["certificate_refs"])
		if len(refs) == 0 {
			break
		}
		return refs[0], nil
	}
	if result.VerifiedInput != nil && strings.TrimSpace(result.VerifiedInput.CertificateID) != "" {
		return result.VerifiedInput.CertificateID, nil
	}
	return "", fmt.Errorf("certificate id not found in verification result")
}

func stringSliceFromDetails(v any) []string {
	switch t := v.(type) {
	case []string:
		return t
	case []any:
		out := make([]string, 0, len(t))
		for _, item := range t {
			if s, ok := item.(string); ok {
				out = append(out, s)
			}
		}
		return out
	default:
		return nil
	}
}

func verifiedInputsEqual(a, b VerifiedInput) bool {
	return a.BundleHash == b.BundleHash &&
		a.CertificateID == b.CertificateID &&
		a.TraceHash == b.TraceHash
}

// AssertReleaseArtifactChain checks certified bundle, verification result, and signed wrapper align.
func AssertReleaseArtifactChain(certified *ScienceClaimBundle, result VerificationResult, signed *SignedScienceClaimBundle) error {
	if certified == nil || signed == nil || signed.ScienceClaimBundle == nil {
		return fmt.Errorf("certified bundle and signed.science_claim_bundle are required")
	}
	certID := strings.TrimSpace(certified.Certificates[0].CertificateID)
	vrCert, err := CertificateIDFromVerificationResult(result)
	if err != nil {
		return err
	}
	embeddedCert := strings.TrimSpace(signed.ScienceClaimBundle.Certificates[0].CertificateID)
	if certID != vrCert || certID != embeddedCert {
		return fmt.Errorf("certificate_id mismatch: bundle=%q verification=%q signed=%q", certID, vrCert, embeddedCert)
	}
	if result.VerifiedInput != nil {
		if result.VerifiedInput.CertificateID != certID {
			return fmt.Errorf("verified_input.certificate_id %q != bundle %q",
				result.VerifiedInput.CertificateID, certID)
		}
	}
	if signed.SignedInputBundleHash != "" && result.VerifiedInput != nil {
		if signed.SignedInputBundleHash != result.VerifiedInput.BundleHash {
			return fmt.Errorf("signed_input_bundle_hash %q != verified_input.bundle_hash %q",
				signed.SignedInputBundleHash, result.VerifiedInput.BundleHash)
		}
	}
	return AssertBundlesCanonicallyEqual(certified, signed.ScienceClaimBundle)
}
