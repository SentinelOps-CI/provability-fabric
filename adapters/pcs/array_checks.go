// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// checkRuntimeReceiptPresent enforces pcs-core v0.1: exactly one runtime receipt in runtime_receipts[].
func checkRuntimeReceiptPresent(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "runtime_receipt_present"
	n := 0
	if bundle != nil {
		n = len(bundle.RuntimeReceipts)
	}
	switch {
	case n == 0:
		return failCheck(id, "Exactly one RuntimeReceipt exists in runtime_receipts",
			ReasonArtifactMissing, map[string]any{"present": false, "artifact": "runtime_receipts", "count": 0})
	case n > 1:
		return failCheck(id, "Exactly one RuntimeReceipt exists in runtime_receipts",
			ReasonRuntimeReceiptCount, map[string]any{"present": true, "artifact": "runtime_receipts", "count": n, "max_allowed": 1})
	case bundle.PrimaryRuntimeReceipt() == nil:
		return failCheck(id, "Exactly one RuntimeReceipt exists in runtime_receipts",
			ReasonArtifactMissing, map[string]any{"present": false, "artifact": "runtime_receipts", "count": 1, "message": "null receipt"})
	default:
		return passCheck(id, "Exactly one RuntimeReceipt exists in runtime_receipts",
			map[string]any{"present": true, "artifact": "runtime_receipts", "count": 1})
	}
}

// checkTraceCertificatesPresent enforces certified bundles include at least one certificate.
func checkTraceCertificatesPresent(bundle *ScienceClaimBundle) VerificationCheck {
	const id = "trace_certificate_present"
	n := 0
	if bundle != nil {
		n = len(bundle.Certificates)
	}
	if n == 0 {
		return failCheck(id, "At least one TraceCertificate exists in certificates",
			ReasonArtifactMissing, map[string]any{"present": false, "artifact": "certificates", "count": 0})
	}
	return passCheck(id, "At least one TraceCertificate exists in certificates",
		map[string]any{"present": true, "artifact": "certificates", "count": n})
}
