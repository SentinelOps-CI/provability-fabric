// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import "strings"

// CheckRuntimeTraceHashPresent verifies RuntimeReceipt.trace_hash is non-empty.
func CheckRuntimeTraceHashPresent(receipt *RuntimeReceipt) VerificationCheck {
	const id = "runtime_trace_hash_present"
	if receipt == nil {
		return failCheck(id, "RuntimeReceipt.trace_hash is non-empty", ReasonTraceHashMissing, detailMsg("runtime receipt missing"))
	}
	if strings.TrimSpace(receipt.TraceHash) == "" {
		return failCheck(id, "RuntimeReceipt.trace_hash is non-empty", ReasonTraceHashMissing, detailMsg("trace_hash is empty"))
	}
	return passCheck(id, "RuntimeReceipt.trace_hash is non-empty", map[string]any{"trace_hash": receipt.TraceHash})
}

// CheckAllTraceHashAlignment verifies every TraceCertificate trace_hash matches the runtime receipt.
func CheckAllTraceHashAlignment(receipt *RuntimeReceipt, certs []*TraceCertificate) VerificationCheck {
	const id = "trace_hash_alignment"
	if receipt == nil || len(certs) == 0 {
		return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", ReasonTraceHashMismatch,
			detailMsg("runtime receipt or trace certificate missing"))
	}
	if strings.TrimSpace(receipt.TraceHash) == "" {
		return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", ReasonTraceHashMissing,
			detailMsg("runtime receipt trace_hash empty"))
	}
	for i, cert := range certs {
		if cert == nil {
			return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", ReasonTraceHashMismatch,
				map[string]any{"certificate_index": i, "message": "null certificate"})
		}
		if strings.TrimSpace(cert.TraceHash) == "" {
			return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", ReasonTraceHashMissing,
				map[string]any{"certificate_index": i, "certificate_id": cert.CertificateID})
		}
		if cert.TraceHash != receipt.TraceHash {
			return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", ReasonTraceHashMismatch, map[string]any{
				"certificate_index":            i,
				"certificate_id":               cert.CertificateID,
				"runtime_receipt_trace_hash":     receipt.TraceHash,
				"trace_certificate_trace_hash": cert.TraceHash,
			})
		}
	}
	return passCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", map[string]any{
		"trace_hash":         receipt.TraceHash,
		"certificate_count": len(certs),
	})
}
