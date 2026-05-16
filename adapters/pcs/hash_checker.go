// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import "strings"

// CheckRuntimeTraceHashPresent verifies RuntimeReceipt.trace_hash is non-empty.
func CheckRuntimeTraceHashPresent(receipt *RuntimeReceipt) VerificationCheck {
	const id = "pcs.runtime.trace_hash_present"
	if receipt == nil {
		return failCheck(id, "RuntimeReceipt.trace_hash is present", "runtime receipt missing")
	}
	if strings.TrimSpace(receipt.TraceHash) == "" {
		return failCheck(id, "RuntimeReceipt.trace_hash is present", "trace_hash is empty")
	}
	return passCheck(id, "RuntimeReceipt.trace_hash is present", receipt.TraceHash)
}

// CheckTraceHashMatch verifies TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash.
func CheckTraceHashMatch(receipt *RuntimeReceipt, cert *TraceCertificate) VerificationCheck {
	const id = "pcs.certificate.trace_hash_match"
	if receipt == nil || cert == nil {
		return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", "required artifacts missing")
	}
	if strings.TrimSpace(receipt.TraceHash) == "" || strings.TrimSpace(cert.TraceHash) == "" {
		return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", "trace_hash missing on receipt or certificate")
	}
	if receipt.TraceHash != cert.TraceHash {
		return failCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash",
			"mismatch: receipt="+receipt.TraceHash+" certificate="+cert.TraceHash)
	}
	return passCheck(id, "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash", receipt.TraceHash)
}
