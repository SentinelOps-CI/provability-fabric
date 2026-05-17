// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// CheckAllCertificateStatus verifies every TraceCertificate.status is CertificateChecked.
func CheckAllCertificateStatus(certs []*TraceCertificate) VerificationCheck {
	const id = "certificate_status_checked"
	if len(certs) == 0 {
		return failCheck(id, "TraceCertificate.status is CertificateChecked", ReasonArtifactMissing,
			detailMsg("no trace certificates"))
	}
	for i, cert := range certs {
		if cert == nil {
			return failCheck(id, "TraceCertificate.status is CertificateChecked", ReasonCertificateNotChecked,
				map[string]any{"certificate_index": i, "message": "null certificate"})
		}
		if cert.Status == StatusRejected {
			return failCheck(id, "TraceCertificate.status is CertificateChecked", ReasonCertificateRejected, map[string]any{
				"certificate_index": i,
				"certificate_id":    cert.CertificateID,
				"status":              cert.Status,
			})
		}
		if cert.Status != StatusCertificateChecked {
			return failCheck(id, "TraceCertificate.status is CertificateChecked", ReasonCertificateNotChecked, map[string]any{
				"certificate_index": i,
				"certificate_id":    cert.CertificateID,
				"status":              cert.Status,
			})
		}
	}
	return passCheck(id, "TraceCertificate.status is CertificateChecked", map[string]any{
		"certificate_count": len(certs),
		"status":              StatusCertificateChecked,
	})
}
