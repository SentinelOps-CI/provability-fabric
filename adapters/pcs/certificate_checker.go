// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

// CheckCertificateStatus verifies TraceCertificate.status is CertificateChecked.
func CheckCertificateStatus(cert *TraceCertificate) VerificationCheck {
	const id = "pcs.certificate.status_checked"
	if cert == nil {
		return failCheck(id, "TraceCertificate.status is CertificateChecked", "trace certificate missing")
	}
	if cert.Status == StatusRejected {
		return failCheck(id, "TraceCertificate.status is CertificateChecked", "certificate status is Rejected")
	}
	if cert.Status != StatusCertificateChecked {
		return failCheck(id, "TraceCertificate.status is CertificateChecked", "status="+cert.Status)
	}
	return passCheck(id, "TraceCertificate.status is CertificateChecked", cert.Status)
}
