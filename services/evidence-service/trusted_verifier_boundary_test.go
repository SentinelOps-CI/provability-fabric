// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/x509"
	"encoding/base64"
	"encoding/json"
	"encoding/pem"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
)

// signedValidationCertificate creates synthetic certificate claims and an
// Ed25519 signature over the exact canonical payload the service verifies.
func signedValidationCertificate(t *testing.T, private ed25519.PrivateKey) json.RawMessage {
	t.Helper()
	claims := map[string]interface{}{
		"bundle_id":           "fixture-bundle",
		"policy_hash":         "fixture-policy",
		"proof_hash":          "fixture-proof",
		"automata_hash":       "fixture-automata",
		"labeler_hash":        "fixture-labeler",
		"ni_monitor":          "accept",
		"permit_decision":     "permit",
		"path_witness_ok":     true,
		"label_derivation_ok": true,
		"epoch":               float64(1),
		"egress_profile":      "fixture-profile",
	}
	canonical, err := marshalCanonicalJSON(claims)
	if err != nil {
		t.Fatalf("canonicalize fixture: %v", err)
	}
	claims["sig"] = base64.StdEncoding.EncodeToString(ed25519.Sign(private, canonical))
	raw, err := json.Marshal(claims)
	if err != nil {
		t.Fatalf("encode fixture: %v", err)
	}
	return raw
}

func postEvidenceValidation(t *testing.T, service *EvidenceService, raw json.RawMessage, pemPub string) (int, []byte) {
	t.Helper()
	gin.SetMode(gin.TestMode)
	router := gin.New()
	router.POST("/api/v1/evidence/validate", service.verifyCertHandler)
	requestBody, err := json.Marshal(CertValidationRequest{Raw: raw, PEMPub: pemPub})
	if err != nil {
		t.Fatal(err)
	}
	request := httptest.NewRequest(http.MethodPost, "/api/v1/evidence/validate", bytes.NewReader(requestBody))
	request.Header.Set("Content-Type", "application/json")
	response := httptest.NewRecorder()
	router.ServeHTTP(response, request)
	return response.Code, response.Body.Bytes()
}

func parseEvidenceValidation(t *testing.T, status int, body []byte) CertValidationResponse {
	t.Helper()
	if status != http.StatusOK {
		t.Fatalf("unexpected HTTP %d: %s", status, body)
	}
	var result CertValidationResponse
	if err := json.Unmarshal(body, &result); err != nil {
		t.Fatalf("decode validation response: %v", err)
	}
	if !result.SchemaValid || !result.SignatureChecked {
		t.Fatalf("well-formed signed fixture was not evaluated: %+v", result)
	}
	return result
}

func TestEvidenceVerificationDoesNotTrustCallerSuppliedPEM(t *testing.T) {
	attackerPub, attackerPrivate, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	trustedPub, _, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	payload := signedValidationCertificate(t, attackerPrivate)
	der, err := x509.MarshalPKIXPublicKey(attackerPub)
	if err != nil {
		t.Fatal(err)
	}
	attackerPEM := string(pem.EncodeToMemory(&pem.Block{Type: "PUBLIC KEY", Bytes: der}))

	for _, service := range []*EvidenceService{
		{},
		{trustedJWKSKeys: []ed25519.PublicKey{trustedPub}},
	} {
		status, body := postEvidenceValidation(t, service, payload, attackerPEM)
		if status != http.StatusBadRequest || !strings.Contains(string(body), "UNTRUSTED_VERIFIER_KEY") {
			t.Fatalf("caller-provided verifier was accepted: HTTP %d: %s", status, body)
		}
	}

	// The same attacker-signed payload without a supplied PEM is not
	// authenticated by an unrelated operator-owned verification key.
	status, body := postEvidenceValidation(t, &EvidenceService{
		trustedJWKSKeys: []ed25519.PublicKey{trustedPub},
	}, payload, "")
	result := parseEvidenceValidation(t, status, body)
	if result.SignatureValid {
		t.Fatalf("untrusted issuer accepted as trusted evidence: %+v", result)
	}

	status, body = postEvidenceValidation(t, &EvidenceService{}, payload, "")
	result = parseEvidenceValidation(t, status, body)
	if result.SignatureValid || len(result.Errors) != 1 || result.Errors[0] != "trusted_verifier_unavailable" {
		t.Fatalf("missing trusted root did not fail closed: %+v", result)
	}
}

func TestEvidenceVerificationBindsTrustRootToCertificateBytes(t *testing.T) {
	trustedPub, trustedPrivate, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	service := &EvidenceService{trustedJWKSKeys: []ed25519.PublicKey{trustedPub}}
	payload := signedValidationCertificate(t, trustedPrivate)

	status, body := postEvidenceValidation(t, service, payload, "")
	result := parseEvidenceValidation(t, status, body)
	if !result.SignatureValid {
		t.Fatalf("legitimate trusted signature rejected: %+v", result)
	}

	var tampered map[string]interface{}
	if err := json.Unmarshal(payload, &tampered); err != nil {
		t.Fatal(err)
	}
	tampered["policy_hash"] = "replaced-policy"
	mutated, err := json.Marshal(tampered)
	if err != nil {
		t.Fatal(err)
	}
	status, body = postEvidenceValidation(t, service, mutated, "")
	result = parseEvidenceValidation(t, status, body)
	if result.SignatureValid {
		t.Fatalf("certificate field tampering accepted: %+v", result)
	}

	tampered["sig"] = "malformed-signature!"
	malformed, err := json.Marshal(tampered)
	if err != nil {
		t.Fatal(err)
	}
	status, body = postEvidenceValidation(t, service, malformed, "")
	result = parseEvidenceValidation(t, status, body)
	if result.SignatureValid || len(result.Errors) != 1 || result.Errors[0] != "sig_decode_error" {
		t.Fatalf("invalid signature encoding accepted: %+v", result)
	}
}
