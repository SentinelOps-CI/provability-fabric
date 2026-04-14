package main

import (
	"encoding/base64"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

// TestDSSEFixtureVerify loads tests/fixtures/crypto and verifies the sample DSSE
// envelope signature with the fixture public key (cross-language fixture contract).
func TestDSSEFixtureVerify(t *testing.T) {
	// From evidence-service dir, fixtures are ../../tests/fixtures/crypto
	base := filepath.Join("..", "..", "tests", "fixtures", "crypto")
	pemPath := filepath.Join(base, "ed25519_public.pem")
	envPath := filepath.Join(base, "dsse_sample_envelope.json")
	pemB, err := os.ReadFile(pemPath)
	if err != nil {
		t.Skipf("fixture not found (run from repo root or set fixtures path): %v", err)
		return
	}
	envB, err := os.ReadFile(envPath)
	if err != nil {
		t.Skipf("envelope fixture not found: %v", err)
		return
	}
	var envelope struct {
		Payload    string `json:"payload"`
		Signatures []struct {
			Sig string `json:"sig"`
		} `json:"signatures"`
	}
	if err := json.Unmarshal(envB, &envelope); err != nil {
		t.Fatalf("parse envelope: %v", err)
	}
	if len(envelope.Signatures) == 0 {
		t.Fatal("no signature in envelope")
	}
	payloadBytes, err := base64.StdEncoding.DecodeString(envelope.Payload)
	if err != nil {
		t.Fatalf("decode payload: %v", err)
	}
	sigBytes, err := base64.StdEncoding.DecodeString(envelope.Signatures[0].Sig)
	if err != nil {
		t.Fatalf("decode sig: %v", err)
	}
	pub, err := loadEd25519PublicKeyFromPEMString(string(pemB))
	if err != nil {
		t.Fatalf("load public key: %v", err)
	}
	ok, reason := verifySignature(payloadBytes, envelope.Signatures[0].Sig, "", string(pemB))
	if !ok {
		t.Errorf("verify fixture signature: %s", reason)
	}
	_ = pub
	_ = sigBytes
}
