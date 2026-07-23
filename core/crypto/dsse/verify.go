// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package dsse

import (
	"crypto/ed25519"
	"crypto/x509"
	"encoding/base64"
	"encoding/json"
	"encoding/pem"
	"fmt"
	"io"
	"net/http"
	"os"
	"sort"
	"strings"
	"time"
)

const (
	EnvTrustRootPEM  = "PF_TRUST_ROOT_PEM"
	EnvJWKSURL       = "PF_JWKS_URL"
	EnvEnforceDSSE   = "PF_ENFORCE_DSSE"
	AccessReceiptType = "application/vnd.provability-fabric.access-receipt"
)

// Envelope is a DSSE signing envelope.
type Envelope struct {
	PayloadType string          `json:"payloadType"`
	Payload     string          `json:"payload"`
	Signatures  []Signature     `json:"signatures"`
}

// Signature is a single DSSE signature entry.
type Signature struct {
	KeyID string `json:"keyid"`
	Sig   string `json:"sig"`
	Alg   string `json:"alg,omitempty"`
}

// VerifyResult is the outcome of verification.
type VerifyResult struct {
	Valid  bool   `json:"valid"`
	Reason string `json:"reason,omitempty"`
}

// EnforceDSSE returns true when DSSE verification must fail closed.
// Default is enforce (unset / empty). Opt out only with PF_ENFORCE_DSSE=0 or false.
func EnforceDSSE() bool {
	v := strings.TrimSpace(os.Getenv(EnvEnforceDSSE))
	if v == "0" || strings.EqualFold(v, "false") {
		return false
	}
	return true
}

// TrustRootConfigured reports whether a trust root is available.
func TrustRootConfigured() bool {
	pem := strings.TrimSpace(os.Getenv(EnvTrustRootPEM))
	if pem == "" {
		return false
	}
	if _, err := os.Stat(pem); err == nil {
		return true
	}
	return strings.Contains(pem, "BEGIN PUBLIC KEY") || strings.Contains(pem, "BEGIN PRIVATE KEY")
}

// LoadTrustRootPEM loads PEM from env (file path or inline content).
func LoadTrustRootPEM() ([]byte, error) {
	raw := strings.TrimSpace(os.Getenv(EnvTrustRootPEM))
	if raw == "" {
		return nil, fmt.Errorf("trust root not configured (%s unset)", EnvTrustRootPEM)
	}
	if _, err := os.Stat(raw); err == nil {
		b, err := os.ReadFile(raw)
		if err != nil {
			return nil, fmt.Errorf("read trust root file: %w", err)
		}
		return b, nil
	}
	return []byte(raw), nil
}

// LoadEd25519PublicKeyFromPEM parses an Ed25519 public key from PEM bytes.
func LoadEd25519PublicKeyFromPEM(pemData []byte) (ed25519.PublicKey, error) {
	block, _ := pem.Decode(pemData)
	if block == nil {
		return nil, fmt.Errorf("no PEM block found")
	}
	if pub, err := x509.ParsePKIXPublicKey(block.Bytes); err == nil {
		if ed, ok := pub.(ed25519.PublicKey); ok {
			return ed, nil
		}
		return nil, fmt.Errorf("not an Ed25519 public key")
	}
	if len(block.Bytes) == ed25519.PublicKeySize {
		return ed25519.PublicKey(block.Bytes), nil
	}
	return nil, fmt.Errorf("unsupported public key format")
}

func decodeBase64Sig(sigBase64 string) ([]byte, error) {
	if b, err := base64.StdEncoding.DecodeString(sigBase64); err == nil {
		return b, nil
	}
	if b, err := base64.RawURLEncoding.DecodeString(sigBase64); err == nil {
		return b, nil
	}
	return nil, fmt.Errorf("sig_decode_error")
}

// VerifySignature verifies an Ed25519 signature over message bytes.
func VerifySignature(message []byte, sigBase64, jwksURL string, pemPub []byte) (bool, string) {
	sig, err := decodeBase64Sig(sigBase64)
	if err != nil {
		return false, err.Error()
	}
	if len(pemPub) > 0 {
		pub, err := LoadEd25519PublicKeyFromPEM(pemPub)
		if err == nil && ed25519.Verify(pub, message, sig) {
			return true, ""
		}
	}
	if strings.TrimSpace(jwksURL) != "" {
		pubs, err := fetchEd25519KeysFromJWKS(jwksURL)
		if err == nil {
			for _, pub := range pubs {
				if ed25519.Verify(pub, message, sig) {
					return true, ""
				}
			}
		}
	}
	return false, "signature_mismatch"
}

type jwksDoc struct {
	Keys []struct {
		Kty string `json:"kty"`
		Crv string `json:"crv"`
		X   string `json:"x"`
	} `json:"keys"`
}

func fetchEd25519KeysFromJWKS(url string) ([]ed25519.PublicKey, error) {
	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	var doc jwksDoc
	if err := json.Unmarshal(body, &doc); err != nil {
		return nil, err
	}
	var keys []ed25519.PublicKey
	for _, k := range doc.Keys {
		if k.Kty != "OKP" || k.Crv != "Ed25519" {
			continue
		}
		raw, err := base64.RawURLEncoding.DecodeString(k.X)
		if err != nil || len(raw) != ed25519.PublicKeySize {
			continue
		}
		keys = append(keys, ed25519.PublicKey(raw))
	}
	if len(keys) == 0 {
		return nil, fmt.Errorf("no Ed25519 keys in JWKS")
	}
	return keys, nil
}

// VerifyEnvelope verifies a DSSE envelope against an expected payload type.
func VerifyEnvelope(envelope Envelope, expectedPayloadType string) VerifyResult {
	if expectedPayloadType != "" && envelope.PayloadType != expectedPayloadType {
		return VerifyResult{Valid: false, Reason: "payload_type_mismatch"}
	}
	if len(envelope.Signatures) == 0 {
		return VerifyResult{Valid: false, Reason: "no_signatures"}
	}
	payload, err := base64.StdEncoding.DecodeString(envelope.Payload)
	if err != nil {
		return VerifyResult{Valid: false, Reason: "payload_decode_error"}
	}
	pemPub, err := LoadTrustRootPEM()
	if err != nil {
		return VerifyResult{Valid: false, Reason: "trust_root_not_configured"}
	}
	jwks := strings.TrimSpace(os.Getenv(EnvJWKSURL))
	for _, sig := range envelope.Signatures {
		if sig.Alg != "" && !strings.EqualFold(sig.Alg, "ed25519") {
			continue
		}
		ok, reason := VerifySignature(payload, sig.Sig, jwks, pemPub)
		if ok {
			return VerifyResult{Valid: true}
		}
		if reason != "" {
			return VerifyResult{Valid: false, Reason: reason}
		}
	}
	return VerifyResult{Valid: false, Reason: "signature_mismatch"}
}

// ParseEnvelopeJSON parses a DSSE envelope from JSON bytes.
func ParseEnvelopeJSON(data []byte) (Envelope, error) {
	var env Envelope
	if err := json.Unmarshal(data, &env); err != nil {
		return Envelope{}, err
	}
	return env, nil
}

// AccessReceiptPayload is the canonical signed receipt body.
type AccessReceiptPayload struct {
	ReceiptID   string `json:"receipt_id"`
	Tenant      string `json:"tenant"`
	SubjectID   string `json:"subject_id"`
	QueryHash   string `json:"query_hash"`
	IndexShard  string `json:"index_shard"`
	Timestamp   int64  `json:"timestamp"`
	ResultHash  string `json:"result_hash"`
	ResultCount int    `json:"result_count,omitempty"`
	QueryTimeMs int    `json:"query_time_ms,omitempty"`
	Signature   string `json:"signature"`
}

// CanonicalReceiptPayload builds deterministic JSON for receipt signing.
func CanonicalReceiptPayload(r AccessReceiptPayload) ([]byte, error) {
	m := map[string]interface{}{
		"index_shard":  r.IndexShard,
		"query_hash":   r.QueryHash,
		"receipt_id":   r.ReceiptID,
		"result_hash":  r.ResultHash,
		"signature":    r.Signature,
		"subject_id":   r.SubjectID,
		"tenant":       r.Tenant,
		"timestamp":    r.Timestamp,
	}
	if r.ResultCount != 0 {
		m["result_count"] = r.ResultCount
	}
	if r.QueryTimeMs != 0 {
		m["query_time_ms"] = r.QueryTimeMs
	}
	return marshalCanonicalJSON(m)
}

func marshalCanonicalJSON(v interface{}) ([]byte, error) {
	switch t := v.(type) {
	case map[string]interface{}:
		keys := make([]string, 0, len(t))
		for k := range t {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		buf := strings.Builder{}
		buf.WriteByte('{')
		for i, k := range keys {
			if i > 0 {
				buf.WriteByte(',')
			}
			kb, _ := json.Marshal(k)
			buf.Write(kb)
			buf.WriteByte(':')
			vb, err := marshalCanonicalJSON(t[k])
			if err != nil {
				return nil, err
			}
			buf.Write(vb)
		}
		buf.WriteByte('}')
		return []byte(buf.String()), nil
	default:
		return json.Marshal(t)
	}
}

// VerifyAccessReceipt verifies structural fields and Ed25519 signature.
func VerifyAccessReceipt(receipt AccessReceiptPayload, signAlg, sig string) error {
	if receipt.ReceiptID == "" {
		return fmt.Errorf("receipt ID is required")
	}
	if receipt.Tenant == "" {
		return fmt.Errorf("receipt tenant is required")
	}
	if receipt.IndexShard == "" {
		return fmt.Errorf("receipt index shard is required")
	}
	if signAlg != "ed25519" {
		return fmt.Errorf("unsupported signature algorithm: %s", signAlg)
	}
	if sig == "" {
		return fmt.Errorf("receipt signature is required")
	}
	if !EnforceDSSE() {
		return nil
	}
	if !TrustRootConfigured() {
		return fmt.Errorf("trust root not configured")
	}
	payload, err := CanonicalReceiptPayload(receipt)
	if err != nil {
		return fmt.Errorf("canonical payload: %w", err)
	}
	pemPub, err := LoadTrustRootPEM()
	if err != nil {
		return err
	}
	jwks := strings.TrimSpace(os.Getenv(EnvJWKSURL))
	ok, reason := VerifySignature(payload, sig, jwks, pemPub)
	if !ok {
		if reason == "" {
			reason = "signature_mismatch"
		}
		return fmt.Errorf("receipt signature verification failed: %s", reason)
	}
	return nil
}
