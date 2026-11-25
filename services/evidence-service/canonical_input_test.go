// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/base64"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/gin-gonic/gin"
)

func TestEvidenceStrictCanonicalNumbers(t *testing.T) {
	for _, raw := range []string{"9007199254740993", "1.00000000000000001", "1e-400", "1e99999999999", "1e309"} {
		if _, err := canonicalEvidenceNumber(json.Number(raw)); err == nil {
			t.Errorf("lossy or unsupported number accepted: %s", raw)
		}
	}
	for _, tc := range []struct{ raw, want string }{
		{"9007199254740992", "9007199254740992"},
		{"1.00", "1"}, {"1e0", "1"}, {"0.125", "0.125"}, {"1e-7", "1e-7"},
	} {
		got, err := canonicalEvidenceNumber(json.Number(tc.raw))
		if err != nil || string(got) != tc.want {
			t.Errorf("representable number %s: %s, %v", tc.raw, got, err)
		}
	}
}

func TestEvidenceStrictSignatureBoundary(t *testing.T) {
	pub, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	payload := signedValidationCertificate(t, priv)
	var claims map[string]interface{}
	if err := json.Unmarshal(payload, &claims); err != nil {
		t.Fatal(err)
	}
	delete(claims, "sig")
	claims["epoch"] = float64(9007199254740992)
	claims["extensions"] = map[string]interface{}{"fraction": 0.125}
	canon, err := marshalCanonicalJSON(claims)
	if err != nil {
		t.Fatal(err)
	}
	claims["sig"] = base64.RawURLEncoding.EncodeToString(ed25519.Sign(priv, canon))
	payload, err = json.Marshal(claims)
	if err != nil {
		t.Fatal(err)
	}
	router := gin.New()
	service := &EvidenceService{trustedJWKSKeys: []ed25519.PublicKey{pub}}
	router.POST("/validate", service.verifyCertHandler)
	call := func(body string, expected int, valid bool) {
		t.Helper()
		request := httptest.NewRequest(http.MethodPost, "/validate", strings.NewReader(body))
		request.Header.Set("Content-Type", "application/json")
		rec := httptest.NewRecorder()
		router.ServeHTTP(rec, request)
		if rec.Code != expected {
			t.Fatalf("HTTP %d, expected %d: %s", rec.Code, expected, rec.Body.String())
		}
		if expected == 200 {
			var result CertValidationResponse
			if err := json.Unmarshal(rec.Body.Bytes(), &result); err != nil || !result.SignatureChecked || result.SignatureValid != valid {
				t.Fatalf("unexpected signature verdict: %+v, %v", result, err)
			}
		}
	}
	for _, field := range []string{"raw", "cert"} {
		wrap := func(p []byte) string { return "{\"" + field + "\":" + string(p) + "}" }
		call(wrap(payload), 200, true)
		call(wrap(bytes.Replace(payload, []byte("0.125"), []byte("0.1250"), 1)), 200, true)
		call(wrap(bytes.Replace(payload, []byte("9007199254740992"), []byte("9007199254740993"), 1)), 400, false)
		call(wrap(bytes.Replace(payload, []byte("\"fraction\":0.125"), []byte("\"fraction\":0.5,\"fraction\":0.125"), 1)), 400, false)
		call(wrap(bytes.Replace(payload, []byte("0.125"), []byte("0.25"), 1)), 200, false)
	}
	call("{\"raw\":"+string(payload)+",\"cert\":"+string(payload)+"}", 400, false)
	call("{\"raw\":"+string(payload)+",\"raw\":"+string(payload)+"}", 400, false)
	for _, raw := range []string{`{"raw":{"value":"\ud800"}}`, `{"raw":null}`, `{"raw":{}} {}`} {
		call(raw, 400, false)
	}
}
