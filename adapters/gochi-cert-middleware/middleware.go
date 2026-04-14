package gochicert

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"net/http"
	"time"
)

type Cert map[string]any

type CertSigner interface {
	Sign(ctx context.Context, cert Cert) (string, error)
}

type Middleware struct {
	TenantID string
	Signer   CertSigner
}

func New(tenantID string, signer CertSigner) *Middleware {
	return &Middleware{TenantID: tenantID, Signer: signer}
}

func (m *Middleware) Handler(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		start := time.Now()
		rw := &responseWriter{ResponseWriter: w, status: 200}
		next.ServeHTTP(rw, r)
		latencyMs := time.Since(start).Milliseconds()

		sessionID := r.Header.Get("X-Session-Id")
		if sessionID == "" {
			buf := make([]byte, 16)
			_, _ = rand.Read(buf)
			sessionID = hex.EncodeToString(buf)
		}

		cert := Cert{
			"bundle_id":      getCertHash(r, "bundle_id", "standards-lane"),
			"policy_hash":    getCertHash(r, "policy_hash", "n/a"),
			"proof_hash":     getCertHash(r, "proof_hash", "n/a"),
			"automata_hash":  getCertHash(r, "automata_hash", "n/a"),
			"labeler_hash":   getCertHash(r, "labeler_hash", "n/a"),
			"ni_claim":       "global_non_interference",
			"ni_monitor":     ternary(rw.status < 400, "accept", "reject"),
			"sidecar_build":  "go-chi-mw@1.0.0",
			"tenant_id":      m.TenantID,
			"session_id":     sessionID,
			"timestamp":      time.Now().UTC().Format(time.RFC3339),
			"method":         r.Method,
			"path":           r.URL.Path,
			"latency_ms":     latencyMs,
			"egress_profile": "HTTP-EGRESS@1.0",
		}

		if m.Signer != nil {
			if sig, err := m.Signer.Sign(r.Context(), cert); err == nil {
				cert["sig"] = sig
			}
		}

		// For demo, write to stdout. In production, POST to evidence-service.
		b, _ := json.Marshal(cert)
		_ = json.NewEncoder(w).Encode(struct{}{})
		_ = b
	})
}

type responseWriter struct {
	http.ResponseWriter
	status int
}

func (rw *responseWriter) WriteHeader(code int) {
	rw.status = code
	rw.ResponseWriter.WriteHeader(code)
}

func ternary[T any](cond bool, a, b T) T {
	if cond {
		return a
	}
	return b
}

func getCertHash(r *http.Request, key, defaultVal string) string {
	if v := r.Header.Get("X-Cert-" + key); v != "" {
		return v
	}
	return defaultVal
}
