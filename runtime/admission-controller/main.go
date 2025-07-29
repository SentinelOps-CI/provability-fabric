// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"

	admissionv1 "k8s.io/api/admission/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/serializer"
)

var (
	runtimeScheme = runtime.NewScheme()
	codecs        = serializer.NewCodecFactory(runtimeScheme)
	deserializer  = codecs.UniversalDeserializer()
)

type LeanCheckRequest struct {
	Hash      string `json:"hash"`
	Signature string `json:"signature"`
}

type LeanCheckResponse struct {
	Valid bool   `json:"valid"`
	Error string `json:"error,omitempty"`
}

type LedgerRequest struct {
	Hash    string  `json:"hash"`
	SpecSig string  `json:"specSig"`
	Risk    float64 `json:"risk"`
	Reason  string  `json:"reason"`
}

type LedgerResponse struct {
	Hash      string  `json:"hash"`
	SpecSig   string  `json:"specSig"`
	RiskScore float64 `json:"riskScore"`
	Reason    string  `json:"reason"`
}

type AdmissionResponse struct {
	Allowed   bool                   `json:"allowed"`
	Result    *metav1.Status         `json:"result,omitempty"`
	Patch     []byte                 `json:"patch,omitempty"`
	PatchType *admissionv1.PatchType `json:"patchType,omitempty"`
}

func init() {
	_ = corev1.AddToScheme(runtimeScheme)
	_ = admissionv1.AddToScheme(runtimeScheme)
}

func postToLedger(hash, specSig string, risk float64, reason string) error {
	ledgerURL := os.Getenv("LEDGER_URL")
	if ledgerURL == "" {
		ledgerURL = "http://ledger:4000/graphql"
	}

	query := `mutation Publish($hash: ID!, $specSig: String!, $risk: Float!, $reason: String!) {
		publish(hash: $hash, specSig: $specSig, risk: $risk, reason: $reason) {
			hash
			specSig
			riskScore
			reason
		}
	}`

	variables := map[string]interface{}{
		"hash":    hash,
		"specSig": specSig,
		"risk":    risk,
		"reason":  reason,
	}

	requestBody := map[string]interface{}{
		"query":     query,
		"variables": variables,
	}

	reqBytes, err := json.Marshal(requestBody)
	if err != nil {
		return fmt.Errorf("failed to marshal ledger request: %w", err)
	}

	resp, err := http.Post(ledgerURL, "application/json", bytes.NewBuffer(reqBytes))
	if err != nil {
		return fmt.Errorf("failed to post to ledger: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("ledger returned status %d: %s", resp.StatusCode, string(body))
	}

	var result struct {
		Data struct {
			Publish LedgerResponse `json:"publish"`
		} `json:"data"`
		Errors []struct {
			Message string `json:"message"`
		} `json:"errors,omitempty"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return fmt.Errorf("failed to decode ledger response: %w", err)
	}

	if len(result.Errors) > 0 {
		return fmt.Errorf("ledger GraphQL errors: %v", result.Errors)
	}

	return nil
}

func validatePod(pod *corev1.Pod) (*AdmissionResponse, error) {
	// Extract spec.sig and lean.hash from annotations
	specSig := pod.Annotations["spec.sig"]
	leanHash := pod.Annotations["lean.hash"]

	if specSig == "" || leanHash == "" {
		// Post to ledger with risk 1.0 and reason "missing_annotations"
		if err := postToLedger(leanHash, specSig, 1.0, "missing_annotations"); err != nil {
			fmt.Printf("Warning: failed to post to ledger: %v\n", err)
		}

		return &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: "Missing required annotations: spec.sig or lean.hash",
			},
		}, nil
	}

	// Call LeanCheck microservice
	leanCheckURL := os.Getenv("LEANCHECK_URL")
	if leanCheckURL == "" {
		leanCheckURL = "http://leancheck:8080/check"
	}

	reqBody := LeanCheckRequest{
		Hash:      leanHash,
		Signature: specSig,
	}

	reqBytes, err := json.Marshal(reqBody)
	if err != nil {
		// Post to ledger with risk 1.0 and reason "failed_leancheck"
		if err := postToLedger(leanHash, specSig, 1.0, "failed_leancheck"); err != nil {
			fmt.Printf("Warning: failed to post to ledger: %v\n", err)
		}

		return &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: fmt.Sprintf("Failed to marshal LeanCheck request: %v", err),
			},
		}, nil
	}

	resp, err := http.Post(leanCheckURL, "application/json", bytes.NewBuffer(reqBytes))
	if err != nil {
		// Post to ledger with risk 1.0 and reason "failed_leancheck"
		if err := postToLedger(leanHash, specSig, 1.0, "failed_leancheck"); err != nil {
			fmt.Printf("Warning: failed to post to ledger: %v\n", err)
		}

		return &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: fmt.Sprintf("Failed to call LeanCheck: %v", err),
			},
		}, nil
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		// Post to ledger with risk 1.0 and reason "failed_leancheck"
		if err := postToLedger(leanHash, specSig, 1.0, "failed_leancheck"); err != nil {
			fmt.Printf("Warning: failed to post to ledger: %v\n", err)
		}

		return &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: fmt.Sprintf("LeanCheck returned status: %d", resp.StatusCode),
			},
		}, nil
	}

	var leanResp LeanCheckResponse
	if err := json.NewDecoder(resp.Body).Decode(&leanResp); err != nil {
		// Post to ledger with risk 1.0 and reason "failed_leancheck"
		if err := postToLedger(leanHash, specSig, 1.0, "failed_leancheck"); err != nil {
			fmt.Printf("Warning: failed to post to ledger: %v\n", err)
		}

		return &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: fmt.Sprintf("Failed to decode LeanCheck response: %v", err),
			},
		}, nil
	}

	if !leanResp.Valid {
		// Post to ledger with risk 1.0 and reason "failed_leancheck"
		if err := postToLedger(leanHash, specSig, 1.0, "failed_leancheck"); err != nil {
			fmt.Printf("Warning: failed to post to ledger: %v\n", err)
		}

		return &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: fmt.Sprintf("LeanCheck validation failed: %s", leanResp.Error),
			},
		}, nil
	}

	// Check OPA policy if enabled
	enablePolicy := os.Getenv("ENABLE_POLICY")
	if enablePolicy == "" {
		enablePolicy = "true"
	}

	if enablePolicy == "true" {
		// Check for revoked signatures
		if len(specSig) > 8 && specSig[:8] == "revoked:" {
			// Post to ledger with risk 1.0 and reason "revoked_sig"
			if err := postToLedger(leanHash, specSig, 1.0, "revoked_sig"); err != nil {
				fmt.Printf("Warning: failed to post to ledger: %v\n", err)
			}

			return &AdmissionResponse{
				Allowed: false,
				Result: &metav1.Status{
					Message: "Signature is revoked",
				},
			}, nil
		}
	}

	// Post to ledger with risk 0.0 and empty reason for successful validation
	if err := postToLedger(leanHash, specSig, 0.0, ""); err != nil {
		fmt.Printf("Warning: failed to post to ledger: %v\n", err)
	}

	// Inject sidecar watcher container
	sidecarContainer := corev1.Container{
		Name:  "sidecar-watcher",
		Image: "provability-fabric/sidecar-watcher:latest",
		Env: []corev1.EnvVar{
			{
				Name:  "SPEC_SIG",
				Value: specSig,
			},
			{
				Name:  "LIMIT_BUDGET",
				Value: "300.0",
			},
			{
				Name:  "LIMIT_SPAMSCORE",
				Value: "0.07",
			},
		},
		Ports: []corev1.ContainerPort{
			{
				ContainerPort: 9102,
				Name:          "metrics",
			},
		},
	}

	// Create patch to add sidecar container
	patch := []map[string]interface{}{
		{
			"op":    "add",
			"path":  "/spec/containers/-",
			"value": sidecarContainer,
		},
	}

	patchBytes, err := json.Marshal(patch)
	if err != nil {
		return &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: fmt.Sprintf("Failed to create patch: %v", err),
			},
		}, nil
	}

	return &AdmissionResponse{
		Allowed:   true,
		Patch:     patchBytes,
		PatchType: &[]admissionv1.PatchType{admissionv1.PatchTypeJSONPatch}[0],
	}, nil
}

func handleAdmissionReview(w http.ResponseWriter, r *http.Request) {
	var body []byte
	if r.Body != nil {
		if data, err := io.ReadAll(r.Body); err == nil {
			body = data
		}
	}

	if len(body) == 0 {
		http.Error(w, "Empty body", http.StatusBadRequest)
		return
	}

	var admissionResponse *AdmissionResponse
	ar := admissionv1.AdmissionReview{}
	if _, _, err := deserializer.Decode(body, nil, &ar); err != nil {
		admissionResponse = &AdmissionResponse{
			Allowed: false,
			Result: &metav1.Status{
				Message: fmt.Sprintf("Failed to decode admission review: %v", err),
			},
		}
	} else {
		// Extract the pod from the admission review
		var pod corev1.Pod
		if err := json.Unmarshal(ar.Request.Object.Raw, &pod); err != nil {
			admissionResponse = &AdmissionResponse{
				Allowed: false,
				Result: &metav1.Status{
					Message: fmt.Sprintf("Failed to unmarshal pod: %v", err),
				},
			}
		} else {
			admissionResponse, err = validatePod(&pod)
			if err != nil {
				admissionResponse = &AdmissionResponse{
					Allowed: false,
					Result: &metav1.Status{
						Message: fmt.Sprintf("Failed to validate pod: %v", err),
					},
				}
			}
		}
	}

	ar.Response = &admissionv1.AdmissionResponse{
		Allowed:   admissionResponse.Allowed,
		Result:    admissionResponse.Result,
		Patch:     admissionResponse.Patch,
		PatchType: admissionResponse.PatchType,
	}

	resp, err := json.Marshal(ar)
	if err != nil {
		http.Error(w, fmt.Sprintf("Failed to marshal response: %v", err), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	w.Write(resp)
}

func main() {
	port := os.Getenv("PORT")
	if port == "" {
		port = "8443"
	}

	certFile := os.Getenv("CERT_FILE")
	keyFile := os.Getenv("KEY_FILE")

	if certFile == "" {
		certFile = "/etc/certs/tls.crt"
	}
	if keyFile == "" {
		keyFile = "/etc/certs/tls.key"
	}

	http.HandleFunc("/mutate", handleAdmissionReview)

	fmt.Printf("Starting admission controller on port %s\n", port)
	if err := http.ListenAndServeTLS(":"+port, certFile, keyFile, nil); err != nil {
		panic(err)
	}
}
