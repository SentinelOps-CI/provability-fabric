// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package sentinelops

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"time"
)

// Client provides access to SentinelOps Platform APIs
type Client struct {
	baseURL    string
	httpClient *http.Client
	apiKey     string
}

// NewClient creates a new SentinelOps client
func NewClient(baseURL string, apiKey string) *Client {
	if baseURL == "" {
		baseURL = "http://localhost:8000"
	}

	return &Client{
		baseURL: baseURL,
		httpClient: &http.Client{
			Timeout: 30 * time.Second,
		},
		apiKey: apiKey,
	}
}

// request makes HTTP request to platform API
func (c *Client) request(ctx context.Context, method, endpoint string, body interface{}) (*http.Response, error) {
	var reqBody io.Reader
	if body != nil {
		jsonData, err := json.Marshal(body)
		if err != nil {
			return nil, fmt.Errorf("failed to marshal request body: %w", err)
		}
		reqBody = bytes.NewBuffer(jsonData)
	}

	req, err := http.NewRequestWithContext(ctx, method, c.baseURL+endpoint, reqBody)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")
	if c.apiKey != "" {
		req.Header.Set("Authorization", "Bearer "+c.apiKey)
	}

	resp, err := c.httpClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}

	if resp.StatusCode >= 400 {
		defer resp.Body.Close()
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API error %d: %s", resp.StatusCode, string(body))
	}

	return resp, nil
}

// CompilePolicy converts English policy to ActionDSL
func (c *Client) CompilePolicy(ctx context.Context, req PolicyCompileRequest) (*PolicyCompileResponse, error) {
	resp, err := c.request(ctx, "POST", "/api/v1/policy/compile", req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result PolicyCompileResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// BuildPolicy compiles ActionDSL to DFA
func (c *Client) BuildPolicy(ctx context.Context, req PolicyBuildRequest) (*PolicyBuildResponse, error) {
	resp, err := c.request(ctx, "POST", "/api/v1/policy/build", req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result PolicyBuildResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// RunProofs executes Lean proofs for policy
func (c *Client) RunProofs(ctx context.Context, req ProofRunRequest) (*ProofRunResponse, error) {
	resp, err := c.request(ctx, "POST", "/api/v1/proofs/run", req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result ProofRunResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// DeployPolicy deploys policy to runtime
func (c *Client) DeployPolicy(ctx context.Context, req DeployRequest) (*DeployResponse, error) {
	resp, err := c.request(ctx, "POST", "/api/v1/runtime/deploy", req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result DeployResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// VerifyCert validates CERT-V1 certificate
func (c *Client) VerifyCert(ctx context.Context, cert CertV1) (bool, error) {
	resp, err := c.request(ctx, "POST", "/api/v1/evidence/cert", cert)
	if err != nil {
		return false, err
	}
	defer resp.Body.Close()

	return resp.StatusCode == 201, nil
}

// SearchCertificates searches for certificates with filters
func (c *Client) SearchCertificates(ctx context.Context, req CertSearchRequest) (*CertSearchResponse, error) {
	resp, err := c.request(ctx, "POST", "/api/v1/evidence/search", req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result CertSearchResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// StartReplay initiates deterministic replay
func (c *Client) StartReplay(ctx context.Context, req ReplayRequest) (*ReplayResponse, error) {
	resp, err := c.request(ctx, "POST", "/api/v1/replay", req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result ReplayResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// GetReplayStatus gets replay job status
func (c *Client) GetReplayStatus(ctx context.Context, jobID string) (*ReplayStatus, error) {
	resp, err := c.request(ctx, "GET", fmt.Sprintf("/api/v1/replay/%s", jobID), nil)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result ReplayStatus
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// DownloadPacket downloads compliance packet
func (c *Client) DownloadPacket(ctx context.Context, decisionID string) ([]byte, error) {
	// Create packet first
	packetReq := map[string]interface{}{
		"session_id": decisionID,
	}

	resp, err := c.request(ctx, "POST", "/api/v1/compliance/packet", packetReq)
	if err != nil {
		return nil, err
	}

	var packetResp struct {
		PacketID string `json:"packet_id"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&packetResp); err != nil {
		resp.Body.Close()
		return nil, fmt.Errorf("failed to decode packet response: %w", err)
	}
	resp.Body.Close()

	// Download packet
	downloadResp, err := c.request(ctx, "GET", fmt.Sprintf("/api/v1/compliance/packet/%s", packetResp.PacketID), nil)
	if err != nil {
		return nil, err
	}
	defer downloadResp.Body.Close()

	return io.ReadAll(downloadResp.Body)
}

// RotateEpoch rotates permission epoch
func (c *Client) RotateEpoch(ctx context.Context, oldEpoch, newEpoch int, reason string) (*EpochRotateResponse, error) {
	req := map[string]interface{}{
		"old_epoch": oldEpoch,
		"new_epoch": newEpoch,
	}
	if reason != "" {
		req["reason"] = reason
	}

	resp, err := c.request(ctx, "POST", "/api/v1/runtime/epoch/rotate", req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result EpochRotateResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// GetHealth gets platform health status
func (c *Client) GetHealth(ctx context.Context) (*HealthResponse, error) {
	resp, err := c.request(ctx, "GET", "/health", nil)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result HealthResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// GetSLO gets runtime SLO metrics
func (c *Client) GetSLO(ctx context.Context) (*SLOResponse, error) {
	resp, err := c.request(ctx, "GET", "/api/v1/runtime/slo", nil)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var result SLOResponse
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// CI helper functions
func (c *Client) AssertCertsValid(ctx context.Context, certs []CertV1) error {
	for _, cert := range certs {
		valid, err := c.VerifyCert(ctx, cert)
		if err != nil {
			return fmt.Errorf("cert verification failed: %w", err)
		}
		if !valid {
			return fmt.Errorf("invalid certificate: %s", cert.SessionID)
		}
	}
	return nil
}

func (c *Client) AssertLowView(ctx context.Context, replayID string, threshold float64) error {
	status, err := c.GetReplayStatus(ctx, replayID)
	if err != nil {
		return fmt.Errorf("failed to get replay status: %w", err)
	}

	if status.LowViewMatchPct < threshold {
		return fmt.Errorf("low-view match %.3f%% below threshold %.3f%%", 
			status.LowViewMatchPct*100, threshold*100)
	}

	return nil
}

// WaitForReplay waits for replay completion with timeout
func (c *Client) WaitForReplay(ctx context.Context, jobID string, timeout time.Duration) (*ReplayStatus, error) {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	ticker := time.NewTicker(2 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return nil, fmt.Errorf("replay timeout: %w", ctx.Err())
		case <-ticker.C:
			status, err := c.GetReplayStatus(ctx, jobID)
			if err != nil {
				return nil, err
			}

			if status.Status == "completed" || status.Status == "failed" {
				return status, nil
			}
		}
	}
}

// FullPolicyWorkflow executes complete policy lifecycle
func (c *Client) FullPolicyWorkflow(ctx context.Context, englishPolicy, policyID string) (*WorkflowResult, error) {
	// 1. Compile
	compileResp, err := c.CompilePolicy(ctx, PolicyCompileRequest{
		English:  englishPolicy,
		PolicyID: policyID,
		Version:  "1.0.0",
	})
	if err != nil {
		return nil, fmt.Errorf("compile failed: %w", err)
	}

	// 2. Run proofs
	proofResp, err := c.RunProofs(ctx, ProofRunRequest{
		PolicyHash: compileResp.PolicyHash,
		ActionDSL:  compileResp.ActionDSL,
	})
	if err != nil {
		return nil, fmt.Errorf("proof failed: %w", err)
	}

	// 3. Build
	buildResp, err := c.BuildPolicy(ctx, PolicyBuildRequest{
		PolicyHash: compileResp.PolicyHash,
		ActionDSL:  compileResp.ActionDSL,
		ProofHash:  proofResp.ProofHash,
	})
	if err != nil {
		return nil, fmt.Errorf("build failed: %w", err)
	}

	// 4. Deploy
	deployResp, err := c.DeployPolicy(ctx, DeployRequest{
		PolicyHash:   compileResp.PolicyHash,
		AutomataHash: buildResp.AutomataHash,
		Epoch:        1,
	})
	if err != nil {
		return nil, fmt.Errorf("deploy failed: %w", err)
	}

	return &WorkflowResult{
		PolicyHash:   compileResp.PolicyHash,
		ProofHash:    proofResp.ProofHash,
		AutomataHash: buildResp.AutomataHash,
		Epoch:        deployResp.Epoch,
		Status:       "deployed",
	}, nil
}