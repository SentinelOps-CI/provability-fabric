package main

import (
	"context"
	"math"
	"regexp"
	"testing"
)

// TestPolicyHashKnownSHA256Vector pins the on-wire digest format and prevents
// a return to prefix-encoding the serialized policy as a purported hash.
func TestPolicyHashKnownSHA256Vector(t *testing.T) {
	service := NewSpecService()
	policy := ActionDSLPolicy{
		PolicyID: "simple",
		Version: "v1",
		Metadata: map[string]string{
			"compiled_at":      "2026-01-01T00:00:00Z",
			"compiler_version": "v1",
		},
	}

	const expected = "75d68e36bd9ea7fea18aab1fba7ea6bc37e0a5ef022cc16cd0acb62fac7bdc25"
	got, err := service.calculatePolicyHash(policy)
	if err != nil {
		t.Fatalf("calculate policy digest: %v", err)
	}
	if got != expected {
		t.Fatalf("SHA-256 digest = %q, want %q", got, expected)
	}
	if policy.Metadata["compiled_at"] != "2026-01-01T00:00:00Z" {
		t.Fatal("hashing modified the source metadata")
	}
}

// TestPolicyHashTracksPolicyContent proves that policies sharing a long
// serialized prefix cannot alias a proof cache entry. Volatile compilation
// timestamps are excluded; version, rules and user metadata remain relevant.
func TestPolicyHashTracksPolicyContent(t *testing.T) {
	service := NewSpecService()
	req := PolicyCompileRequest{
		PolicyID: "fixed-policy-id-for-repeated-compilations",
		Version:  "1.0.0",
		English:  "allow analyst to read report when role is analyst",
		Metadata: map[string]string{"owner": "team-a"},
	}

	first, err := service.CompilePolicy(context.Background(), req)
	if err != nil {
		t.Fatalf("compile original policy: %v", err)
	}
	second, err := service.CompilePolicy(context.Background(), req)
	if err != nil {
		t.Fatalf("recompile original policy: %v", err)
	}
	if first.PolicyHash != second.PolicyHash {
		t.Fatalf("same compiled policy has unstable hash: %q != %q", first.PolicyHash, second.PolicyHash)
	}
	if matched, _ := regexp.MatchString("^[0-9a-f]{64}$", first.PolicyHash); !matched {
		t.Fatalf("policy hash is not 64 lowercase hexadecimal characters: %q", first.PolicyHash)
	}

	req.English = "allow analyst to read confidentialreport when role is analyst"
	changedRule, err := service.CompilePolicy(context.Background(), req)
	if err != nil {
		t.Fatalf("compile policy with changed rule: %v", err)
	}
	if first.PolicyHash == changedRule.PolicyHash {
		t.Fatal("distinct rules shared a policy hash")
	}

	req.English = "allow analyst to read report when role is analyst"
	req.Metadata = map[string]string{"owner": "team-b"}
	changedMetadata, err := service.CompilePolicy(context.Background(), req)
	if err != nil {
		t.Fatalf("compile policy with changed user metadata: %v", err)
	}
	if first.PolicyHash == changedMetadata.PolicyHash {
		t.Fatal("distinct declared metadata shared a policy hash")
	}

	req.Metadata = map[string]string{"owner": "team-a"}
	req.Version = "2.0.0"
	changedVersion, err := service.CompilePolicy(context.Background(), req)
	if err != nil {
		t.Fatalf("compile policy with changed version: %v", err)
	}
	if first.PolicyHash == changedVersion.PolicyHash {
		t.Fatal("distinct policy versions shared a policy hash")
	}

	policyWithDifferentTimestamp := first.ActionDSL
	policyWithDifferentTimestamp.Metadata = map[string]string{
		"owner":            "team-a",
		"compiler_version": "spec-service-v1.0.0",
		"compiled_at":      "2040-01-01T00:00:00Z",
	}
	stableHash, err := service.calculatePolicyHash(policyWithDifferentTimestamp)
	if err != nil {
		t.Fatalf("hash policy with different compilation timestamp: %v", err)
	}
	if stableHash != first.PolicyHash {
		t.Fatalf("compilation timestamp changed content hash: %q != %q", stableHash, first.PolicyHash)
	}
}

// TestPolicyHashRejectsUnencodableContent prevents an invalid compiled
// policy from receiving a fabricated or truncated identifier.
func TestPolicyHashRejectsUnencodableContent(t *testing.T) {
	service := NewSpecService()
	invalid := ActionDSLPolicy{
		PolicyID: "bad-numeric-value",
		Version:  "1.0.0",
		Rules: []DSLRule{{
			RuleID: "rule_1",
			Type:   "budget",
			Budget: &Budget{MaxCost: math.Inf(1), Currency: "USD"},
		}},
	}
	if got, err := service.calculatePolicyHash(invalid); err == nil {
		t.Fatalf("expected JSON encoding error for infinity, got hash %q", got)
	}
}
