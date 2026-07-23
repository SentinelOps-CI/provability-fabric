package policykernel

import (
	"testing"
	"time"

	"github.com/alicebob/miniredis/v2"
)

func sampleDecision(reason string) Decision {
	return Decision{
		Valid:  true,
		Reason: reason,
		SecurityChecks: SecurityCheckResults{
			CapabilityMatch: true,
		},
	}
}

func TestRedisCacheGetSet(t *testing.T) {
	mr, err := miniredis.Run()
	if err != nil {
		t.Fatalf("miniredis: %v", err)
	}
	defer mr.Close()

	cache := NewDecisionCache(100, time.Minute, mr.Addr())
	defer cache.Close()

	if !cache.RedisEnabled() {
		t.Fatal("expected Redis L2 to be enabled against miniredis")
	}

	key := CacheKey{
		PlanHash:    "plan-a",
		CapsTokenID: "caps-1",
		PolicyHash:  "policy-xyz",
	}
	want := sampleDecision("approved")

	if err := cache.Set(key, want); err != nil {
		t.Fatalf("Set: %v", err)
	}

	// Drop in-memory entry so the next Get must hit Redis.
	cache.mu.Lock()
	delete(cache.inMemory, key.String())
	cache.mu.Unlock()

	got, ok := cache.Get(key)
	if !ok {
		t.Fatal("expected Redis-backed hit after memory eviction")
	}
	if got.Reason != want.Reason || !got.Valid {
		t.Fatalf("got %+v, want %+v", got, want)
	}

	stats := cache.GetStats()
	if stats.HitCount < 1 {
		t.Fatalf("expected at least one hit, got %+v", stats)
	}
}

func TestRedisCacheInvalidateByPolicyHash(t *testing.T) {
	mr, err := miniredis.Run()
	if err != nil {
		t.Fatalf("miniredis: %v", err)
	}
	defer mr.Close()

	cache := NewDecisionCache(100, time.Minute, mr.Addr())
	defer cache.Close()

	keep := CacheKey{PlanHash: "p1", CapsTokenID: "c1", PolicyHash: "keep-me"}
	drop := CacheKey{PlanHash: "p2", CapsTokenID: "c2", PolicyHash: "drop-me"}

	if err := cache.Set(keep, sampleDecision("keep")); err != nil {
		t.Fatalf("Set keep: %v", err)
	}
	if err := cache.Set(drop, sampleDecision("drop")); err != nil {
		t.Fatalf("Set drop: %v", err)
	}

	if err := cache.InvalidateByPolicyHash("drop-me"); err != nil {
		t.Fatalf("InvalidateByPolicyHash: %v", err)
	}

	if _, ok := cache.Get(drop); ok {
		t.Fatal("expected drop-me policy entries to be gone")
	}
	if got, ok := cache.Get(keep); !ok || got.Reason != "keep" {
		t.Fatalf("expected keep-me to survive invalidation, got ok=%v decision=%+v", ok, got)
	}

	// Confirm Redis index cleared for drop-me.
	cache.mu.Lock()
	delete(cache.inMemory, keep.String())
	cache.mu.Unlock()
	if _, ok := cache.Get(keep); !ok {
		t.Fatal("expected keep-me to remain available via Redis after memory clear")
	}
	cache.mu.Lock()
	delete(cache.inMemory, drop.String())
	cache.mu.Unlock()
	if _, ok := cache.Get(drop); ok {
		t.Fatal("expected drop-me to be absent from Redis after invalidation")
	}
}

func TestRedisCacheMemoryOnlyWhenAddrEmpty(t *testing.T) {
	cache := NewDecisionCache(10, time.Minute, "")
	defer cache.Close()

	if cache.RedisEnabled() {
		t.Fatal("empty Redis addr must not enable L2")
	}

	key := CacheKey{PlanHash: "p", CapsTokenID: "c", PolicyHash: "pol"}
	if err := cache.Set(key, sampleDecision("mem")); err != nil {
		t.Fatalf("Set: %v", err)
	}
	got, ok := cache.Get(key)
	if !ok || got.Reason != "mem" {
		t.Fatalf("memory-only path failed: ok=%v got=%+v", ok, got)
	}
}

func TestRedisCacheFallsBackWhenUnreachable(t *testing.T) {
	cache := NewDecisionCache(10, time.Minute, "127.0.0.1:1")
	defer cache.Close()

	if cache.RedisEnabled() {
		t.Fatal("unreachable Redis must fall back to memory-only")
	}

	key := CacheKey{PlanHash: "p", CapsTokenID: "c", PolicyHash: "pol"}
	if err := cache.Set(key, sampleDecision("fallback")); err != nil {
		t.Fatalf("Set: %v", err)
	}
	if _, ok := cache.Get(key); !ok {
		t.Fatal("expected in-memory hit after Redis dial failure")
	}
}
