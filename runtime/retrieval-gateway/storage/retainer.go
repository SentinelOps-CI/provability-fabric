package storage

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"log"
	"time"

	"github.com/go-redis/redis/v8"
)

// RetentionConfig holds TTL and sanitization settings
type RetentionConfig struct {
	RawQueryTTL   time.Duration
	RawResultTTL  time.Duration
	IndexCacheTTL time.Duration
	HashRetention time.Duration
	ZeroRetention bool
	SanitizeLogs  bool
}

// Retainer manages data retention and sanitization
type Retainer struct {
	redis  *redis.Client
	config RetentionConfig
}

// NewRetainer creates a new retainer instance
func NewRetainer(redisClient *redis.Client, config RetentionConfig) *Retainer {
	if config.ZeroRetention && config.RawQueryTTL > 10*time.Minute {
		log.Printf("WARNING: Raw query TTL %v exceeds zero-retention limit of 10 minutes", config.RawQueryTTL)
	}

	return &Retainer{
		redis:  redisClient,
		config: config,
	}
}

// StoreQuery stores a query with automatic TTL deletion
func (r *Retainer) StoreQuery(ctx context.Context, queryID string, rawQuery string) error {
	// Store raw query with TTL
	rawKey := fmt.Sprintf("query:raw:%s", queryID)
	err := r.redis.Set(ctx, rawKey, rawQuery, r.config.RawQueryTTL).Err()
	if err != nil {
		return fmt.Errorf("failed to store raw query: %w", err)
	}

	// Store query hash with longer retention
	queryHash := r.hashContent(rawQuery)
	hashKey := fmt.Sprintf("query:hash:%s", queryID)
	err = r.redis.Set(ctx, hashKey, queryHash, r.config.HashRetention).Err()
	if err != nil {
		return fmt.Errorf("failed to store query hash: %w", err)
	}

	log.Printf("Stored query %s (raw TTL: %v, hash retention: %v)",
		queryID, r.config.RawQueryTTL, r.config.HashRetention)

	return nil
}

// StoreResult stores a result with automatic TTL deletion
func (r *Retainer) StoreResult(ctx context.Context, resultID string, rawResult string) error {
	// Store raw result with TTL
	rawKey := fmt.Sprintf("result:raw:%s", resultID)
	err := r.redis.Set(ctx, rawKey, rawResult, r.config.RawResultTTL).Err()
	if err != nil {
		return fmt.Errorf("failed to store raw result: %w", err)
	}

	// Store result hash with longer retention
	resultHash := r.hashContent(rawResult)
	hashKey := fmt.Sprintf("result:hash:%s", resultID)
	err = r.redis.Set(ctx, hashKey, resultHash, r.config.HashRetention).Err()
	if err != nil {
		return fmt.Errorf("failed to store result hash: %w", err)
	}

	log.Printf("Stored result %s (raw TTL: %v, hash retention: %v)",
		resultID, r.config.RawResultTTL, r.config.HashRetention)

	return nil
}

// GetQuery retrieves a query (raw if within TTL, hash otherwise)
func (r *Retainer) GetQuery(ctx context.Context, queryID string) (string, string, error) {
	// Try to get raw query first
	rawKey := fmt.Sprintf("query:raw:%s", queryID)
	rawQuery, err := r.redis.Get(ctx, rawKey).Result()
	if err == nil {
		// Raw query available
		return rawQuery, "", nil
	}

	// Raw query expired, get hash
	hashKey := fmt.Sprintf("query:hash:%s", queryID)
	queryHash, err := r.redis.Get(ctx, hashKey).Result()
	if err != nil {
		return "", "", fmt.Errorf("query not found: %w", err)
	}

	return "", queryHash, nil
}

// GetResult retrieves a result (raw if within TTL, hash otherwise)
func (r *Retainer) GetResult(ctx context.Context, resultID string) (string, string, error) {
	// Try to get raw result first
	rawKey := fmt.Sprintf("result:raw:%s", resultID)
	rawResult, err := r.redis.Get(ctx, rawKey).Result()
	if err == nil {
		// Raw result available
		return rawResult, "", nil
	}

	// Raw result expired, get hash
	hashKey := fmt.Sprintf("result:hash:%s", resultID)
	resultHash, err := r.redis.Get(ctx, hashKey).Result()
	if err != nil {
		return "", "", fmt.Errorf("result not found: %w", err)
	}

	return "", resultHash, nil
}

// CleanupExpired manually cleans up any expired content (safety measure)
func (r *Retainer) CleanupExpired(ctx context.Context) error {
	// Find all raw keys that should have expired
	now := time.Now()

	// Scan for raw query keys
	queryKeys, err := r.redis.Keys(ctx, "query:raw:*").Result()
	if err != nil {
		return fmt.Errorf("failed to scan query keys: %w", err)
	}

	var expiredKeys []string
	for _, key := range queryKeys {
		ttl, err := r.redis.TTL(ctx, key).Result()
		if err != nil {
			continue
		}

		// If TTL is -1 (no expiration) or key is older than max TTL
		if ttl == -1 || (ttl > 0 && ttl > r.config.RawQueryTTL) {
			expiredKeys = append(expiredKeys, key)
		}
	}

	// Scan for raw result keys
	resultKeys, err := r.redis.Keys(ctx, "result:raw:*").Result()
	if err != nil {
		return fmt.Errorf("failed to scan result keys: %w", err)
	}

	for _, key := range resultKeys {
		ttl, err := r.redis.TTL(ctx, key).Result()
		if err != nil {
			continue
		}

		// If TTL is -1 (no expiration) or key is older than max TTL
		if ttl == -1 || (ttl > 0 && ttl > r.config.RawResultTTL) {
			expiredKeys = append(expiredKeys, key)
		}
	}

	// Delete expired keys
	if len(expiredKeys) > 0 {
		deleted, err := r.redis.Del(ctx, expiredKeys...).Result()
		if err != nil {
			return fmt.Errorf("failed to delete expired keys: %w", err)
		}
		log.Printf("Cleaned up %d expired keys", deleted)
	}

	return nil
}

// GetRetentionStatus returns current retention status for attestation
func (r *Retainer) GetRetentionStatus(ctx context.Context) (map[string]interface{}, error) {
	// Count raw vs hash-only entries
	rawQueryCount, _ := r.countKeys(ctx, "query:raw:*")
	hashQueryCount, _ := r.countKeys(ctx, "query:hash:*")
	rawResultCount, _ := r.countKeys(ctx, "result:raw:*")
	hashResultCount, _ := r.countKeys(ctx, "result:hash:*")

	// Check for any TTL violations
	violations, err := r.checkTTLViolations(ctx)
	if err != nil {
		return nil, err
	}

	status := map[string]interface{}{
		"zero_retention_enabled": r.config.ZeroRetention,
		"raw_query_ttl_seconds":  int(r.config.RawQueryTTL.Seconds()),
		"raw_result_ttl_seconds": int(r.config.RawResultTTL.Seconds()),
		"raw_queries_count":      rawQueryCount,
		"hash_queries_count":     hashQueryCount,
		"raw_results_count":      rawResultCount,
		"hash_results_count":     hashResultCount,
		"ttl_violations":         violations,
		"compliance_status":      len(violations) == 0,
		"timestamp":              time.Now().Unix(),
	}

	return status, nil
}

// hashContent creates SHA-256 hash of content
func (r *Retainer) hashContent(content string) string {
	hash := sha256.Sum256([]byte(content))
	return hex.EncodeToString(hash[:])
}

// countKeys counts keys matching a pattern
func (r *Retainer) countKeys(ctx context.Context, pattern string) (int, error) {
	keys, err := r.redis.Keys(ctx, pattern).Result()
	if err != nil {
		return 0, err
	}
	return len(keys), nil
}

// checkTTLViolations checks for keys that exceed max TTL
func (r *Retainer) checkTTLViolations(ctx context.Context) ([]string, error) {
	var violations []string

	// Check raw query keys
	queryKeys, err := r.redis.Keys(ctx, "query:raw:*").Result()
	if err == nil {
		for _, key := range queryKeys {
			ttl, err := r.redis.TTL(ctx, key).Result()
			if err != nil {
				continue
			}

			if ttl > r.config.RawQueryTTL {
				violations = append(violations, fmt.Sprintf("query key %s has TTL %v exceeding limit %v",
					key, ttl, r.config.RawQueryTTL))
			}
		}
	}

	// Check raw result keys
	resultKeys, err := r.redis.Keys(ctx, "result:raw:*").Result()
	if err == nil {
		for _, key := range resultKeys {
			ttl, err := r.redis.TTL(ctx, key).Result()
			if err != nil {
				continue
			}

			if ttl > r.config.RawResultTTL {
				violations = append(violations, fmt.Sprintf("result key %s has TTL %v exceeding limit %v",
					key, ttl, r.config.RawResultTTL))
			}
		}
	}

	return violations, nil
}
