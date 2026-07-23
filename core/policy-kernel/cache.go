package policykernel

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"sync"
	"time"

	"github.com/go-redis/redis/v8"
)

const (
	redisDecisionPrefix = "pf:policy-kernel:decision:"
	redisPolicyPrefix   = "pf:policy-kernel:policy:"
)

// CacheKey represents the unique identifier for cached decisions
type CacheKey struct {
	PlanHash    string `json:"plan_hash"`
	CapsTokenID string `json:"caps_token_id"`
	PolicyHash  string `json:"policy_hash"`
}

// String returns a string representation of the cache key
func (ck CacheKey) String() string {
	data, _ := json.Marshal(ck)
	hash := sha256.Sum256(data)
	return hex.EncodeToString(hash[:])
}

// CachedDecision represents a cached decision with metadata
type CachedDecision struct {
	Decision    Decision  `json:"decision"`
	Key         CacheKey  `json:"key"`
	ExpiresAt   time.Time `json:"expires_at"`
	AccessCount int64     `json:"access_count"`
	LastAccess  time.Time `json:"last_access"`
	CreatedAt   time.Time `json:"created_at"`
}

// CacheStats represents cache performance metrics
type CacheStats struct {
	HitCount     int64   `json:"hit_count"`
	MissCount    int64   `json:"miss_count"`
	HitRate      float64 `json:"hit_rate"`
	TotalItems   int64   `json:"total_items"`
	EvictedCount int64   `json:"evicted_count"`
}

// DecisionCache provides fast-path caching for approved decisions
type DecisionCache struct {
	mu          sync.RWMutex
	inMemory    map[string]*CachedDecision
	accessOrder map[int64]string // frequency -> key mapping
	keyToFreq   map[string]int64 // key -> frequency mapping
	maxSize     int
	ttl         time.Duration
	redisClient *redis.Client
	stats       CacheStats
	ctx         context.Context
	cancel      context.CancelFunc
}

// NewDecisionCache creates a new decision cache instance.
// When redisAddr is non-empty, an L2 Redis client is dialed (Ping required).
// Connection failure falls back to in-memory-only caching.
func NewDecisionCache(maxSize int, ttl time.Duration, redisAddr string) *DecisionCache {
	ctx, cancel := context.WithCancel(context.Background())

	cache := &DecisionCache{
		inMemory:    make(map[string]*CachedDecision),
		accessOrder: make(map[int64]string),
		keyToFreq:   make(map[string]int64),
		maxSize:     maxSize,
		ttl:         ttl,
		ctx:         ctx,
		cancel:      cancel,
	}

	if redisAddr != "" {
		client := redis.NewClient(&redis.Options{
			Addr:     redisAddr,
			Password: "",
			DB:       0,
		})
		pingCtx, pingCancel := context.WithTimeout(ctx, 2*time.Second)
		err := client.Ping(pingCtx).Err()
		pingCancel()
		if err != nil {
			_ = client.Close()
		} else {
			cache.redisClient = client
			go cache.backgroundCleanup()
			go cache.redisSync()
		}
	}

	return cache
}

// RedisEnabled reports whether L2 Redis is active.
func (dc *DecisionCache) RedisEnabled() bool {
	return dc.redisClient != nil
}

// Get retrieves a cached decision if it exists and is valid
func (dc *DecisionCache) Get(key CacheKey) (*Decision, bool) {
	cacheKey := key.String()

	dc.mu.RLock()
	if cached, exists := dc.inMemory[cacheKey]; exists {
		if time.Now().Before(cached.ExpiresAt) {
			cached.AccessCount++
			cached.LastAccess = time.Now()
			dc.updateFrequency(cacheKey, cached.AccessCount)
			decision := cached.Decision
			dc.mu.RUnlock()
			dc.updateStats(true)
			return &decision, true
		}
		dc.mu.RUnlock()
		dc.mu.Lock()
		delete(dc.inMemory, cacheKey)
		delete(dc.keyToFreq, cacheKey)
		dc.mu.Unlock()
	} else {
		dc.mu.RUnlock()
	}

	if dc.redisClient != nil {
		if cached, exists := dc.getFromRedis(cacheKey); exists {
			dc.mu.Lock()
			dc.addToMemoryCache(cacheKey, cached)
			dc.mu.Unlock()
			dc.updateStats(true)
			decision := cached.Decision
			return &decision, true
		}
	}

	dc.updateStats(false)
	return nil, false
}

// Set stores a decision in the cache
func (dc *DecisionCache) Set(key CacheKey, decision Decision) error {
	cacheKey := key.String()

	cached := &CachedDecision{
		Decision:    decision,
		Key:         key,
		ExpiresAt:   time.Now().Add(dc.ttl),
		AccessCount: 1,
		LastAccess:  time.Now(),
		CreatedAt:   time.Now(),
	}

	dc.mu.Lock()
	dc.addToMemoryCache(cacheKey, cached)
	dc.mu.Unlock()

	if dc.redisClient != nil {
		return dc.setToRedis(cacheKey, cached)
	}

	return nil
}

// InvalidateByPolicyHash removes all cached decisions for a specific policy
func (dc *DecisionCache) InvalidateByPolicyHash(policyHash string) error {
	dc.mu.Lock()
	var keysToRemove []string
	for keyStr, cached := range dc.inMemory {
		if cached.Key.PolicyHash == policyHash {
			keysToRemove = append(keysToRemove, keyStr)
		}
	}
	for _, key := range keysToRemove {
		delete(dc.inMemory, key)
		delete(dc.keyToFreq, key)
	}
	dc.mu.Unlock()

	if dc.redisClient != nil {
		return dc.invalidatePolicyInRedis(policyHash)
	}

	return nil
}

// GetStats returns current cache statistics
func (dc *DecisionCache) GetStats() CacheStats {
	dc.mu.RLock()
	defer dc.mu.RUnlock()

	stats := dc.stats
	stats.TotalItems = int64(len(dc.inMemory))

	if stats.HitCount+stats.MissCount > 0 {
		stats.HitRate = float64(stats.HitCount) / float64(stats.HitCount+stats.MissCount)
	}

	return stats
}

// Close cleans up the cache and stops background goroutines
func (dc *DecisionCache) Close() error {
	dc.cancel()

	if dc.redisClient != nil {
		return dc.redisClient.Close()
	}

	return nil
}

// addToMemoryCache adds an item to the in-memory cache with LFU eviction
func (dc *DecisionCache) addToMemoryCache(key string, cached *CachedDecision) {
	if len(dc.inMemory) >= dc.maxSize {
		dc.evictLFU()
	}

	dc.inMemory[key] = cached
	dc.keyToFreq[key] = cached.AccessCount
	dc.accessOrder[cached.AccessCount] = key
}

// evictLFU removes the least frequently used item from the cache
func (dc *DecisionCache) evictLFU() {
	var minFreq int64 = 1<<63 - 1
	var keyToEvict string

	for freq, key := range dc.accessOrder {
		if freq < minFreq {
			minFreq = freq
			keyToEvict = key
		}
	}

	if keyToEvict != "" {
		delete(dc.inMemory, keyToEvict)
		delete(dc.keyToFreq, keyToEvict)
		delete(dc.accessOrder, minFreq)
		dc.stats.EvictedCount++
	}
}

// updateFrequency updates the frequency mapping for LFU
func (dc *DecisionCache) updateFrequency(key string, newFreq int64) {
	oldFreq := dc.keyToFreq[key]
	if oldFreq != 0 {
		delete(dc.accessOrder, oldFreq)
	}

	dc.keyToFreq[key] = newFreq
	dc.accessOrder[newFreq] = key
}

// updateStats updates cache hit/miss statistics
func (dc *DecisionCache) updateStats(hit bool) {
	dc.mu.Lock()
	defer dc.mu.Unlock()

	if hit {
		dc.stats.HitCount++
	} else {
		dc.stats.MissCount++
	}
}

func redisDecisionKey(key string) string {
	return redisDecisionPrefix + key
}

func redisPolicyKey(policyHash string) string {
	return redisPolicyPrefix + policyHash
}

// getFromRedis retrieves a cached decision from Redis
func (dc *DecisionCache) getFromRedis(key string) (*CachedDecision, bool) {
	data, err := dc.redisClient.Get(dc.ctx, redisDecisionKey(key)).Bytes()
	if err != nil {
		return nil, false
	}

	var cached CachedDecision
	if err := json.Unmarshal(data, &cached); err != nil {
		return nil, false
	}

	if time.Now().After(cached.ExpiresAt) {
		_ = dc.redisClient.Del(dc.ctx, redisDecisionKey(key)).Err()
		if cached.Key.PolicyHash != "" {
			_ = dc.redisClient.SRem(dc.ctx, redisPolicyKey(cached.Key.PolicyHash), key).Err()
		}
		return nil, false
	}

	return &cached, true
}

// setToRedis stores a cached decision in Redis and indexes it by policy hash
func (dc *DecisionCache) setToRedis(key string, cached *CachedDecision) error {
	data, err := json.Marshal(cached)
	if err != nil {
		return err
	}

	ttl := time.Until(cached.ExpiresAt)
	if ttl <= 0 {
		return fmt.Errorf("refusing to cache expired decision")
	}

	pipe := dc.redisClient.TxPipeline()
	pipe.Set(dc.ctx, redisDecisionKey(key), data, ttl)
	if cached.Key.PolicyHash != "" {
		pkey := redisPolicyKey(cached.Key.PolicyHash)
		pipe.SAdd(dc.ctx, pkey, key)
		pipe.Expire(dc.ctx, pkey, ttl)
	}
	_, err = pipe.Exec(dc.ctx)
	return err
}

func (dc *DecisionCache) invalidatePolicyInRedis(policyHash string) error {
	pkey := redisPolicyKey(policyHash)
	members, err := dc.redisClient.SMembers(dc.ctx, pkey).Result()
	if err != nil && err != redis.Nil {
		return err
	}

	if len(members) > 0 {
		keys := make([]string, 0, len(members)+1)
		for _, m := range members {
			keys = append(keys, redisDecisionKey(m))
		}
		keys = append(keys, pkey)
		return dc.redisClient.Del(dc.ctx, keys...).Err()
	}

	return dc.redisClient.Del(dc.ctx, pkey).Err()
}

// backgroundCleanup periodically removes expired items from the in-memory cache
func (dc *DecisionCache) backgroundCleanup() {
	ticker := time.NewTicker(time.Minute)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			dc.cleanupExpired()
		case <-dc.ctx.Done():
			return
		}
	}
}

// cleanupExpired removes expired items from the cache
func (dc *DecisionCache) cleanupExpired() {
	dc.mu.Lock()
	defer dc.mu.Unlock()

	now := time.Now()
	var keysToRemove []string

	for key, cached := range dc.inMemory {
		if now.After(cached.ExpiresAt) {
			keysToRemove = append(keysToRemove, key)
		}
	}

	for _, key := range keysToRemove {
		delete(dc.inMemory, key)
		delete(dc.keyToFreq, key)
	}
}

// redisSync periodically warms in-memory cache from Redis decision keys
func (dc *DecisionCache) redisSync() {
	ticker := time.NewTicker(30 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			dc.syncWithRedis()
		case <-dc.ctx.Done():
			return
		}
	}
}

// syncWithRedis performs a one-way sync from Redis to in-memory cache via SCAN
func (dc *DecisionCache) syncWithRedis() {
	if dc.redisClient == nil {
		return
	}

	var cursor uint64
	for {
		keys, next, err := dc.redisClient.Scan(dc.ctx, cursor, redisDecisionPrefix+"*", 64).Result()
		if err != nil {
			return
		}
		for _, fullKey := range keys {
			hashKey := fullKey[len(redisDecisionPrefix):]
			cached, ok := dc.getFromRedis(hashKey)
			if !ok {
				continue
			}
			dc.mu.Lock()
			if _, exists := dc.inMemory[hashKey]; !exists {
				dc.addToMemoryCache(hashKey, cached)
			}
			dc.mu.Unlock()
		}
		cursor = next
		if cursor == 0 {
			return
		}
	}
}
