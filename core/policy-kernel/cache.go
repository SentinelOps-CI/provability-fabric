package policykernel

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"sync"
	"time"
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
	redisClient interface{} // Will be properly typed when Redis is available
	stats       CacheStats
	ctx         context.Context
	cancel      context.CancelFunc
}

// NewDecisionCache creates a new decision cache instance
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

	// Initialize Redis client if address is provided
	if redisAddr != "" {
		// TODO: Initialize Redis client when Redis dependency is available
		// cache.redisClient = redis.NewClient(&redis.Options{
		//     Addr:     redisAddr,
		//     Password: "",
		//     DB:       0,
		// })

		// Start background cleanup and Redis sync
		go cache.backgroundCleanup()
		go cache.redisSync()
	}

	return cache
}

// Get retrieves a cached decision if it exists and is valid
func (dc *DecisionCache) Get(key CacheKey) (*Decision, bool) {
	cacheKey := key.String()

	// Try in-memory cache first
	dc.mu.RLock()
	if cached, exists := dc.inMemory[cacheKey]; exists {
		if time.Now().Before(cached.ExpiresAt) {
			// Update access metrics
			cached.AccessCount++
			cached.LastAccess = time.Now()

			// Update frequency for LFU
			dc.updateFrequency(cacheKey, cached.AccessCount)

			dc.mu.RUnlock()

			// Update stats
			dc.updateStats(true)

			return &cached.Decision, true
		} else {
			// Expired, remove from cache
			dc.mu.RUnlock()
			dc.mu.Lock()
			delete(dc.inMemory, cacheKey)
			delete(dc.keyToFreq, cacheKey)
			dc.mu.Unlock()
		}
	}
	dc.mu.RUnlock()

	// Try Redis if available
	if dc.redisClient != nil {
		if cached, exists := dc.getFromRedis(cacheKey); exists {
			// Add back to in-memory cache
			dc.mu.Lock()
			dc.addToMemoryCache(cacheKey, cached)
			dc.mu.Unlock()

			dc.updateStats(true)
			return &cached.Decision, true
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
		ExpiresAt:   time.Now().Add(dc.ttl),
		AccessCount: 1,
		LastAccess:  time.Now(),
		CreatedAt:   time.Now(),
	}

	// Add to in-memory cache
	dc.mu.Lock()
	dc.addToMemoryCache(cacheKey, cached)
	dc.mu.Unlock()

	// Add to Redis if available
	if dc.redisClient != nil {
		return dc.setToRedis(cacheKey, cached)
	}

	return nil
}

// InvalidateByPolicyHash removes all cached decisions for a specific policy
func (dc *DecisionCache) InvalidateByPolicyHash(policyHash string) error {
	dc.mu.Lock()
	defer dc.mu.Unlock()

	// Find and remove all keys with matching policy hash
	var keysToRemove []string
	for keyStr := range dc.inMemory {
		// Parse the key to extract policy hash
		if key, err := dc.parseCacheKey(keyStr); err == nil && key.PolicyHash == policyHash {
			keysToRemove = append(keysToRemove, keyStr)
		}
	}

	// Remove from in-memory cache
	for _, key := range keysToRemove {
		delete(dc.inMemory, key)
		delete(dc.keyToFreq, key)
	}

	// Remove from Redis if available
	if dc.redisClient != nil {
		// TODO: Implement Redis deletion when Redis client is properly typed
		// for _, key := range keysToRemove {
		//     dc.redisClient.Del(dc.ctx, key)
		// }
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
		// TODO: Implement Redis close when Redis client is properly typed
		// return dc.redisClient.Close()
	}

	return nil
}

// addToMemoryCache adds an item to the in-memory cache with LFU eviction
func (dc *DecisionCache) addToMemoryCache(key string, cached *CachedDecision) {
	// If cache is full, evict least frequently used item
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

// getFromRedis retrieves a cached decision from Redis
func (dc *DecisionCache) getFromRedis(key string) (*CachedDecision, bool) {
	// TODO: Implement Redis get when Redis client is properly typed
	// data, err := dc.redisClient.Get(dc.ctx, key).Bytes()
	// if err != nil {
	//     return nil, false
	// }
	//
	// var cached CachedDecision
	// if err := json.Unmarshal(data, &cached); err != nil {
	//     return nil, false
	// }
	//
	// // Check if expired
	// if time.Now().After(cached.ExpiresAt) {
	//     dc.redisClient.Del(dc.ctx, key)
	//     return nil, false
	// }
	//
	// return &cached, true
	return nil, false
}

// setToRedis stores a cached decision in Redis
func (dc *DecisionCache) setToRedis(key string, cached *CachedDecision) error {
	// TODO: Implement Redis set when Redis client is properly typed
	// data, err := json.Marshal(cached)
	// if err != nil {
	//     return err
	// }
	//
	// ttl := time.Until(cached.ExpiresAt)
	// return dc.redisClient.Set(dc.ctx, key, data, ttl).Err()
	return nil
}

// parseCacheKey attempts to parse a cache key string back to CacheKey struct
func (dc *DecisionCache) parseCacheKey(keyStr string) (*CacheKey, error) {
	// This is a simplified implementation - in practice, you might want to store
	// the original key components separately or use a different serialization approach
	return nil, fmt.Errorf("key parsing not implemented")
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

// redisSync synchronizes the in-memory cache with Redis
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

// syncWithRedis performs a one-way sync from Redis to in-memory cache
func (dc *DecisionCache) syncWithRedis() {
	// This is a placeholder for Redis synchronization logic
	// In practice, you might want to implement pub/sub for real-time updates
}
