use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::Arc,
    time::{Duration, SystemTime, UNIX_EPOCH},
};
use tokio::sync::RwLock;
use tracing::{debug, info};

use crate::SearchResult;

/// Cache key combining question hash and label set for semantic caching
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct CacheKey {
    pub question_hash: String,
    pub label_set: Vec<String>,
    pub tenant: String,
    /// Requested result count forms part of the authorization-sensitive cache key.
    pub result_limit: usize,
}

/// Cache entry storing search results with metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    pub key: CacheKey,
    pub results: Vec<SearchResult>,
    pub scores: Vec<f64>,
    pub created_at: u64,
    pub accessed_at: u64,
    pub access_count: u64,
    pub ttl_seconds: u64,
}

/// Cache statistics per tenant
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TenantCacheStats {
    pub tenant: String,
    pub total_queries: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub hit_rate: f64,
    pub total_cache_size: usize,
    pub avg_query_time_ms: f64,
    pub last_updated: u64,
}

/// Semantic cache implementation with tenant isolation
pub struct SemanticCache {
    /// Main cache storage: tenant -> (cache_key -> cache_entry)
    cache: Arc<RwLock<HashMap<String, HashMap<CacheKey, CacheEntry>>>>,
    
    /// Cache statistics per tenant
    stats: Arc<RwLock<HashMap<String, TenantCacheStats>>>,
    
    /// Configuration
    config: CacheConfig,
    
    /// Background cleanup task handle
    cleanup_handle: Option<tokio::task::JoinHandle<()>>,
}

/// Cache configuration
#[derive(Debug, Clone)]
pub struct CacheConfig {
    /// Default TTL for cache entries in seconds
    pub default_ttl_seconds: u64,
    
    /// Maximum cache size per tenant
    pub max_entries_per_tenant: usize,
    
    /// Maximum memory usage per tenant in bytes
    pub max_memory_per_tenant: usize,
    
    /// Cleanup interval in seconds
    pub cleanup_interval_seconds: u64,
    
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            default_ttl_seconds: 3600, // 1 hour
            max_entries_per_tenant: 1000,
            max_memory_per_tenant: 100 * 1024 * 1024, // 100 MB
            cleanup_interval_seconds: 300, // 5 minutes
        }
    }
}

impl SemanticCache {
    /// Create a new semantic cache with default configuration
    pub fn new() -> Self {
        Self::with_config(CacheConfig::default())
    }
    
    /// Create a new semantic cache with custom configuration
    pub fn with_config(config: CacheConfig) -> Self {
        let cache = Arc::new(RwLock::new(HashMap::new()));
        let stats = Arc::new(RwLock::new(HashMap::new()));
        
        let cleanup_handle = if config.cleanup_interval_seconds == 0 {
            None
        } else {
            let cache_clone = cache.clone();
            let stats_clone = stats.clone();
            let config_clone = config.clone();
            Some(tokio::spawn(async move {
                Self::cleanup_task(cache_clone, stats_clone, config_clone).await;
            }))
        };
        
        Self {
            cache,
            stats,
            config,
            cleanup_handle,
        }
    }
    
    /// Get cached results for a query
    pub async fn get(
        &self,
        question_hash: &str,
        label_set: &[String],
        tenant: &str,
        result_limit: usize,
    ) -> Option<Vec<SearchResult>> {
        let cache_key = CacheKey {
            question_hash: question_hash.to_string(),
            label_set: label_set.to_vec(),
            tenant: tenant.to_string(),
            result_limit,
        };

        let hit = {
            let cache = self.cache.read().await;
            let tenant_cache = cache.get(tenant)?;
            if let Some(entry) = tenant_cache.get(&cache_key) {
                if self.is_expired(entry) {
                    debug!("Cache entry expired for tenant {}: {:?}", tenant, cache_key);
                    return None;
                }
                Some(entry.results.clone())
            } else {
                // Authorization-sensitive reuse must match the entire cache key.
                None
            }
        };

        if let Some(results) = hit {
            self.update_access_stats(tenant, &cache_key).await;
            debug!("Cache hit for tenant {}: {:?}", tenant, cache_key);
            Some(results)
        } else {
            None
        }
    }
    
    /// Store results in cache
    pub async fn put(
        &self,
        question_hash: &str,
        label_set: &[String],
        tenant: &str,
        result_limit: usize,
        results: Vec<SearchResult>,
        ttl_seconds: Option<u64>,
    ) -> Result<()> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let cache_key = CacheKey {
            question_hash: question_hash.to_string(),
            label_set: label_set.to_vec(),
            tenant: tenant.to_string(),
            result_limit,
        };
        
        let scores: Vec<f64> = results.iter().map(|r| r.score).collect();
        
        let entry = CacheEntry {
            key: cache_key.clone(),
            results: results.clone(),
            scores,
            created_at: now,
            accessed_at: now,
            access_count: 1,
            ttl_seconds: ttl_seconds.unwrap_or(self.config.default_ttl_seconds),
        };
        
        {
            let mut cache = self.cache.write().await;
            let tenant_cache = cache.entry(tenant.to_string()).or_insert_with(HashMap::new);

            if tenant_cache.len() >= self.config.max_entries_per_tenant {
                self.evict_entries(tenant, tenant_cache).await;
            }

            tenant_cache.insert(cache_key.clone(), entry);
        }

        self.update_put_stats(tenant).await;

        debug!("Cached results for tenant {}: {:?}", tenant, cache_key);
        Ok(())
    }
    
    /// Invalidate cache entries for a tenant (e.g., on index update)
    pub async fn invalidate_tenant(&self, tenant: &str) -> Result<()> {
        // Release the cache guard before taking the statistics lock.
        // Other update paths take these locks in separate scopes as well.
        let removed = {
            self.cache.write().await.remove(tenant).is_some()
        };

        if removed {
            info!("Invalidated all cache entries for tenant: {}", tenant);
            
            // Update statistics
            let mut stats = self.stats.write().await;
            if let Some(tenant_stats) = stats.get_mut(tenant) {
                tenant_stats.total_cache_size = 0;
                tenant_stats.last_updated = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
            }
        }
        
        Ok(())
    }
    
    /// Invalidate specific cache entries based on pattern
    pub async fn invalidate_pattern(
        &self,
        tenant: &str,
        pattern: &str,
    ) -> Result<usize> {
        let mut cache = self.cache.write().await;
        let tenant_cache = cache.get_mut(tenant);
        
        if let Some(tenant_cache) = tenant_cache {
            let keys_to_remove: Vec<CacheKey> = tenant_cache
                .keys()
                .filter(|key| {
                    key.question_hash.contains(pattern) || 
                    key.label_set.iter().any(|label| label.contains(pattern))
                })
                .cloned()
                .collect();
            
            let removed_count = keys_to_remove.len();
            for key in keys_to_remove {
                tenant_cache.remove(&key);
            }
            
            if removed_count > 0 {
                info!("Invalidated {} cache entries for tenant {} with pattern: {}", 
                      removed_count, tenant, pattern);
            }
            
            Ok(removed_count)
        } else {
            Ok(0)
        }
    }
    
    /// Get cache statistics for a tenant
    pub async fn get_tenant_stats(&self, tenant: &str) -> Option<TenantCacheStats> {
        let stats = self.stats.read().await;
        stats.get(tenant).cloned()
    }
    
    /// Get all tenant statistics
    pub async fn get_all_stats(&self) -> Vec<TenantCacheStats> {
        let stats = self.stats.read().await;
        stats.values().cloned().collect()
    }
    
    /// Check if a cache entry is expired
    fn is_expired(&self, entry: &CacheEntry) -> bool {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        now > entry.created_at + entry.ttl_seconds
    }
    
    /// Evict entries when cache is full
    async fn evict_entries(
        &self,
        tenant: &str,
        tenant_cache: &mut HashMap<CacheKey, CacheEntry>,
    ) {
        // LRU eviction based on access time and count
        let mut entries: Vec<(&CacheKey, &CacheEntry)> = tenant_cache.iter().collect();
        entries.sort_by(|(_, a), (_, b)| {
            // Sort by access count (descending) then by access time (ascending)
            b.access_count.cmp(&a.access_count)
                .then(a.accessed_at.cmp(&b.accessed_at))
        });
        
        // Remove oldest/least accessed entries
        let to_remove = entries.len().saturating_sub(self.config.max_entries_per_tenant) + 1;
        let keys_to_remove: Vec<CacheKey> = entries
            .iter()
            .take(to_remove)
            .map(|(key, _)| (*key).clone())
            .collect();
        for key in keys_to_remove {
            tenant_cache.remove(&key);
        }
        
        debug!("Evicted {} entries from cache for tenant {}", to_remove, tenant);
    }
    
    /// Update access statistics
    async fn update_access_stats(&self, tenant: &str, cache_key: &CacheKey) {
        {
            let mut cache = self.cache.write().await;
            if let Some(tenant_cache) = cache.get_mut(tenant) {
                if let Some(entry) = tenant_cache.get_mut(cache_key) {
                    entry.accessed_at = SystemTime::now()
                        .duration_since(UNIX_EPOCH)
                        .unwrap()
                        .as_secs();
                    entry.access_count += 1;
                }
            }
        }

        let mut stats = self.stats.write().await;
        let tenant_stats = stats.entry(tenant.to_string()).or_insert_with(|| TenantCacheStats {
            tenant: tenant.to_string(),
            total_queries: 0,
            cache_hits: 0,
            cache_misses: 0,
            hit_rate: 0.0,
            total_cache_size: 0,
            avg_query_time_ms: 0.0,
            last_updated: 0,
        });
        
        tenant_stats.cache_hits += 1;
        tenant_stats.total_queries += 1;
        tenant_stats.hit_rate = tenant_stats.cache_hits as f64 / tenant_stats.total_queries as f64;
        tenant_stats.last_updated = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
    }
    
    /// Update put statistics
    async fn update_put_stats(&self, tenant: &str) {
        // Snapshot the cache size before acquiring stats. The previous
        // stats-write -> cache-read order could deadlock with invalidation
        // and cleanup, which acquired these locks in the opposite order.
        let cache_size = {
            let cache = self.cache.read().await;
            cache.get(tenant).map_or(0, HashMap::len)
        };
        let mut stats = self.stats.write().await;
        let tenant_stats = stats.entry(tenant.to_string()).or_insert_with(|| TenantCacheStats {
            tenant: tenant.to_string(),
            total_queries: 0,
            cache_hits: 0,
            cache_misses: 0,
            hit_rate: 0.0,
            total_cache_size: 0,
            avg_query_time_ms: 0.0,
            last_updated: 0,
        });
        
        tenant_stats.total_cache_size = cache_size;
        
        tenant_stats.last_updated = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
    }
    
    /// Background cleanup task
    async fn cleanup_task(
        cache: Arc<RwLock<HashMap<String, HashMap<CacheKey, CacheEntry>>>>,
        stats: Arc<RwLock<HashMap<String, TenantCacheStats>>>,
        config: CacheConfig,
    ) {
        let mut interval = tokio::time::interval(Duration::from_secs(config.cleanup_interval_seconds));
        
        loop {
            interval.tick().await;
            
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs();
            
            // Never hold both RwLocks at once. Retain only ordinary numeric
            // snapshots while updating the per-tenant statistics separately.
            let sizes: Vec<(String, usize)> = {
                let mut cache = cache.write().await;
                for entries in cache.values_mut() {
                    entries.retain(|_, entry| {
                        now <= entry.created_at.saturating_add(entry.ttl_seconds)
                    });
                }
                cache.iter().map(|(tenant, entries)| (tenant.clone(), entries.len())).collect()
            };

            let mut stats = stats.write().await;
            for (tenant, size) in sizes {
                if let Some(tenant_stats) = stats.get_mut(&tenant) {
                    tenant_stats.total_cache_size = size;
                    tenant_stats.last_updated = now;
                }
            }

            debug!("Cache cleanup completed");
        }
    }
}

impl Drop for SemanticCache {
    fn drop(&mut self) {
        if let Some(handle) = self.cleanup_handle.take() {
            handle.abort();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SearchResult;
    use std::collections::HashMap;
    
    #[tokio::test]
    async fn test_cache_basic_operations() {
        let cache = SemanticCache::with_config(CacheConfig {
            cleanup_interval_seconds: 0,
            ..CacheConfig::default()
        });
        let tenant = "test-tenant";
        let question_hash = "test-hash";
        let labels = vec!["label1".to_string(), "label2".to_string()];
        
        let results = vec![
            SearchResult {
                document_id: "doc1".to_string(),
                content: "test content".to_string(),
                content_hash: "hash1".to_string(),
                score: 0.9,
                metadata: HashMap::new(),
                labels: vec!["label1".to_string()],
            }
        ];
        
        // Test put
        cache.put(question_hash, &labels, tenant, results.clone(), None).await.unwrap();
        
        // Test get
        let cached = cache.get(question_hash, &labels, tenant).await;
        assert!(cached.is_some());
        assert_eq!(cached.unwrap().len(), 1);
        
        // Test statistics
        let stats = cache.get_tenant_stats(tenant).await;
        assert!(stats.is_some());
        let stats = stats.unwrap();
        assert_eq!(stats.cache_hits, 1);
        assert_eq!(stats.total_queries, 1);
        assert_eq!(stats.hit_rate, 1.0);
    }
    
    #[tokio::test]
    async fn test_cache_tenant_isolation() {
        let cache = SemanticCache::with_config(CacheConfig {
            cleanup_interval_seconds: 0,
            ..CacheConfig::default()
        });
        let tenant1 = "tenant1";
        let tenant2 = "tenant2";
        let question_hash = "test-hash";
        let labels = vec!["label1".to_string()];
        
        let results = vec![
            SearchResult {
                document_id: "doc1".to_string(),
                content: "test content".to_string(),
                content_hash: "hash1".to_string(),
                score: 0.9,
                metadata: HashMap::new(),
                labels: vec![],
            }
        ];
        
        // Put in tenant1
        cache.put(question_hash, &labels, tenant1, results.clone(), None).await.unwrap();
        
        // Should not find in tenant2
        let cached = cache.get(question_hash, &labels, tenant2).await;
        assert!(cached.is_none());
        
        // Should find in tenant1
        let cached = cache.get(question_hash, &labels, tenant1).await;
        assert!(cached.is_some());
    }
    
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn concurrent_access_put_invalidate_and_cleanup_do_not_deadlock() {
        let cache = Arc::new(SemanticCache::with_config(CacheConfig {
            cleanup_interval_seconds: 1,
            max_entries_per_tenant: 16,
            ..CacheConfig::default()
        }));
        let mut work = Vec::new();
        let labels = vec!["public".to_string()];
        for worker in 0..6 {
            let cache = Arc::clone(&cache);
            let labels = labels.clone();
            work.push(tokio::spawn(async move {
                for iteration in 0..150 {
                    let tenant = if iteration % 2 == 0 { "tenant-a" } else { "tenant-b" };
                    let query_hash = format!("query-{}", iteration % 12);
                    match worker % 3 {
                        0 => {
                            cache.put(
                                &query_hash, &labels, tenant,
                                vec![SearchResult {
                                    document_id: "synthetic".into(),
                                    content: "synthetic".into(),
                                    content_hash: "hash".into(),
                                    score: 1.0,
                                    metadata: HashMap::new(),
                                    labels: labels.clone(),
                                }],
                                None,
                            ).await.unwrap();
                        }
                        1 => {
                            let _ = cache.get(&query_hash, &labels, tenant).await;
                        }
                        _ => {
                            cache.invalidate_tenant(tenant).await.unwrap();
                        }
                    }
                    tokio::task::yield_now().await;
                }
            }));
        }
        tokio::time::timeout(Duration::from_secs(15), async {
            for task in work {
                task.await.unwrap();
            }
        }).await.expect("Concurrent cache operations deadlocked");
    }

    #[tokio::test]
    async fn test_cache_invalidation() {
        let cache = SemanticCache::with_config(CacheConfig {
            cleanup_interval_seconds: 0,
            ..CacheConfig::default()
        });
        let tenant = "test-tenant";
        let question_hash = "test-hash";
        let labels = vec!["label1".to_string()];
        
        let results = vec![
            SearchResult {
                document_id: "doc1".to_string(),
                content: "test content".to_string(),
                content_hash: "hash1".to_string(),
                score: 0.9,
                metadata: HashMap::new(),
                labels: vec![],
            }
        ];
        
        // Put and verify
        cache.put(question_hash, &labels, tenant, results.clone(), None).await.unwrap();
        assert!(cache.get(question_hash, &labels, tenant).await.is_some());
        
        // Invalidate tenant
        cache.invalidate_tenant(tenant).await.unwrap();
        assert!(cache.get(question_hash, &labels, tenant).await.is_none());
    }
}
