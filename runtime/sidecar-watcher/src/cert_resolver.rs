/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * you may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

use super::cert_v1_core::CertV1Core;
use super::cert_v1_extended::CertV1Extended;

/// Certificate type enumeration
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CertificateType {
    Core(CertV1Core),
    Extended(CertV1Extended),
}

/// Certificate resolver that transparently handles both core and extended certificates
pub struct CertResolver {
    /// Core certificates cache (hot path)
    core_cache: Arc<RwLock<HashMap<String, CertV1Core>>>,

    /// Extended certificates cache (async)
    extended_cache: Arc<RwLock<HashMap<String, CertV1Extended>>>,

    /// Pending extended certificate generation
    pending_extended: Arc<RwLock<HashMap<String, bool>>>,
}

impl CertResolver {
    /// Create a new certificate resolver
    pub fn new() -> Self {
        Self {
            core_cache: Arc::new(RwLock::new(HashMap::new())),
            extended_cache: Arc::new(RwLock::new(HashMap::new())),
            pending_extended: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Store a core certificate (synchronous, hot path)
    pub async fn store_core(&self, cert: CertV1Core) -> Result<(), String> {
        // Validate certificate
        cert.validate()?;

        // Store in cache
        let key = self.generate_cert_key(&cert.bundle_id, &cert.session_id);
        let mut cache = self.core_cache.write().await;
        cache.insert(key.clone(), cert);

        // Mark as pending for extended generation
        let mut pending = self.pending_extended.write().await;
        pending.insert(key, true);

        Ok(())
    }

    /// Store an extended certificate (asynchronous)
    pub async fn store_extended(&self, cert: CertV1Extended) -> Result<(), String> {
        // Validate core certificate
        cert.core.validate()?;

        // Store in cache
        let key = self.generate_cert_key(&cert.core.bundle_id, &cert.core.session_id);
        let mut cache = self.extended_cache.write().await;
        cache.insert(key.clone(), cert);

        // Mark as no longer pending
        let mut pending = self.pending_extended.write().await;
        pending.remove(&key);

        Ok(())
    }

    /// Get a certificate (transparently resolves core or extended)
    pub async fn get_certificate(
        &self,
        bundle_id: &str,
        session_id: &str,
    ) -> Option<CertificateType> {
        let key = self.generate_cert_key(bundle_id, session_id);

        // First try to get extended certificate
        {
            let extended_cache = self.extended_cache.read().await;
            if let Some(extended) = extended_cache.get(&key) {
                return Some(CertificateType::Extended(extended.clone()));
            }
        }

        // Fall back to core certificate
        {
            let core_cache = self.core_cache.read().await;
            if let Some(core) = core_cache.get(&key) {
                return Some(CertificateType::Core(core.clone()));
            }
        }

        None
    }

    /// Get core certificate only
    pub async fn get_core(&self, bundle_id: &str, session_id: &str) -> Option<CertV1Core> {
        let key = self.generate_cert_key(bundle_id, session_id);
        let cache = self.core_cache.read().await;
        cache.get(&key).cloned()
    }

    /// Get extended certificate only
    pub async fn get_extended(&self, bundle_id: &str, session_id: &str) -> Option<CertV1Extended> {
        let key = self.generate_cert_key(bundle_id, session_id);
        let cache = self.extended_cache.read().await;
        cache.get(&key).cloned()
    }

    /// Check if extended certificate is pending
    pub async fn is_extended_pending(&self, bundle_id: &str, session_id: &str) -> bool {
        let key = self.generate_cert_key(bundle_id, session_id);
        let pending = self.pending_extended.read().await;
        pending.get(&key).copied().unwrap_or(false)
    }

    /// Get certificate summary (works for both types)
    pub async fn get_certificate_summary(
        &self,
        bundle_id: &str,
        session_id: &str,
    ) -> Option<CertificateSummary> {
        match self.get_certificate(bundle_id, session_id).await? {
            CertificateType::Core(core) => Some(CertificateSummary::from_core(core)),
            CertificateType::Extended(extended) => {
                Some(CertificateSummary::from_extended(extended))
            }
        }
    }

    /// Search certificates by criteria
    pub async fn search_certificates(&self, criteria: &SearchCriteria) -> Vec<CertificateType> {
        let mut results = Vec::new();

        // Search core certificates
        {
            let core_cache = self.core_cache.read().await;
            for cert in core_cache.values() {
                if self.matches_criteria(cert, criteria) {
                    results.push(CertificateType::Core(cert.clone()));
                }
            }
        }

        // Search extended certificates
        {
            let extended_cache = self.extended_cache.read().await;
            for cert in extended_cache.values() {
                if self.matches_criteria(&cert.core, criteria) {
                    results.push(CertificateType::Extended(cert.clone()));
                }
            }
        }

        // Sort by timestamp (newest first)
        results.sort_by(|a, b| {
            let timestamp_a = match a {
                CertificateType::Core(core) => core.timestamp,
                CertificateType::Extended(extended) => extended.core.timestamp,
            };
            let timestamp_b = match b {
                CertificateType::Core(core) => core.timestamp,
                CertificateType::Extended(extended) => extended.core.timestamp,
            };
            timestamp_b.cmp(&timestamp_a)
        });

        // Apply limit
        if let Some(limit) = criteria.limit {
            results.truncate(limit);
        }

        results
    }

    /// Generate certificate key
    fn generate_cert_key(&self, bundle_id: &str, session_id: &str) -> String {
        format!("{}:{}", bundle_id, session_id)
    }

    /// Check if certificate matches search criteria
    fn matches_criteria(&self, cert: &CertV1Core, criteria: &SearchCriteria) -> bool {
        if let Some(ref tenant_id) = criteria.tenant_id {
            if cert.tenant_id != *tenant_id {
                return false;
            }
        }

        if let Some(ref policy_hash) = criteria.policy_hash {
            if cert.policy_hash != *policy_hash {
                return false;
            }
        }

        if let Some(ref ni_monitor) = criteria.ni_monitor {
            if cert.ni_monitor != *ni_monitor {
                return false;
            }
        }

        if let Some(start_time) = criteria.start_time {
            if cert.timestamp < start_time {
                return false;
            }
        }

        if let Some(end_time) = criteria.end_time {
            if cert.timestamp > end_time {
                return false;
            }
        }

        true
    }

    /// Get cache statistics
    pub async fn get_cache_stats(&self) -> CacheStats {
        let core_count = self.core_cache.read().await.len();
        let extended_count = self.extended_cache.read().await.len();
        let pending_count = self.pending_extended.read().await.len();

        CacheStats {
            core_certificates: core_count,
            extended_certificates: extended_count,
            pending_extended: pending_count,
        }
    }
}

/// Certificate summary for display
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateSummary {
    pub bundle_id: String,
    pub session_id: String,
    pub tenant_id: String,
    pub ni_monitor: String,
    pub reason_code: String,
    pub timestamp: u64,
    pub epoch: u64,
    pub is_extended: bool,
    pub size_bytes: usize,
}

impl CertificateSummary {
    pub fn from_core(core: CertV1Core) -> Self {
        Self {
            bundle_id: core.bundle_id.clone(),
            session_id: core.session_id.clone(),
            tenant_id: core.tenant_id.clone(),
            ni_monitor: core.ni_monitor.clone(),
            reason_code: core.reason_code.clone(),
            timestamp: core.timestamp,
            epoch: core.epoch,
            is_extended: false,
            size_bytes: core.size_bytes(),
        }
    }

    pub fn from_extended(extended: CertV1Extended) -> Self {
        Self {
            bundle_id: extended.core.bundle_id.clone(),
            session_id: extended.core.session_id.clone(),
            tenant_id: extended.core.tenant_id.clone(),
            ni_monitor: extended.core.ni_monitor.clone(),
            reason_code: extended.core.reason_code.clone(),
            timestamp: extended.core.timestamp,
            epoch: extended.core.epoch,
            is_extended: true,
            size_bytes: extended.size_bytes(),
        }
    }
}

/// Search criteria
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchCriteria {
    pub tenant_id: Option<String>,
    pub policy_hash: Option<String>,
    pub ni_monitor: Option<String>,
    pub start_time: Option<u64>,
    pub end_time: Option<u64>,
    pub limit: Option<usize>,
}

/// Cache statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStats {
    pub core_certificates: usize,
    pub extended_certificates: usize,
    pub pending_extended: usize,
}

impl Default for CertResolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_cert_resolver_core_storage() {
        let resolver = CertResolver::new();

        let core = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        assert!(resolver.store_core(core).await.is_ok());

        let retrieved = resolver.get_core("bundle-123", "session-1").await;
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().bundle_id, "bundle-123");
    }

    #[tokio::test]
    async fn test_cert_resolver_extended_storage() {
        let resolver = CertResolver::new();

        let core = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        let extended = CertV1Extended::from_core(core);

        assert!(resolver.store_extended(extended).await.is_ok());

        let retrieved = resolver.get_extended("bundle-123", "session-1").await;
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().core.bundle_id, "bundle-123");
    }

    #[tokio::test]
    async fn test_cert_resolver_transparent_resolution() {
        let resolver = CertResolver::new();

        let core = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        resolver.store_core(core).await.unwrap();

        let cert = resolver.get_certificate("bundle-123", "session-1").await;
        assert!(cert.is_some());

        match cert.unwrap() {
            CertificateType::Core(core) => {
                assert_eq!(core.bundle_id, "bundle-123");
            }
            CertificateType::Extended(_) => {
                panic!("Expected core certificate");
            }
        }
    }

    #[tokio::test]
    async fn test_cert_resolver_search() {
        let resolver = CertResolver::new();

        let core1 = CertV1Core::new(
            "bundle-1".to_string(),
            1,
            "policy-hash-1".to_string(),
            "proof-hash-1".to_string(),
            "automata-hash-1".to_string(),
            "labeler-hash-1".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        let core2 = CertV1Core::new(
            "bundle-2".to_string(),
            2,
            "policy-hash-2".to_string(),
            "proof-hash-2".to_string(),
            "automata-hash-2".to_string(),
            "labeler-hash-2".to_string(),
            "reject".to_string(),
            42,
            "DENY".to_string(),
            "tenant-1".to_string(),
            "session-2".to_string(),
        );

        resolver.store_core(core1).await.unwrap();
        resolver.store_core(core2).await.unwrap();

        let criteria = SearchCriteria {
            tenant_id: Some("tenant-1".to_string()),
            policy_hash: None,
            ni_monitor: None,
            start_time: None,
            end_time: None,
            limit: Some(10),
        };

        let results = resolver.search_certificates(&criteria).await;
        assert_eq!(results.len(), 2);
    }

    #[tokio::test]
    async fn test_cert_resolver_cache_stats() {
        let resolver = CertResolver::new();

        let core = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        resolver.store_core(core).await.unwrap();

        let stats = resolver.get_cache_stats().await;
        assert_eq!(stats.core_certificates, 1);
        assert_eq!(stats.extended_certificates, 0);
        assert_eq!(stats.pending_extended, 1);
    }
}
