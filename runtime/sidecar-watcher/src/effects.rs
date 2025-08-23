/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::error::Error;
use std::time::{Duration, Instant};
use uuid::Uuid;

/// Effect type enumeration
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EffectType {
    HttpGet,
    FileRead,
    FileWrite,
    NetworkConnect,
    ProcessCreate,
    DatabaseQuery,
    ApiCall,
    LogWrite,
    Declassify,
    Emit,
    Retrieve,
}

impl EffectType {
    pub fn to_string(&self) -> &'static str {
        match self {
            EffectType::HttpGet => "http_get",
            EffectType::FileRead => "file_read",
            EffectType::FileWrite => "file_write",
            EffectType::NetworkConnect => "network_connect",
            EffectType::ProcessCreate => "process_create",
            EffectType::DatabaseQuery => "database_query",
            EffectType::ApiCall => "api_call",
            EffectType::LogWrite => "log_write",
            EffectType::Declassify => "declassify",
            EffectType::Emit => "emit",
            EffectType::Retrieve => "retrieve",
        }
    }

    pub fn from_string(s: &str) -> Result<Self, String> {
        match s {
            "http_get" => Ok(EffectType::HttpGet),
            "file_read" => Ok(EffectType::FileRead),
            "file_write" => Ok(EffectType::FileWrite),
            "network_connect" => Ok(EffectType::NetworkConnect),
            "process_create" => Ok(EffectType::ProcessCreate),
            "database_query" => Ok(EffectType::DatabaseQuery),
            "api_call" => Ok(EffectType::ApiCall),
            "log_write" => Ok(EffectType::LogWrite),
            "declassify" => Ok(EffectType::Declassify),
            "emit" => Ok(EffectType::Emit),
            "retrieve" => Ok(EffectType::Retrieve),
            _ => Err(format!("Unknown effect type: {}", s)),
        }
    }
}

/// Effect signature with security constraints
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EffectSignature {
    pub effect_id: String,
    pub effect_type: EffectType,
    pub resource: String,
    pub constraints: EffectConstraints,
    pub metadata: HashMap<String, String>,
    pub created_at: u64,
    pub expires_at: Option<u64>,
}

/// Effect constraints for security enforcement
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EffectConstraints {
    pub rate_limit: Option<RateLimit>,
    pub resource_limits: Option<ResourceLimits>,
    pub network_restrictions: Option<NetworkRestrictions>,
    pub file_restrictions: Option<FileRestrictions>,
    pub process_restrictions: Option<ProcessRestrictions>,
}

/// Rate limiting constraints
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimit {
    pub max_operations: u32,
    pub window_ms: u32,
    pub tolerance_ms: u32,
}

/// Resource usage limits
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_time_ms: u64,
    pub max_disk_io_mb: u64,
}

/// Network access restrictions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkRestrictions {
    pub allowed_domains: Vec<String>,
    pub allowed_ports: Vec<u16>,
    pub allowed_protocols: Vec<String>,
    pub max_connections: u32,
}

/// File access restrictions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileRestrictions {
    pub allowed_paths: Vec<String>,
    pub allowed_extensions: Vec<String>,
    pub max_file_size_mb: u64,
    pub read_only: bool,
}

/// Process creation restrictions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessRestrictions {
    pub allowed_commands: Vec<String>,
    pub max_processes: u32,
    pub timeout_ms: u32,
}

/// Effect allow-list manager
pub struct EffectsAllowList {
    allowed_effects: HashMap<String, EffectSignature>,
    effect_usage: HashMap<String, Vec<EffectUsage>>,
    last_cleanup: Instant,
}

/// Effect usage tracking
#[derive(Debug, Clone)]
struct EffectUsage {
    timestamp: u64,
    resource: String,
    success: bool,
    duration_ms: u64,
}

impl EffectsAllowList {
    /// Create new effects allow-list
    pub fn new() -> Self {
        Self {
            allowed_effects: HashMap::new(),
            effect_usage: HashMap::new(),
            last_cleanup: Instant::now(),
        }
    }

    /// Add effect to allow-list
    pub fn allow_effect(&mut self, effect: EffectSignature) -> Result<(), Box<dyn Error>> {
        // Validate effect signature
        self.validate_effect_signature(&effect)?;

        // Check for conflicts
        if self.allowed_effects.contains_key(&effect.effect_id) {
            return Err("Effect ID already exists".into());
        }

        // Add to allow-list
        self.allowed_effects
            .insert(effect.effect_id.clone(), effect);

        Ok(())
    }

    /// Remove effect from allow-list
    pub fn remove_effect(&mut self, effect_id: &str) -> Result<(), Box<dyn Error>> {
        if !self.allowed_effects.contains_key(effect_id) {
            return Err("Effect not found".into());
        }

        self.allowed_effects.remove(effect_id);
        self.effect_usage.remove(effect_id);

        Ok(())
    }

    /// Check if effect is allowed
    pub fn is_effect_allowed(&self, effect_type: &EffectType, resource: &str) -> bool {
        self.allowed_effects.values().any(|effect| {
            effect.effect_type == *effect_type
                && (effect.resource == resource || effect.resource == "*")
                && !effect.is_expired()
        })
    }

    /// Validate effect signature
    fn validate_effect_signature(&self, effect: &EffectSignature) -> Result<(), Box<dyn Error>> {
        // Check required fields
        if effect.effect_id.is_empty() {
            return Err("Effect ID cannot be empty".into());
        }

        if effect.resource.is_empty() {
            return Err("Resource cannot be empty".into());
        }

        // Validate constraints
        if let Some(rate_limit) = &effect.constraints.rate_limit {
            if rate_limit.max_operations == 0 || rate_limit.window_ms == 0 {
                return Err("Invalid rate limit constraints".into());
            }
        }

        if let Some(resource_limits) = &effect.constraints.resource_limits {
            if resource_limits.max_memory_mb == 0 || resource_limits.max_cpu_time_ms == 0 {
                return Err("Invalid resource limits".into());
            }
        }

        Ok(())
    }

    /// Record effect usage
    pub fn record_usage(
        &mut self,
        effect_id: &str,
        resource: &str,
        success: bool,
        duration_ms: u64,
    ) {
        let usage = EffectUsage {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            resource: resource.to_string(),
            success,
            duration_ms,
        };

        self.effect_usage
            .entry(effect_id.to_string())
            .or_insert_with(Vec::new)
            .push(usage);

        // Cleanup old usage records periodically
        self.cleanup_old_usage();
    }

    /// Cleanup old usage records
    fn cleanup_old_usage(&mut self) {
        let now = Instant::now();
        if now.duration_since(self.last_cleanup) < Duration::from_secs(3600) {
            return; // Only cleanup every hour
        }

        let cutoff_time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs()
            - 86400; // Keep last 24 hours

        for usage_list in self.effect_usage.values_mut() {
            usage_list.retain(|usage| usage.timestamp >= cutoff_time);
        }

        self.last_cleanup = now;
    }

    /// Get effect statistics
    pub fn get_effect_stats(&self, effect_id: &str) -> Option<EffectStats> {
        let effect = self.allowed_effects.get(effect_id)?;
        let usage_list = self.effect_usage.get(effect_id)?;

        let total_operations = usage_list.len() as u32;
        let successful_operations = usage_list.iter().filter(|u| u.success).count() as u32;
        let failed_operations = total_operations - successful_operations;

        let avg_duration = if total_operations > 0 {
            usage_list.iter().map(|u| u.duration_ms).sum::<u64>() / total_operations as u64
        } else {
            0
        };

        Some(EffectStats {
            effect_id: effect_id.to_string(),
            effect_type: effect.effect_type.clone(),
            total_operations,
            successful_operations,
            failed_operations,
            avg_duration_ms: avg_duration,
            last_used: usage_list.last().map(|u| u.timestamp),
        })
    }

    /// Get all allowed effects
    pub fn get_allowed_effects(&self) -> Vec<&EffectSignature> {
        self.allowed_effects.values().collect()
    }

    /// Check if any effects are expired
    pub fn has_expired_effects(&self) -> bool {
        self.allowed_effects
            .values()
            .any(|effect| effect.is_expired())
    }
}

impl EffectSignature {
    /// Check if effect is expired
    pub fn is_expired(&self) -> bool {
        if let Some(expires_at) = self.expires_at {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();
            now > expires_at
        } else {
            false
        }
    }

    /// Create new effect signature
    pub fn new(effect_type: EffectType, resource: String) -> Self {
        Self {
            effect_id: Uuid::new_v4().to_string(),
            effect_type,
            resource,
            constraints: EffectConstraints {
                rate_limit: None,
                resource_limits: None,
                network_restrictions: None,
                file_restrictions: None,
                process_restrictions: None,
            },
            metadata: HashMap::new(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            expires_at: None,
        }
    }
}

/// Effect statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EffectStats {
    pub effect_id: String,
    pub effect_type: EffectType,
    pub total_operations: u32,
    pub successful_operations: u32,
    pub failed_operations: u32,
    pub avg_duration_ms: u64,
    pub last_used: Option<u64>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_effect_allow_list() {
        let mut allow_list = EffectsAllowList::new();

        let effect = EffectSignature::new(EffectType::HttpGet, "https://example.com".to_string());
        assert!(allow_list.allow_effect(effect).is_ok());

        assert!(allow_list.is_effect_allowed(&EffectType::HttpGet, "https://example.com"));
        assert!(!allow_list.is_effect_allowed(&EffectType::FileWrite, "/tmp/test"));
    }

    #[test]
    fn test_effect_validation() {
        let mut allow_list = EffectsAllowList::new();

        let mut invalid_effect = EffectSignature::new(EffectType::HttpGet, "".to_string());
        invalid_effect.effect_id = "".to_string();

        assert!(allow_list.allow_effect(invalid_effect).is_err());
    }

    #[test]
    fn test_effect_usage_tracking() {
        let mut allow_list = EffectsAllowList::new();

        let effect = EffectSignature::new(EffectType::FileRead, "/tmp".to_string());
        let effect_id = effect.effect_id.clone();

        allow_list.allow_effect(effect).unwrap();
        allow_list.record_usage(&effect_id, "/tmp/test.txt", true, 100);

        let stats = allow_list.get_effect_stats(&effect_id).unwrap();
        assert_eq!(stats.total_operations, 1);
        assert_eq!(stats.successful_operations, 1);
    }
}
