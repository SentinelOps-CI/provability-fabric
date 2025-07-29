// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::{error, warn};

/// Assumption with expected value
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Assumption {
    pub key: String,
    pub expected: String,
}

/// Assumption drift monitor
pub struct AssumptionMonitor {
    assumptions: HashMap<String, String>,
    violation_count: u64,
}

impl AssumptionMonitor {
    /// Create new assumption monitor
    pub fn new() -> Self {
        Self {
            assumptions: HashMap::new(),
            violation_count: 0,
        }
    }

    /// Process assumption message
    pub fn process_assumption(&mut self, assumption: Assumption) -> Result<bool> {
        let key = assumption.key.clone();
        let expected = assumption.expected.clone();

        // Check if this is a new assumption or if value has changed
        if let Some(current_value) = self.assumptions.get(&key) {
            if current_value != &expected {
                // Assumption drift detected
                self.violation_count += 1;
                error!(
                    "Assumption drift detected for key '{}': expected '{}', got '{}'",
                    key, expected, current_value
                );
                return Ok(false);
            }
        } else {
            // New assumption, record it
            self.assumptions.insert(key.clone(), expected.clone());
        }

        Ok(true)
    }

    /// Get violation count for metrics
    pub fn violation_count(&self) -> u64 {
        self.violation_count
    }

    /// Get current assumptions
    pub fn assumptions(&self) -> &HashMap<String, String> {
        &self.assumptions
    }
}

impl Default for AssumptionMonitor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_assumption() {
        let mut monitor = AssumptionMonitor::new();
        let assumption = Assumption {
            key: "test_key".to_string(),
            expected: "test_value".to_string(),
        };

        assert!(monitor.process_assumption(assumption).unwrap());
        assert_eq!(monitor.violation_count(), 0);
        assert_eq!(monitor.assumptions().len(), 1);
    }

    #[test]
    fn test_assumption_drift() {
        let mut monitor = AssumptionMonitor::new();
        
        // Add initial assumption
        let assumption1 = Assumption {
            key: "test_key".to_string(),
            expected: "test_value".to_string(),
        };
        assert!(monitor.process_assumption(assumption1).unwrap());
        
        // Add conflicting assumption
        let assumption2 = Assumption {
            key: "test_key".to_string(),
            expected: "different_value".to_string(),
        };
        assert!(!monitor.process_assumption(assumption2).unwrap());
        assert_eq!(monitor.violation_count(), 1);
    }

    #[test]
    fn test_same_assumption_no_drift() {
        let mut monitor = AssumptionMonitor::new();
        
        let assumption = Assumption {
            key: "test_key".to_string(),
            expected: "test_value".to_string(),
        };
        
        // Add same assumption twice
        assert!(monitor.process_assumption(assumption.clone()).unwrap());
        assert!(monitor.process_assumption(assumption).unwrap());
        
        assert_eq!(monitor.violation_count(), 0);
    }
}