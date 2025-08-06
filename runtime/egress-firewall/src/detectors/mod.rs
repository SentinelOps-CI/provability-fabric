pub mod pii;
pub mod secrets;
pub mod near_dupe;

use pii::{PIIDetector, PIIDetection};
use secrets::{SecretDetector, SecretDetection};
use near_dupe::{NearDupeDetector, NearDupeDetection};

use anyhow::Result;
use serde::{Deserialize, Serialize};

/// Unified detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectionResult {
    pub detector_name: String,
    pub confidence: f64,
    pub redactions: Vec<Redaction>,
}

/// Redaction information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Redaction {
    pub start: usize,
    pub end: usize,
    pub text: String,
    pub category: String,
}

/// Suite of all detectors
pub struct DetectorSuite {
    pii_detector: PIIDetector,
    secret_detector: SecretDetector,
    near_dupe_detector: NearDupeDetector,
}

impl DetectorSuite {
    /// Create new detector suite
    pub async fn new() -> Result<Self> {
        let mut near_dupe_detector = NearDupeDetector::new();
        
        // Add some known training data patterns
        near_dupe_detector.add_known_content(
            "Please provide your personal information including name, address, and phone number",
            "training_template_1".to_string(),
        );
        
        Ok(Self {
            pii_detector: PIIDetector::new(),
            secret_detector: SecretDetector::new(),
            near_dupe_detector,
        })
    }

    /// Scan text with all detectors
    pub async fn scan_text(&self, text: &str) -> Result<Vec<DetectionResult>> {
        let mut results = Vec::new();

        // PII detection
        let pii_detections = self.pii_detector.detect(text);
        if !pii_detections.is_empty() {
            let redactions = pii_detections
                .into_iter()
                .map(|d| Redaction {
                    start: d.start,
                    end: d.end,
                    text: d.text,
                    category: d.category,
                })
                .collect();

            let avg_confidence = redactions.len() as f64 * 0.9; // Simplified confidence
            results.push(DetectionResult {
                detector_name: "pii_detector".to_string(),
                confidence: avg_confidence.min(1.0),
                redactions,
            });
        }

        // Secret detection
        let secret_detections = self.secret_detector.detect(text);
        if !secret_detections.is_empty() {
            let redactions = secret_detections
                .into_iter()
                .map(|d| Redaction {
                    start: d.start,
                    end: d.end,
                    text: d.text,
                    category: d.category,
                })
                .collect();

            let avg_confidence = redactions.iter().map(|_| 0.95).sum::<f64>() / redactions.len() as f64;
            results.push(DetectionResult {
                detector_name: "secret_detector".to_string(),
                confidence: avg_confidence,
                redactions,
            });
        }

        // Near-duplicate detection
        if let Some(near_dupe) = self.near_dupe_detector.detect(text) {
            results.push(DetectionResult {
                detector_name: "near_dupe_detector".to_string(),
                confidence: near_dupe.similarity_score,
                redactions: vec![], // Near-dupe doesn't redact, just flags
            });
        }

        Ok(results)
    }

    /// Get number of loaded detectors
    pub async fn detector_count(&self) -> usize {
        3 // PII, Secret, Near-dupe
    }

    /// Check if text should be blocked entirely
    pub fn should_block(&self, detections: &[DetectionResult]) -> bool {
        for detection in detections {
            match detection.detector_name.as_str() {
                "secret_detector" => {
                    // Block if any high-confidence secrets detected
                    if detection.confidence > 0.9 && !detection.redactions.is_empty() {
                        return true;
                    }
                }
                "near_dupe_detector" => {
                    // Block if high similarity to known training data
                    if detection.confidence > 0.85 {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// Calculate overall risk score
    pub fn calculate_risk_score(&self, detections: &[DetectionResult]) -> f64 {
        let mut total_risk = 0.0;
        
        for detection in detections {
            let weight = match detection.detector_name.as_str() {
                "secret_detector" => 1.0,
                "pii_detector" => 0.8,
                "near_dupe_detector" => 0.6,
                _ => 0.5,
            };
            
            total_risk += detection.confidence * weight;
        }

        total_risk.min(1.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_detector_suite_creation() {
        let suite = DetectorSuite::new().await.unwrap();
        let count = suite.detector_count().await;
        assert_eq!(count, 3);
    }

    #[tokio::test]
    async fn test_combined_detection() {
        let suite = DetectorSuite::new().await.unwrap();
        let text = "My email is john@example.com and my API key is AKIAIOSFODNN7EXAMPLE";
        
        let results = suite.scan_text(text).await.unwrap();
        
        // Should detect both PII and secrets
        assert!(results.len() >= 1);
        
        let has_pii = results.iter().any(|r| r.detector_name == "pii_detector");
        let has_secret = results.iter().any(|r| r.detector_name == "secret_detector");
        
        assert!(has_pii || has_secret);
    }

    #[test]
    fn test_risk_calculation() {
        let suite = DetectorSuite {
            pii_detector: PIIDetector::new(),
            secret_detector: SecretDetector::new(),
            near_dupe_detector: NearDupeDetector::new(),
        };

        let detections = vec![
            DetectionResult {
                detector_name: "secret_detector".to_string(),
                confidence: 0.9,
                redactions: vec![],
            },
            DetectionResult {
                detector_name: "pii_detector".to_string(),
                confidence: 0.7,
                redactions: vec![],
            },
        ];

        let risk = suite.calculate_risk_score(&detections);
        assert!(risk > 0.5);
        assert!(risk <= 1.0);
    }

    #[test]
    fn test_blocking_logic() {
        let suite = DetectorSuite {
            pii_detector: PIIDetector::new(),
            secret_detector: SecretDetector::new(),
            near_dupe_detector: NearDupeDetector::new(),
        };

        // High-confidence secret should block
        let high_secret = vec![DetectionResult {
            detector_name: "secret_detector".to_string(),
            confidence: 0.95,
            redactions: vec![Redaction {
                start: 0,
                end: 10,
                text: "secret".to_string(),
                category: "api_key".to_string(),
            }],
        }];
        assert!(suite.should_block(&high_secret));

        // Low-confidence PII should not block
        let low_pii = vec![DetectionResult {
            detector_name: "pii_detector".to_string(),
            confidence: 0.3,
            redactions: vec![],
        }];
        assert!(!suite.should_block(&low_pii));
    }
}