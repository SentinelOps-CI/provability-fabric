use regex::Regex;
use serde::{Deserialize, Serialize};
use hyperscan::{BlockDatabase, Pattern, PatternFlags};
use aho_corasick::AhoCorasick;
use lazy_static::lazy_static;
use std::sync::Arc;

/// PII detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PIIDetection {
    pub category: String,
    pub confidence: f64,
    pub start: usize,
    pub end: usize,
    pub text: String,
}

/// PII detector configuration
#[derive(Debug, Clone)]
pub struct PiiDetectorConfig {
    /// Enable Hyperscan for regex matching
    pub enable_hyperscan: bool,
    
    /// Enable Aho-Corasick for exact token matching
    pub enable_aho_corasick: bool,
    
    /// Fallback to regex if Hyperscan fails
    pub enable_fallback: bool,
    
    /// Minimum confidence threshold for PII detection
    pub min_confidence: f64,
    
    /// Maximum number of patterns to compile
    pub max_patterns: usize,
}

impl Default for PiiDetectorConfig {
    fn default() -> Self {
        Self {
            enable_hyperscan: true,
            enable_aho_corasick: true,
            enable_fallback: true,
            min_confidence: 0.8,
            max_patterns: 1000,
        }
    }
}

/// PII detector for emails, phones, SSNs, etc.
pub struct PIIDetector {
    // Hyperscan database for complex regex patterns
    hyperscan_db: Arc<BlockDatabase>,
    
    // Aho-Corasick for exact token matches
    exact_tokens: Arc<AhoCorasick>,
    
    // Fallback regex patterns (used when Hyperscan is not available)
    fallback_patterns: Vec<Regex>,
    
    // Configuration
    config: PiiDetectorConfig,
}

// PII patterns for Hyperscan compilation
lazy_static! {
    static ref PII_PATTERNS: Vec<(String, String, f64)> = vec![
        // Email patterns
        (r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b".to_string(), "email".to_string(), 0.95),
        
        // Phone number patterns
        (r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b".to_string(), "phone".to_string(), 0.90),
        (r"\b\+\d{1,3}[-.\s]?\d{1,4}[-.\s]?\d{1,4}[-.\s]?\d{1,4}\b".to_string(), "phone".to_string(), 0.85),
        
        // SSN patterns
        (r"\b\d{3}-\d{2}-\d{4}\b".to_string(), "ssn".to_string(), 0.98),
        (r"\b\d{9}\b".to_string(), "ssn".to_string(), 0.95),
        
        // Credit card patterns
        (r"\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b".to_string(), "credit_card".to_string(), 0.92),
        (r"\b\d{4}[-\s]?\d{6}[-\s]?\d{5}\b".to_string(), "credit_card".to_string(), 0.90), // Amex format
        
        // IP address patterns
        (r"\b(?:[0-9]{1,3}\.){3}[0-9]{1,3}\b".to_string(), "ip_address".to_string(), 0.85),
        (r"\b(?:[0-9a-fA-F]{1,4}:){7}[0-9a-fA-F]{1,4}\b".to_string(), "ip_address".to_string(), 0.85), // IPv6
        
        // MAC address patterns
        (r"\b([0-9A-Fa-f]{2}[:-]){5}([0-9A-Fa-f]{2})\b".to_string(), "mac_address".to_string(), 0.95),
        
        // Passport patterns
        (r"\b[A-Z]{1,2}[0-9]{6,9}\b".to_string(), "passport".to_string(), 0.90),
        
        // Driver license patterns
        (r"\b[A-Z]{1,2}[0-9]{6,8}\b".to_string(), "driver_license".to_string(), 0.88),
        
        // Address patterns
        (r"\b\d+\s+[A-Za-z\s]+(?:Street|St|Avenue|Ave|Road|Rd|Boulevard|Blvd|Lane|Ln|Drive|Dr|Court|Ct|Place|Pl|Way|Terrace|Ter)\b".to_string(), "address".to_string(), 0.80),
        
        // Date patterns
        (r"\b\d{1,2}[/-]\d{1,2}[/-]\d{2,4}\b".to_string(), "date".to_string(), 0.75),
        (r"\b\d{4}-\d{2}-\d{2}\b".to_string(), "date".to_string(), 0.85),
        
        // Social media handles
        (r"\b@[A-Za-z0-9_]{1,15}\b".to_string(), "social_media".to_string(), 0.95),
        
        // URLs
        (r"\bhttps?://[^\s<>\"{}|\\^`\[\]]+\b".to_string(), "url".to_string(), 0.90),
    ];
    
    // Exact tokens for Aho-Corasick matching
    static ref EXACT_TOKENS: Vec<&'static str> = vec![
        "password", "secret", "key", "token", "api_key", "private_key", "secret_key",
        "admin", "root", "superuser", "administrator", "master", "god",
        "test", "demo", "example", "sample", "dummy", "fake",
        "john.doe", "jane.smith", "user123", "admin123", "password123",
    ];
}

impl PIIDetector {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        Self::with_config(PiiDetectorConfig::default())
    }
    
    pub fn with_config(config: PiiDetectorConfig) -> Result<Self, Box<dyn std::error::Error>> {
        let mut detector = Self {
            hyperscan_db: Arc::new(BlockDatabase::new()?),
            exact_tokens: Arc::new(AhoCorasick::new(EXACT_TOKENS.iter())),
            fallback_patterns: Vec::new(),
            config,
        };
        
        // Initialize Hyperscan database if enabled
        if config.enable_hyperscan {
            detector.init_hyperscan()?;
        }
        
        // Initialize fallback patterns if enabled
        if config.enable_fallback {
            detector.init_fallback_patterns()?;
        }
        
        Ok(detector)
    }

    /// Initialize Hyperscan database with PII patterns
    fn init_hyperscan(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut patterns = Vec::new();
        
        for (pattern_str, category, confidence) in PII_PATTERNS.iter().take(self.config.max_patterns) {
            let pattern = Pattern::new(
                pattern_str,
                PatternFlags::empty(),
                Some(category.clone()),
            )?;
            patterns.push(pattern);
        }
        
        // Compile patterns into Hyperscan database
        let db = BlockDatabase::new(&patterns)?;
        self.hyperscan_db = Arc::new(db);
        
        Ok(())
    }
    
    /// Initialize fallback regex patterns
    fn init_fallback_patterns(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        for (pattern_str, _, _) in PII_PATTERNS.iter().take(self.config.max_patterns) {
            let regex = Regex::new(pattern_str)?;
            self.fallback_patterns.push(regex);
        }
        Ok(())
    }
    
    /// Detect PII in text using Hyperscan and Aho-Corasick
    pub fn detect(&self, text: &str) -> Vec<PIIDetection> {
        let mut detections = Vec::new();
        
        // Use Hyperscan for regex patterns if enabled
        if self.config.enable_hyperscan {
            if let Ok(matches) = self.hyperscan_db.find(text) {
                for mat in matches {
                    if let Some(category) = mat.pattern_info() {
                        let confidence = self.get_confidence_for_category(category);
                        if confidence >= self.config.min_confidence {
                            detections.push(PIIDetection {
                                category: category.to_string(),
                                confidence,
                                start: mat.start(),
                                end: mat.end(),
                                text: text[mat.start()..mat.end()].to_string(),
                            });
                        }
                    }
                }
            }
        }
        
        // Use Aho-Corasick for exact token matches if enabled
        if self.config.enable_aho_corasick {
            for mat in self.exact_tokens.find_iter(text) {
                let token = &text[mat.start()..mat.end()];
                let category = self.categorize_exact_token(token);
                let confidence = 0.95; // High confidence for exact matches
                
                if confidence >= self.config.min_confidence {
                    detections.push(PIIDetection {
                        category,
                        confidence,
                        start: mat.start(),
                        end: mat.end(),
                        text: token.to_string(),
                    });
                }
            }
        }
        
        // Fallback to regex if Hyperscan failed or is disabled
        if self.config.enable_fallback && (detections.is_empty() || !self.config.enable_hyperscan) {
            for (i, regex) in self.fallback_patterns.iter().enumerate() {
                for mat in regex.find_iter(text) {
                    let category = self.get_category_for_pattern_index(i);
                    let confidence = self.get_confidence_for_category(&category);
                    
                    if confidence >= self.config.min_confidence {
                        detections.push(PIIDetection {
                            category,
                            confidence,
                            start: mat.start(),
                            end: mat.end(),
                            text: mat.as_str().to_string(),
                        });
                    }
                }
            }
        }
        
        // Remove duplicates and sort by confidence
        detections.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
        detections.dedup_by(|a, b| a.start == b.start && a.end == b.end);
        
        detections
    }
    
    /// Get confidence score for a category
    fn get_confidence_for_category(&self, category: &str) -> f64 {
        for (_, cat, conf) in PII_PATTERNS.iter() {
            if cat == category {
                return *conf;
            }
        }
        0.8 // Default confidence
    }
    
    /// Get category for pattern index
    fn get_category_for_pattern_index(&self, index: usize) -> String {
        if index < PII_PATTERNS.len() {
            PII_PATTERNS[index].1.clone()
        } else {
            "unknown".to_string()
        }
    }
    
    /// Categorize exact token matches
    fn categorize_exact_token(&self, token: &str) -> String {
        match token {
            "password" | "secret" | "key" | "token" | "api_key" | "private_key" | "secret_key" => "credential".to_string(),
            "admin" | "root" | "superuser" | "administrator" | "master" | "god" => "privileged_account".to_string(),
            "test" | "demo" | "example" | "sample" | "dummy" | "fake" => "test_data".to_string(),
            _ => "sensitive_token".to_string(),
        }
    }
    
    /// Get detector statistics
    pub fn get_stats(&self) -> PiiDetectorStats {
        PiiDetectorStats {
            total_patterns: PII_PATTERNS.len(),
            hyperscan_enabled: self.config.enable_hyperscan,
            aho_corasick_enabled: self.config.enable_aho_corasick,
            fallback_enabled: self.config.enable_fallback,
            max_patterns: self.config.max_patterns,
            min_confidence: self.config.min_confidence,
        }
    }
    
    /// Benchmark detection performance
    pub fn benchmark(&self, text: &str, iterations: usize) -> PiiBenchmarkResult {
        let start = std::time::Instant::now();
        
        for _ in 0..iterations {
            self.detect(text);
        }
        
        let duration = start.elapsed();
        let avg_time = duration.as_micros() as f64 / iterations as f64;
        
        PiiBenchmarkResult {
            iterations,
            total_time_micros: duration.as_micros(),
            avg_time_micros: avg_time,
            throughput_mb_per_sec: (text.len() as f64 * iterations as f64) / (avg_time / 1_000_000.0) / 1_048_576.0,
        }
    }

    /// Luhn algorithm validation for credit cards
    fn is_valid_credit_card(&self, number: &str) -> bool {
        if number.len() < 13 || number.len() > 19 {
            return false;
        }

        let digits: Vec<u32> = number.chars().filter_map(|c| c.to_digit(10)).collect();

        if digits.len() != number.len() {
            return false;
        }

        let mut sum = 0;
        let mut double = false;

        for &digit in digits.iter().rev() {
            let mut d = digit;
            if double {
                d *= 2;
                if d > 9 {
                    d = (d / 10) + (d % 10);
                }
            }
            sum += d;
            double = !double;
        }

        sum % 10 == 0
    }

    /// Validate IP address format
    fn is_valid_ip_address(&self, ip: &str) -> bool {
        let parts: Vec<&str> = ip.split('.').collect();
        if parts.len() != 4 {
            return false;
        }

        for part in parts {
            match part.parse::<u8>() {
                Ok(_) => continue,
                Err(_) => return false,
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_email_detection() {
        let detector = PIIDetector::new().unwrap();
        let text = "Contact me at john.doe@example.com for more info";
        let detections = detector.detect(text);

        assert_eq!(detections.len(), 1);
        assert_eq!(detections[0].category, "email");
        assert_eq!(detections[0].text, "john.doe@example.com");
    }

    #[test]
    fn test_phone_detection() {
        let detector = PIIDetector::new().unwrap();
        let text = "Call me at 555-123-4567 or 555.987.6543";
        let detections = detector.detect(text);

        assert_eq!(detections.len(), 2);
        assert!(detections.iter().all(|d| d.category == "phone"));
    }

    #[test]
    fn test_ssn_detection() {
        let detector = PIIDetector::new().unwrap();
        let text = "My SSN is 123-45-6789";
        let detections = detector.detect(text);

        assert_eq!(detections.len(), 1);
        assert_eq!(detections[0].category, "ssn");
        assert_eq!(detections[0].text, "123-45-6789");
    }

    #[test]
    fn test_credit_card_validation() {
        let detector = PIIDetector::new();

        // Valid test credit card number
        assert!(detector.is_valid_credit_card("4111111111111111"));

        // Invalid number
        assert!(!detector.is_valid_credit_card("1234567890123456"));
    }
    
    #[test]
    fn test_hyperscan_integration() {
        let config = PiiDetectorConfig {
            enable_hyperscan: true,
            enable_aho_corasick: true,
            enable_fallback: false,
            min_confidence: 0.8,
            max_patterns: 100,
        };
        
        let detector = PIIDetector::with_config(config).unwrap();
        let stats = detector.get_stats();
        
        assert!(stats.hyperscan_enabled);
        assert!(stats.aho_corasick_enabled);
        assert!(!stats.fallback_enabled);
        assert_eq!(stats.max_patterns, 100);
        assert_eq!(stats.min_confidence, 0.8);
    }
    
    #[test]
    fn test_benchmark() {
        let detector = PIIDetector::new().unwrap();
        let text = "This is a test text with email@example.com and phone 555-123-4567";
        let result = detector.benchmark(text, 100);
        
        assert_eq!(result.iterations, 100);
        assert!(result.total_time_micros > 0);
        assert!(result.avg_time_micros > 0.0);
        assert!(result.throughput_mb_per_sec > 0.0);
    }
}

/// PII detector statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PiiDetectorStats {
    pub total_patterns: usize,
    pub hyperscan_enabled: bool,
    pub aho_corasick_enabled: bool,
    pub fallback_enabled: bool,
    pub max_patterns: usize,
    pub min_confidence: f64,
}

/// PII detector benchmark results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PiiBenchmarkResult {
    pub iterations: usize,
    pub total_time_micros: u128,
    pub avg_time_micros: f64,
    pub throughput_mb_per_sec: f64,
}
