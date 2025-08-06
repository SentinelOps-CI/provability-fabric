use regex::Regex;
use serde::{Deserialize, Serialize};

/// Secret detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecretDetection {
    pub category: String,
    pub confidence: f64,
    pub start: usize,
    pub end: usize,
    pub text: String,
    pub entropy: f64,
}

/// Secret detector for API keys, passwords, tokens, etc.
pub struct SecretDetector {
    api_key_patterns: Vec<(String, Regex)>,
    high_entropy_regex: Regex,
}

impl SecretDetector {
    pub fn new() -> Self {
        let mut api_key_patterns = Vec::new();

        // Common API key patterns
        api_key_patterns.push((
            "aws_access_key".to_string(),
            Regex::new(r"AKIA[0-9A-Z]{16}").unwrap(),
        ));
        api_key_patterns.push((
            "aws_secret_key".to_string(),
            Regex::new(r"[A-Za-z0-9/+=]{40}").unwrap(),
        ));
        api_key_patterns.push((
            "github_token".to_string(),
            Regex::new(r"ghp_[A-Za-z0-9]{36}").unwrap(),
        ));
        api_key_patterns.push((
            "slack_token".to_string(),
            Regex::new(r"xox[baprs]-[A-Za-z0-9-]+").unwrap(),
        ));
        api_key_patterns.push((
            "jwt_token".to_string(),
            Regex::new(r"eyJ[A-Za-z0-9-_=]+\.[A-Za-z0-9-_=]+\.[A-Za-z0-9-_.+/=]*").unwrap(),
        ));

        Self {
            api_key_patterns,
            high_entropy_regex: Regex::new(r"[A-Za-z0-9+/=]{20,}").unwrap(),
        }
    }

    /// Detect secrets in text
    pub fn detect(&self, text: &str) -> Vec<SecretDetection> {
        let mut detections = Vec::new();

        // Check for known API key patterns
        for (category, regex) in &self.api_key_patterns {
            for mat in regex.find_iter(text) {
                let secret_text = mat.as_str();
                let entropy = self.calculate_entropy(secret_text);

                detections.push(SecretDetection {
                    category: category.clone(),
                    confidence: 0.95,
                    start: mat.start(),
                    end: mat.end(),
                    text: secret_text.to_string(),
                    entropy,
                });
            }
        }

        // Check for high-entropy strings that might be secrets
        for mat in self.high_entropy_regex.find_iter(text) {
            let candidate = mat.as_str();
            let entropy = self.calculate_entropy(candidate);

            // Only flag if entropy is high enough and not already detected
            if entropy > 4.0 && !self.already_detected(&detections, mat.start()) {
                detections.push(SecretDetection {
                    category: "high_entropy".to_string(),
                    confidence: entropy / 8.0, // Normalize entropy to confidence
                    start: mat.start(),
                    end: mat.end(),
                    text: candidate.to_string(),
                    entropy,
                });
            }
        }

        detections
    }

    /// Calculate Shannon entropy of a string
    fn calculate_entropy(&self, text: &str) -> f64 {
        if text.is_empty() {
            return 0.0;
        }

        let mut char_counts = std::collections::HashMap::new();
        let text_len = text.len() as f64;

        // Count character frequencies
        for ch in text.chars() {
            *char_counts.entry(ch).or_insert(0) += 1;
        }

        // Calculate entropy
        let mut entropy = 0.0;
        for &count in char_counts.values() {
            let probability = count as f64 / text_len;
            entropy -= probability * probability.log2();
        }

        entropy
    }

    /// Check if position is already detected
    fn already_detected(&self, detections: &[SecretDetection], position: usize) -> bool {
        detections
            .iter()
            .any(|d| position >= d.start && position < d.end)
    }

    /// Validate if a string looks like a real secret
    pub fn validate_secret(&self, text: &str) -> bool {
        // Check minimum length
        if text.len() < 16 {
            return false;
        }

        // Check entropy
        let entropy = self.calculate_entropy(text);
        if entropy < 3.5 {
            return false;
        }

        // Check for mix of character types
        let has_upper = text.chars().any(|c| c.is_ascii_uppercase());
        let has_lower = text.chars().any(|c| c.is_ascii_lowercase());
        let has_digit = text.chars().any(|c| c.is_ascii_digit());
        let has_special = text.chars().any(|c| !c.is_alphanumeric());

        // Require at least 2 character types
        let char_types = [has_upper, has_lower, has_digit, has_special]
            .iter()
            .filter(|&&x| x)
            .count();

        char_types >= 2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aws_key_detection() {
        let detector = SecretDetector::new();
        let text = "AWS_ACCESS_KEY_ID=AKIAIOSFODNN7EXAMPLE";
        let detections = detector.detect(text);

        assert!(!detections.is_empty());
        let aws_detection = detections.iter().find(|d| d.category == "aws_access_key");
        assert!(aws_detection.is_some());
    }

    #[test]
    fn test_github_token_detection() {
        let detector = SecretDetector::new();
        let text = "export GITHUB_TOKEN=ghp_1234567890abcdef1234567890abcdef12345678";
        let detections = detector.detect(text);

        assert!(!detections.is_empty());
        let github_detection = detections.iter().find(|d| d.category == "github_token");
        assert!(github_detection.is_some());
    }

    #[test]
    fn test_entropy_calculation() {
        let detector = SecretDetector::new();

        // Low entropy (repeated characters)
        let low_entropy = detector.calculate_entropy("aaaaaaaaaa");
        assert!(low_entropy < 1.0);

        // High entropy (random-looking string)
        let high_entropy = detector.calculate_entropy("Kj8$mN2!pQ9#xY7@");
        assert!(high_entropy > 3.0);
    }

    #[test]
    fn test_secret_validation() {
        let detector = SecretDetector::new();

        // Valid secret-like string
        assert!(detector.validate_secret("MySecr3tP@ssw0rd123"));

        // Invalid (too short)
        assert!(!detector.validate_secret("short"));

        // Invalid (low entropy)
        assert!(!detector.validate_secret("aaaaaaaaaaaaaaaa"));

        // Invalid (single character type)
        assert!(!detector.validate_secret("onlylowercaseletters"));
    }

    #[test]
    fn test_jwt_detection() {
        let detector = SecretDetector::new();
        let jwt = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c";
        let detections = detector.detect(jwt);

        assert!(!detections.is_empty());
        let jwt_detection = detections.iter().find(|d| d.category == "jwt_token");
        assert!(jwt_detection.is_some());
    }
}
