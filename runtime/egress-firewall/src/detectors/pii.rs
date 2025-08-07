use regex::Regex;
use serde::{Deserialize, Serialize};

/// PII detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PIIDetection {
    pub category: String,
    pub confidence: f64,
    pub start: usize,
    pub end: usize,
    pub text: String,
}

/// PII detector for emails, phones, SSNs, etc.
pub struct PIIDetector {
    email_regex: Regex,
    phone_regex: Regex,
    ssn_regex: Regex,
    credit_card_regex: Regex,
    ip_address_regex: Regex,
    mac_address_regex: Regex,
    passport_regex: Regex,
    driver_license_regex: Regex,
    address_regex: Regex,
}

impl PIIDetector {
    pub fn new() -> Self {
        Self {
            email_regex: Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b")
                .unwrap(),
            phone_regex: Regex::new(r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b").unwrap(),
            ssn_regex: Regex::new(r"\b\d{3}-\d{2}-\d{4}\b").unwrap(),
            credit_card_regex: Regex::new(r"\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b").unwrap(),
            ip_address_regex: Regex::new(r"\b(?:[0-9]{1,3}\.){3}[0-9]{1,3}\b").unwrap(),
            mac_address_regex: Regex::new(r"\b([0-9A-Fa-f]{2}[:-]){5}([0-9A-Fa-f]{2})\b").unwrap(),
            passport_regex: Regex::new(r"\b[A-Z]{1,2}[0-9]{6,9}\b").unwrap(),
            driver_license_regex: Regex::new(r"\b[A-Z]{1,2}[0-9]{6,8}\b").unwrap(),
            address_regex: Regex::new(r"\b\d+\s+[A-Za-z\s]+(?:Street|St|Avenue|Ave|Road|Rd|Boulevard|Blvd|Lane|Ln|Drive|Dr|Court|Ct|Place|Pl|Way|Terrace|Ter)\b").unwrap(),
        }
    }

    /// Detect PII in text
    pub fn detect(&self, text: &str) -> Vec<PIIDetection> {
        let mut detections = Vec::new();

        // Email detection
        for mat in self.email_regex.find_iter(text) {
            detections.push(PIIDetection {
                category: "email".to_string(),
                confidence: 0.95,
                start: mat.start(),
                end: mat.end(),
                text: mat.as_str().to_string(),
            });
        }

        // Phone number detection
        for mat in self.phone_regex.find_iter(text) {
            detections.push(PIIDetection {
                category: "phone".to_string(),
                confidence: 0.90,
                start: mat.start(),
                end: mat.end(),
                text: mat.as_str().to_string(),
            });
        }

        // SSN detection
        for mat in self.ssn_regex.find_iter(text) {
            detections.push(PIIDetection {
                category: "ssn".to_string(),
                confidence: 0.98,
                start: mat.start(),
                end: mat.end(),
                text: mat.as_str().to_string(),
            });
        }

        // Credit card detection
        for mat in self.credit_card_regex.find_iter(text) {
            let card_text = mat.as_str().replace(&['-', ' '][..], "");
            if self.is_valid_credit_card(&card_text) {
                detections.push(PIIDetection {
                    category: "credit_card".to_string(),
                    confidence: 0.92,
                    start: mat.start(),
                    end: mat.end(),
                    text: mat.as_str().to_string(),
                });
            }
        }

        // IP address detection
        for mat in self.ip_address_regex.find_iter(text) {
            if self.is_valid_ip_address(mat.as_str()) {
                detections.push(PIIDetection {
                    category: "ip_address".to_string(),
                    confidence: 0.85,
                    start: mat.start(),
                    end: mat.end(),
                    text: mat.as_str().to_string(),
                });
            }
        }

        // MAC address detection
        for mat in self.mac_address_regex.find_iter(text) {
            detections.push(PIIDetection {
                category: "mac_address".to_string(),
                confidence: 0.95,
                start: mat.start(),
                end: mat.end(),
                text: mat.as_str().to_string(),
            });
        }

        // Passport detection
        for mat in self.passport_regex.find_iter(text) {
            detections.push(PIIDetection {
                category: "passport".to_string(),
                confidence: 0.80,
                start: mat.start(),
                end: mat.end(),
                text: mat.as_str().to_string(),
            });
        }

        // Driver license detection
        for mat in self.driver_license_regex.find_iter(text) {
            detections.push(PIIDetection {
                category: "driver_license".to_string(),
                confidence: 0.80,
                start: mat.start(),
                end: mat.end(),
                text: mat.as_str().to_string(),
            });
        }

        // Address detection
        for mat in self.address_regex.find_iter(text) {
            detections.push(PIIDetection {
                category: "address".to_string(),
                confidence: 0.75,
                start: mat.start(),
                end: mat.end(),
                text: mat.as_str().to_string(),
            });
        }

        detections
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
        let detector = PIIDetector::new();
        let text = "Contact me at john.doe@example.com for more info";
        let detections = detector.detect(text);

        assert_eq!(detections.len(), 1);
        assert_eq!(detections[0].category, "email");
        assert_eq!(detections[0].text, "john.doe@example.com");
    }

    #[test]
    fn test_phone_detection() {
        let detector = PIIDetector::new();
        let text = "Call me at 555-123-4567 or 555.987.6543";
        let detections = detector.detect(text);

        assert_eq!(detections.len(), 2);
        assert!(detections.iter().all(|d| d.category == "phone"));
    }

    #[test]
    fn test_ssn_detection() {
        let detector = PIIDetector::new();
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
}
