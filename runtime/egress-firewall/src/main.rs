use actix_web::{web, App, HttpServer, HttpResponse, HttpRequest, Error};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
use uuid::Uuid;
use sha2::{Sha256, Digest};
use regex::Regex;
use std::collections::HashSet;

/// Egress request with text to be checked
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressRequest {
    pub text: String,
    pub tenant: String,
    pub subject_id: String,
    pub plan_id: Option<String>,
    pub context: HashMap<String, String>,
}

/// Egress response with certificate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressResponse {
    pub text: String,
    pub certificate: EgressCertificate,
    pub warnings: Vec<String>,
}

/// Egress certificate for audit trail
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertificate {
    pub cert_id: String,
    pub plan_id: Option<String>,
    pub tenant: String,
    pub detectors: DetectorResults,
    pub policy_hash: String,
    pub text_hash: String,
    pub timestamp: u64,
    pub signer: Option<String>,
}

/// Detector results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectorResults {
    pub pii: PiiResult,
    pub secrets: SecretsResult,
    pub near_dupe: NearDupeResult,
    pub policy_violations: Vec<String>,
}

/// PII detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PiiResult {
    pub detected: bool,
    pub types: Vec<String>,
    pub confidence: f64,
    pub redacted: bool,
}

/// Secrets detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecretsResult {
    pub detected: bool,
    pub types: Vec<String>,
    pub confidence: f64,
    pub redacted: bool,
}

/// Near-duplicate detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NearDupeResult {
    pub score: f64,
    pub threshold: f64,
    pub is_duplicate: bool,
    pub similar_texts: Vec<String>,
}

/// Egress firewall service
pub struct EgressFirewall {
    /// PII detectors
    pii_detectors: Vec<Box<dyn PiiDetector>>,
    
    /// Secret detectors
    secret_detectors: Vec<Box<dyn SecretDetector>>,
    
    /// Near-duplicate detector
    near_dupe_detector: Box<dyn NearDupeDetector>,
    
    /// Policy templates
    policies: HashMap<String, PolicyTemplate>,
    
    /// Signing key
    signing_key: Option<Vec<u8>>,
    
    /// Ledger URL
    ledger_url: String,
}

/// PII detector trait
pub trait PiiDetector: Send + Sync {
    fn detect(&self, text: &str) -> PiiResult;
    fn name(&self) -> &str;
}

/// Secret detector trait
pub trait SecretDetector: Send + Sync {
    fn detect(&self, text: &str) -> SecretsResult;
    fn name(&self) -> &str;
}

/// Near-duplicate detector trait
pub trait NearDupeDetector: Send + Sync {
    fn detect(&self, text: &str, history: &[String]) -> NearDupeResult;
    fn name(&self) -> &str;
}

/// Policy template
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyTemplate {
    pub name: String,
    pub tenant: String,
    pub blacklist_phrases: Vec<String>,
    pub tenant_secrets: Vec<String>,
    pub pii_allowed: bool,
    pub secrets_allowed: bool,
    pub near_dupe_threshold: f64,
}

/// Email PII detector
pub struct EmailDetector;

impl PiiDetector for EmailDetector {
    fn detect(&self, text: &str) -> PiiResult {
        let email_regex = Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b").unwrap();
        let matches: Vec<_> = email_regex.find_iter(text).collect();
        
        PiiResult {
            detected: !matches.is_empty(),
            types: if !matches.is_empty() { vec!["email".to_string()] } else { vec![] },
            confidence: if !matches.is_empty() { 0.95 } else { 0.0 },
            redacted: false,
        }
    }
    
    fn name(&self) -> &str {
        "email_detector"
    }
}

/// Phone number PII detector
pub struct PhoneDetector;

impl PiiDetector for PhoneDetector {
    fn detect(&self, text: &str) -> PiiResult {
        let phone_regex = Regex::new(r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b").unwrap();
        let matches: Vec<_> = phone_regex.find_iter(text).collect();
        
        PiiResult {
            detected: !matches.is_empty(),
            types: if !matches.is_empty() { vec!["phone".to_string()] } else { vec![] },
            confidence: if !matches.is_empty() { 0.90 } else { 0.0 },
            redacted: false,
        }
    }
    
    fn name(&self) -> &str {
        "phone_detector"
    }
}

/// SSN PII detector
pub struct SsnDetector;

impl PiiDetector for SsnDetector {
    fn detect(&self, text: &str) -> PiiResult {
        let ssn_regex = Regex::new(r"\b\d{3}-\d{2}-\d{4}\b").unwrap();
        let matches: Vec<_> = ssn_regex.find_iter(text).collect();
        
        PiiResult {
            detected: !matches.is_empty(),
            types: if !matches.is_empty() { vec!["ssn".to_string()] } else { vec![] },
            confidence: if !matches.is_empty() { 0.99 } else { 0.0 },
            redacted: false,
        }
    }
    
    fn name(&self) -> &str {
        "ssn_detector"
    }
}

/// API key secret detector
pub struct ApiKeyDetector;

impl SecretDetector for ApiKeyDetector {
    fn detect(&self, text: &str) -> SecretsResult {
        let api_key_patterns = vec![
            r"sk-[a-zA-Z0-9]{32,}",
            r"pk_[a-zA-Z0-9]{32,}",
            r"api_key['\"]?\s*[:=]\s*['\"]?[a-zA-Z0-9]{32,}",
        ];
        
        let mut detected = false;
        let mut types = Vec::new();
        
        for pattern in api_key_patterns {
            let regex = Regex::new(pattern).unwrap();
            if regex.is_match(text) {
                detected = true;
                types.push("api_key".to_string());
            }
        }
        
        SecretsResult {
            detected,
            types,
            confidence: if detected { 0.95 } else { 0.0 },
            redacted: false,
        }
    }
    
    fn name(&self) -> &str {
        "api_key_detector"
    }
}

/// Password secret detector
pub struct PasswordDetector;

impl SecretDetector for PasswordDetector {
    fn detect(&self, text: &str) -> SecretsResult {
        let password_patterns = vec![
            r"password['\"]?\s*[:=]\s*['\"]?[^\s'\"]+",
            r"passwd['\"]?\s*[:=]\s*['\"]?[^\s'\"]+",
            r"pwd['\"]?\s*[:=]\s*['\"]?[^\s'\"]+",
        ];
        
        let mut detected = false;
        let mut types = Vec::new();
        
        for pattern in password_patterns {
            let regex = Regex::new(pattern).unwrap();
            if regex.is_match(text) {
                detected = true;
                types.push("password".to_string());
            }
        }
        
        SecretsResult {
            detected,
            types,
            confidence: if detected { 0.90 } else { 0.0 },
            redacted: false,
        }
    }
    
    fn name(&self) -> &str {
        "password_detector"
    }
}

/// MinHash near-duplicate detector
pub struct MinHashDetector {
    threshold: f64,
    history: Vec<String>,
}

impl MinHashDetector {
    pub fn new(threshold: f64) -> Self {
        Self {
            threshold,
            history: Vec::new(),
        }
    }
    
    fn calculate_similarity(&self, text1: &str, text2: &str) -> f64 {
        // Simplified similarity calculation using character n-grams
        let n = 3;
        let grams1 = self.get_ngrams(text1, n);
        let grams2 = self.get_ngrams(text2, n);
        
        let intersection = grams1.intersection(&grams2).count();
        let union = grams1.union(&grams2).count();
        
        if union == 0 {
            0.0
        } else {
            intersection as f64 / union as f64
        }
    }
    
    fn get_ngrams(&self, text: &str, n: usize) -> HashSet<String> {
        let mut grams = HashSet::new();
        let chars: Vec<char> = text.chars().collect();
        
        for i in 0..chars.len().saturating_sub(n - 1) {
            let gram: String = chars[i..i + n].iter().collect();
            grams.insert(gram);
        }
        
        grams
    }
}

impl NearDupeDetector for MinHashDetector {
    fn detect(&self, text: &str, history: &[String]) -> NearDupeResult {
        let mut max_similarity = 0.0;
        let mut similar_texts = Vec::new();
        
        for historical_text in history {
            let similarity = self.calculate_similarity(text, historical_text);
            if similarity > max_similarity {
                max_similarity = similarity;
            }
            if similarity > self.threshold {
                similar_texts.push(historical_text.clone());
            }
        }
        
        NearDupeResult {
            score: max_similarity,
            threshold: self.threshold,
            is_duplicate: max_similarity > self.threshold,
            similar_texts,
        }
    }
    
    fn name(&self) -> &str {
        "minhash_detector"
    }
}

impl EgressFirewall {
    pub fn new(ledger_url: String) -> Self {
        let mut firewall = Self {
            pii_detectors: Vec::new(),
            secret_detectors: Vec::new(),
            near_dupe_detector: Box::new(MinHashDetector::new(0.8)),
            policies: HashMap::new(),
            signing_key: None,
            ledger_url,
        };
        
        // Add default detectors
        firewall.pii_detectors.push(Box::new(EmailDetector));
        firewall.pii_detectors.push(Box::new(PhoneDetector));
        firewall.pii_detectors.push(Box::new(SsnDetector));
        
        firewall.secret_detectors.push(Box::new(ApiKeyDetector));
        firewall.secret_detectors.push(Box::new(PasswordDetector));
        
        firewall
    }

    /// Add policy template
    pub fn add_policy(&mut self, policy: PolicyTemplate) {
        self.policies.insert(policy.tenant.clone(), policy);
    }

    /// Set signing key
    pub fn set_signing_key(&mut self, key: Vec<u8>) {
        self.signing_key = Some(key);
    }

    /// Process egress request
    pub async fn process_egress(&self, request: EgressRequest) -> Result<EgressResponse, String> {
        let mut warnings = Vec::new();
        
        // Get policy for tenant
        let policy = self.policies.get(&request.tenant)
            .ok_or_else(|| format!("No policy found for tenant: {}", request.tenant))?;
        
        // Run PII detection
        let pii_result = self.detect_pii(&request.text);
        
        // Run secret detection
        let secrets_result = self.detect_secrets(&request.text);
        
        // Run near-duplicate detection
        let near_dupe_result = self.detect_near_duplicates(&request.text).await;
        
        // Check policy violations
        let policy_violations = self.check_policy_violations(&request.text, policy);
        
        // Apply redactions if needed
        let mut processed_text = request.text.clone();
        if pii_result.redacted || secrets_result.redacted {
            processed_text = self.apply_redactions(&request.text, &pii_result, &secrets_result);
        }
        
        // Generate warnings
        if pii_result.detected && !policy.pii_allowed {
            warnings.push("PII detected but not allowed by policy".to_string());
        }
        
        if secrets_result.detected && !policy.secrets_allowed {
            warnings.push("Secrets detected but not allowed by policy".to_string());
        }
        
        if near_dupe_result.is_duplicate {
            warnings.push("Near-duplicate content detected".to_string());
        }
        
        if !policy_violations.is_empty() {
            warnings.extend(policy_violations.iter().map(|v| format!("Policy violation: {}", v)));
        }
        
        // Generate certificate
        let certificate = self.generate_certificate(&request, &pii_result, &secrets_result, &near_dupe_result, &policy_violations).await?;
        
        // Store certificate in ledger
        self.store_certificate_in_ledger(&certificate).await?;
        
        Ok(EgressResponse {
            text: processed_text,
            certificate,
            warnings,
        })
    }

    /// Detect PII in text
    fn detect_pii(&self, text: &str) -> PiiResult {
        let mut all_types = Vec::new();
        let mut max_confidence = 0.0;
        let mut any_redacted = false;
        
        for detector in &self.pii_detectors {
            let result = detector.detect(text);
            if result.detected {
                all_types.extend(result.types);
                max_confidence = max_confidence.max(result.confidence);
                any_redacted = any_redacted || result.redacted;
            }
        }
        
        PiiResult {
            detected: !all_types.is_empty(),
            types: all_types,
            confidence: max_confidence,
            redacted: any_redacted,
        }
    }

    /// Detect secrets in text
    fn detect_secrets(&self, text: &str) -> SecretsResult {
        let mut all_types = Vec::new();
        let mut max_confidence = 0.0;
        let mut any_redacted = false;
        
        for detector in &self.secret_detectors {
            let result = detector.detect(text);
            if result.detected {
                all_types.extend(result.types);
                max_confidence = max_confidence.max(result.confidence);
                any_redacted = any_redacted || result.redacted;
            }
        }
        
        SecretsResult {
            detected: !all_types.is_empty(),
            types: all_types,
            confidence: max_confidence,
            redacted: any_redacted,
        }
    }

    /// Detect near-duplicates
    async fn detect_near_duplicates(&self, text: &str) -> NearDupeResult {
        // In real implementation, this would query a database of historical texts
        // For now, we'll use an empty history
        let history = Vec::new();
        self.near_dupe_detector.detect(text, &history)
    }

    /// Check policy violations
    fn check_policy_violations(&self, text: &str, policy: &PolicyTemplate) -> Vec<String> {
        let mut violations = Vec::new();
        
        // Check blacklist phrases
        for phrase in &policy.blacklist_phrases {
            if text.to_lowercase().contains(&phrase.to_lowercase()) {
                violations.push(format!("Blacklisted phrase: {}", phrase));
            }
        }
        
        // Check tenant secrets
        for secret in &policy.tenant_secrets {
            if text.contains(secret) {
                violations.push("Tenant secret detected".to_string());
            }
        }
        
        violations
    }

    /// Apply redactions to text
    fn apply_redactions(&self, text: &str, pii_result: &PiiResult, secrets_result: &SecretsResult) -> String {
        let mut redacted_text = text.to_string();
        
        if pii_result.redacted {
            // Redact email addresses
            let email_regex = Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b").unwrap();
            redacted_text = email_regex.replace_all(&redacted_text, "[EMAIL_REDACTED]").to_string();
            
            // Redact phone numbers
            let phone_regex = Regex::new(r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b").unwrap();
            redacted_text = phone_regex.replace_all(&redacted_text, "[PHONE_REDACTED]").to_string();
            
            // Redact SSNs
            let ssn_regex = Regex::new(r"\b\d{3}-\d{2}-\d{4}\b").unwrap();
            redacted_text = ssn_regex.replace_all(&redacted_text, "[SSN_REDACTED]").to_string();
        }
        
        if secrets_result.redacted {
            // Redact API keys
            let api_key_regex = Regex::new(r"sk-[a-zA-Z0-9]{32,}").unwrap();
            redacted_text = api_key_regex.replace_all(&redacted_text, "[API_KEY_REDACTED]").to_string();
            
            // Redact passwords
            let password_regex = Regex::new(r"password['\"]?\s*[:=]\s*['\"]?[^\s'\"]+").unwrap();
            redacted_text = password_regex.replace_all(&redacted_text, "password=[PASSWORD_REDACTED]").to_string();
        }
        
        redacted_text
    }

    /// Generate egress certificate
    async fn generate_certificate(
        &self,
        request: &EgressRequest,
        pii_result: &PiiResult,
        secrets_result: &SecretsResult,
        near_dupe_result: &NearDupeResult,
        policy_violations: &[String],
    ) -> Result<EgressCertificate, String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let cert_id = format!("cert_{}", Uuid::new_v4().to_string().replace("-", ""));
        
        // Hash the text
        let mut hasher = Sha256::new();
        hasher.update(request.text.as_bytes());
        let text_hash = hex::encode(hasher.finalize());
        
        // Hash the policy
        let policy = self.policies.get(&request.tenant)
            .ok_or_else(|| format!("No policy found for tenant: {}", request.tenant))?;
        let mut hasher = Sha256::new();
        hasher.update(format!("{:?}", policy).as_bytes());
        let policy_hash = hex::encode(hasher.finalize());

        let detectors = DetectorResults {
            pii: pii_result.clone(),
            secrets: secrets_result.clone(),
            near_dupe: near_dupe_result.clone(),
            policy_violations: policy_violations.to_vec(),
        };

        let mut certificate = EgressCertificate {
            cert_id,
            plan_id: request.plan_id.clone(),
            tenant: request.tenant.clone(),
            detectors,
            policy_hash,
            text_hash,
            timestamp: now,
            signer: None,
        };

        // Sign the certificate if signing key is available
        if let Some(key) = &self.signing_key {
            certificate.signer = self.sign_certificate(&certificate, key).await;
        }

        Ok(certificate)
    }

    /// Sign certificate
    async fn sign_certificate(&self, certificate: &EgressCertificate, key: &[u8]) -> Option<String> {
        let data = format!(
            "{}{}{}{}{}",
            certificate.cert_id,
            certificate.tenant,
            certificate.text_hash,
            certificate.timestamp,
            certificate.policy_hash
        );

        let mut hasher = Sha256::new();
        hasher.update(data.as_bytes());
        hasher.update(key);
        let result = hasher.finalize();

        Some(hex::encode(result))
    }

    /// Store certificate in ledger
    async fn store_certificate_in_ledger(&self, certificate: &EgressCertificate) -> Result<(), String> {
        let client = reqwest::Client::new();
        let response = client
            .post(&format!("{}/egress-certificates", self.ledger_url))
            .json(certificate)
            .send()
            .await
            .map_err(|e| format!("Failed to store certificate: {}", e))?;

        if !response.status().is_success() {
            return Err(format!(
                "Ledger returned error: {}",
                response.status()
            ));
        }

        Ok(())
    }
}

/// HTTP handlers
async fn egress_handler(
    req: HttpRequest,
    payload: web::Json<EgressRequest>,
    firewall: web::Data<EgressFirewall>,
) -> Result<HttpResponse, Error> {
    let response = firewall.process_egress(payload.into_inner()).await
        .map_err(|e| actix_web::error::ErrorBadRequest(e))?;

    Ok(HttpResponse::Ok().json(response))
}

async fn health_handler() -> Result<HttpResponse, Error> {
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "status": "healthy",
        "timestamp": SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs()
    })))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // Initialize firewall
    let mut firewall = EgressFirewall::new("http://localhost:8080".to_string());

    // Add policy templates
    firewall.add_policy(PolicyTemplate {
        name: "acme-corp-policy".to_string(),
        tenant: "acme-corp".to_string(),
        blacklist_phrases: vec![
            "internal only".to_string(),
            "confidential".to_string(),
            "secret".to_string(),
        ],
        tenant_secrets: vec![
            "acme-api-key-123".to_string(),
            "acme-secret-456".to_string(),
        ],
        pii_allowed: false,
        secrets_allowed: false,
        near_dupe_threshold: 0.8,
    });

    // Set signing key
    firewall.set_signing_key(b"test_signing_key".to_vec());

    // Start HTTP server
    HttpServer::new(move || {
        App::new()
            .app_data(web::Data::new(firewall.clone()))
            .route("/egress", web::post().to(egress_handler))
            .route("/health", web::get().to(health_handler))
    })
    .bind("127.0.0.1:8081")?
    .run()
    .await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_pii_detection() {
        let firewall = EgressFirewall::new("http://localhost:8080".to_string());

        let request = EgressRequest {
            text: "Contact me at john.doe@example.com or call 555-123-4567".to_string(),
            tenant: "test-tenant".to_string(),
            subject_id: "user_123".to_string(),
            plan_id: Some("plan_123".to_string()),
            context: HashMap::new(),
        };

        let pii_result = firewall.detect_pii(&request.text);
        assert!(pii_result.detected);
        assert!(pii_result.types.contains(&"email".to_string()));
        assert!(pii_result.types.contains(&"phone".to_string()));
    }

    #[tokio::test]
    async fn test_secret_detection() {
        let firewall = EgressFirewall::new("http://localhost:8080".to_string());

        let request = EgressRequest {
            text: "API key: sk-1234567890abcdef1234567890abcdef".to_string(),
            tenant: "test-tenant".to_string(),
            subject_id: "user_123".to_string(),
            plan_id: Some("plan_123".to_string()),
            context: HashMap::new(),
        };

        let secrets_result = firewall.detect_secrets(&request.text);
        assert!(secrets_result.detected);
        assert!(secrets_result.types.contains(&"api_key".to_string()));
    }

    #[tokio::test]
    async fn test_policy_violation() {
        let mut firewall = EgressFirewall::new("http://localhost:8080".to_string());

        firewall.add_policy(PolicyTemplate {
            name: "test-policy".to_string(),
            tenant: "test-tenant".to_string(),
            blacklist_phrases: vec!["secret".to_string()],
            tenant_secrets: vec![],
            pii_allowed: false,
            secrets_allowed: false,
            near_dupe_threshold: 0.8,
        });

        let request = EgressRequest {
            text: "This is a secret document".to_string(),
            tenant: "test-tenant".to_string(),
            subject_id: "user_123".to_string(),
            plan_id: Some("plan_123".to_string()),
            context: HashMap::new(),
        };

        let policy = firewall.policies.get("test-tenant").unwrap();
        let violations = firewall.check_policy_violations(&request.text, policy);
        assert!(!violations.is_empty());
        assert!(violations[0].contains("Blacklisted phrase"));
    }
} 