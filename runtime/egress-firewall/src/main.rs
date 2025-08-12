use actix_web::{web, App, HttpServer, HttpResponse, HttpRequest, Error};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
use uuid::Uuid;
use sha2::{Sha256, Digest};
use regex::Regex;
use std::collections::HashSet;
use std::time::Duration;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use std::thread;

/// Egress request with text to be checked
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressRequest {
    pub text: String,
    pub tenant: String,
    pub subject_id: String,
    pub plan_id: Option<String>,
    pub context: HashMap<String, String>,
    pub streaming: bool, // Enable streaming detection
}

/// Egress response with certificate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressResponse {
    pub text: String,
    pub certificate: EgressCertificate,
    pub warnings: Vec<String>,
    pub blocked: bool,
    pub block_reason: Option<String>,
}

/// Enhanced egress certificate for audit trail
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertificate {
    pub cert_id: String,
    pub plan_id: Option<String>,
    pub tenant: String,
    pub detector_flags: DetectorFlags,
    pub near_dupe_score: f64,
    pub policy_hash: String,
    pub text_hash: String,
    pub timestamp: u64,
    pub signer: Option<String>,
    // Enhanced non-interference verdict fields
    pub non_interference: NonInterferenceVerdict,
    pub influencing_labels: Vec<String>,
    pub attestation_ref: Option<String>,
    // Additional security fields
    pub pii_detected: Vec<String>,
    pub secrets_detected: Vec<String>,
    pub entropy_score: f64,
    pub format_analysis: FormatAnalysis,
    pub simhash: String,
    pub minhash_signature: Option<String>,
    pub llm_analysis_required: bool,
    pub llm_verdict: Option<String>,
}

/// Non-interference verdict for formal security verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NonInterferenceVerdict {
    Passed,
    Failed { reason: String, severity: String },
    Ambiguous { confidence: f64, requires_llm: bool },
}

/// Format and entropy analysis
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FormatAnalysis {
    pub text_length: usize,
    pub word_count: usize,
    pub avg_word_length: f64,
    pub entropy_per_char: f64,
    pub contains_code: bool,
    pub contains_structured_data: bool,
    pub language_detected: Option<String>,
}

/// Detector flags for quick reference
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectorFlags {
    pub pii_detected: bool,
    pub secrets_detected: bool,
    pub near_dupe_detected: bool,
    pub policy_violations: bool,
    pub high_entropy: bool,
    pub suspicious_format: bool,
}

/// Detector results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectorResults {
    pub pii: PiiResult,
    pub secrets: SecretsResult,
    pub near_dupe: NearDupeResult,
    pub policy_violations: Vec<String>,
    pub entropy: EntropyResult,
    pub format: FormatAnalysis,
}

/// PII detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PiiResult {
    pub detected: bool,
    pub types: Vec<String>,
    pub confidence: f64,
    pub redacted: bool,
    pub locations: Vec<Location>,
}

/// Secret detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecretsResult {
    pub detected: bool,
    pub types: Vec<String>,
    pub confidence: f64,
    pub redacted: bool,
    pub locations: Vec<Location>,
}

/// Location information for detected items
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    pub start: usize,
    pub end: usize,
    pub text: String,
    pub confidence: f64,
}

/// Near-duplicate detection result with enhanced algorithms
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NearDupeResult {
    pub score: f64,
    pub threshold: f64,
    pub is_duplicate: bool,
    pub similar_texts: Vec<String>,
    pub simhash_distance: f64,
    pub minhash_similarity: Option<f64>,
    pub algorithm_used: String,
}

/// Entropy analysis result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EntropyResult {
    pub per_char: f64,
    pub per_word: f64,
    pub is_suspicious: bool,
    pub threshold: f64,
}

/// Egress firewall service with streaming capabilities
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
    
    /// Streaming detection channel
    streaming_tx: Option<mpsc::Sender<StreamingResult>>,
    
    /// Detection history for near-duplicate analysis
    detection_history: Arc<Mutex<Vec<String>>>,
    
    /// LLM client for ambiguous cases
    llm_client: Option<Box<dyn LlmAnalyzer>>,
}

/// Streaming detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamingResult {
    pub cert_id: String,
    pub detector: String,
    pub result: String,
    pub confidence: f64,
    pub timestamp: u64,
}

/// LLM analyzer trait for ambiguous cases
pub trait LlmAnalyzer: Send + Sync {
    fn analyze_security(&self, text: &str, context: &HashMap<String, String>) -> Result<String, String>;
    fn name(&self) -> &str;
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

/// Enhanced near-duplicate detector trait
pub trait NearDupeDetector: Send + Sync {
    fn detect(&self, text: &str, history: &[String]) -> NearDupeResult;
    fn name(&self) -> &str;
    fn update_history(&mut self, text: String);
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
    pub entropy_threshold: f64,
    pub non_interference_policy: NonInterferencePolicy,
}

/// Non-interference policy configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NonInterferencePolicy {
    pub strict_mode: bool,
    pub allowed_influencing_labels: Vec<String>,
    pub blocked_influencing_labels: Vec<String>,
    pub confidence_threshold: f64,
    pub require_llm_verification: bool,
}

/// Email PII detector
pub struct EmailDetector;

impl PiiDetector for EmailDetector {
    fn detect(&self, text: &str) -> PiiResult {
        let email_regex = Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b").unwrap();
        let matches: Vec<_> = email_regex.find_iter(text).collect();
        
        let locations: Vec<Location> = matches.iter().map(|m| Location {
            start: m.start(),
            end: m.end(),
            text: m.as_str().to_string(),
            confidence: 0.95,
        }).collect();
        
        PiiResult {
            detected: !matches.is_empty(),
            types: if !matches.is_empty() { vec!["email".to_string()] } else { vec![] },
            confidence: if !matches.is_empty() { 0.95 } else { 0.0 },
            redacted: false,
            locations,
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
        
        let locations: Vec<Location> = matches.iter().map(|m| Location {
            start: m.start(),
            end: m.end(),
            text: m.as_str().to_string(),
            confidence: 0.90,
        }).collect();
        
        PiiResult {
            detected: !matches.is_empty(),
            types: if !matches.is_empty() { vec!["phone".to_string()] } else { vec![] },
            confidence: if !matches.is_empty() { 0.90 } else { 0.0 },
            redacted: false,
            locations,
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
        
        let locations: Vec<Location> = matches.iter().map(|m| Location {
            start: m.start(),
            end: m.end(),
            text: m.as_str().to_string(),
            confidence: 0.99,
        }).collect();
        
        PiiResult {
            detected: !matches.is_empty(),
            types: if !matches.is_empty() { vec!["ssn".to_string()] } else { vec![] },
            confidence: if !matches.is_empty() { 0.99 } else { 0.0 },
            redacted: false,
            locations,
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
        let mut locations = Vec::new();
        
        for pattern in api_key_patterns {
            let regex = Regex::new(pattern).unwrap();
            for cap in regex.find_iter(text) {
                detected = true;
                types.push("api_key".to_string());
                locations.push(Location {
                    start: cap.start(),
                    end: cap.end(),
                    text: cap.as_str().to_string(),
                    confidence: 0.95,
                });
            }
        }
        
        SecretsResult {
            detected,
            types,
            confidence: if detected { 0.95 } else { 0.0 },
            redacted: false,
            locations,
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
        let mut locations = Vec::new();
        
        for pattern in password_patterns {
            let regex = Regex::new(pattern).unwrap();
            for cap in regex.find_iter(text) {
                detected = true;
                types.push("password".to_string());
                locations.push(Location {
                    start: cap.start(),
                    end: cap.end(),
                    text: cap.as_str().to_string(),
                    confidence: 0.90,
                });
            }
        }
        
        SecretsResult {
            detected,
            types,
            confidence: if detected { 0.90 } else { 0.0 },
            redacted: false,
            locations,
        }
    }
    
    fn name(&self) -> &str {
        "password_detector"
    }
}

/// Enhanced SimHash + MinHash near-duplicate detector
pub struct EnhancedDupeDetector {
    threshold: f64,
    history: Vec<String>,
    simhash_bits: usize,
    minhash_permutations: usize,
}

impl EnhancedDupeDetector {
    pub fn new(threshold: f64) -> Self {
        Self {
            threshold,
            history: Vec::new(),
            simhash_bits: 64,
            minhash_permutations: 128,
        }
    }
    
    fn calculate_simhash(&self, text: &str) -> String {
        // Simplified SimHash calculation
        let mut hash = [0u64; 64];
        let words: Vec<&str> = text.split_whitespace().collect();
        
        for word in words {
            let word_hash = self.hash_word(word);
            for i in 0..64 {
                if (word_hash >> i) & 1 == 1 {
                    hash[i] += 1;
                } else {
                    hash[i] -= 1;
                }
            }
        }
        
        // Convert to hex string
        let mut result = String::new();
        for i in 0..64 {
            if hash[i] > 0 {
                result.push('1');
            } else {
                result.push('0');
            }
        }
        
        // Convert binary to hex
        let mut hex_result = String::new();
        for chunk in result.as_bytes().chunks(4) {
            let chunk_str = std::str::from_utf8(chunk).unwrap_or("0000");
            let decimal = u8::from_str_radix(chunk_str, 2).unwrap_or(0);
            hex_result.push_str(&format!("{:x}", decimal));
        }
        
        hex_result
    }
    
    fn calculate_minhash(&self, text: &str) -> Option<String> {
        if text.len() < 10 {
            return None; // Too short for meaningful MinHash
        }
        
        // Simplified MinHash using character n-grams
        let n = 3;
        let grams = self.get_ngrams(text, n);
        let mut minhash = vec![u64::MAX; self.minhash_permutations];
        
        for gram in grams {
            let hash = self.hash_string(gram);
            for i in 0..self.minhash_permutations {
                let permuted_hash = self.permute_hash(hash, i);
                if permuted_hash < minhash[i] {
                    minhash[i] = permuted_hash;
                }
            }
        }
        
        // Convert to hex string
        let mut result = String::new();
        for hash in minhash {
            result.push_str(&format!("{:016x}", hash));
        }
        
        Some(result)
    }
    
    fn hash_word(&self, word: &str) -> u64 {
        let mut hash = 0u64;
        for (i, byte) in word.bytes().enumerate() {
            hash = hash.wrapping_add((byte as u64).wrapping_shl(i as u32));
        }
        hash
    }
    
    fn hash_string(&self, s: &str) -> u64 {
        let mut hash = 0u64;
        for (i, byte) in s.bytes().enumerate() {
            hash = hash.wrapping_add((byte as u64).wrapping_shl(i as u32));
        }
        hash
    }
    
    fn permute_hash(&self, hash: u64, permutation: usize) -> u64 {
        hash.wrapping_mul(permutation as u64).wrapping_add(permutation as u64)
    }
    
    fn get_ngrams(&self, text: &str, n: usize) -> Vec<String> {
        let mut grams = Vec::new();
        let chars: Vec<char> = text.chars().collect();
        
        for i in 0..=chars.len().saturating_sub(n) {
            let gram: String = chars[i..i + n].iter().collect();
            grams.push(gram);
        }
        
        grams
    }
    
    fn hamming_distance(&self, hash1: &str, hash2: &str) -> f64 {
        let mut distance = 0;
        let min_len = hash1.len().min(hash2.len());
        
        for i in 0..min_len {
            if hash1.chars().nth(i) != hash2.chars().nth(i) {
                distance += 1;
            }
        }
        
        distance as f64 / min_len as f64
    }
}

impl NearDupeDetector for EnhancedDupeDetector {
    fn detect(&self, text: &str, history: &[String]) -> NearDupeResult {
        let simhash = self.calculate_simhash(text);
        let minhash = self.calculate_minhash(text);
        
        let mut best_score = 0.0;
        let mut similar_texts = Vec::new();
        let mut algorithm_used = "simhash".to_string();
        
        // Check against history using SimHash
        for hist_text in history {
            let hist_simhash = self.calculate_simhash(hist_text);
            let distance = self.hamming_distance(&simhash, &hist_simhash);
            let similarity = 1.0 - distance;
            
            if similarity > best_score {
                best_score = similarity;
                similar_texts = vec![hist_text.clone()];
                algorithm_used = "simhash".to_string();
            }
        }
        
        // If MinHash is available, use it for more precise detection
        if let Some(minhash_sig) = &minhash {
            for hist_text in history {
                if let Some(hist_minhash) = self.calculate_minhash(hist_text) {
                    let minhash_similarity = self.calculate_minhash_similarity(minhash_sig, &hist_minhash);
                    if minhash_similarity > best_score {
                        best_score = minhash_similarity;
                        similar_texts = vec![hist_text.clone()];
                        algorithm_used = "minhash".to_string();
                    }
                }
            }
        }
        
        let is_duplicate = best_score > self.threshold;
        
        NearDupeResult {
            score: best_score,
            threshold: self.threshold,
            is_duplicate,
            similar_texts,
            simhash_distance: 1.0 - best_score,
            minhash_similarity: if algorithm_used == "minhash" { Some(best_score) } else { None },
            algorithm_used,
        }
    }
    
    fn name(&self) -> &str {
        "enhanced_dupe_detector"
    }
    
    fn update_history(&mut self, text: String) {
        self.history.push(text);
        // Keep only last 1000 texts to prevent memory bloat
        if self.history.len() > 1000 {
            self.history.remove(0);
        }
    }
}

impl EnhancedDupeDetector {
    fn calculate_minhash_similarity(&self, hash1: &str, hash2: &str) -> f64 {
        let mut matches = 0;
        let min_len = hash1.len().min(hash2.len());
        
        for i in 0..min_len {
            if hash1.chars().nth(i) == hash2.chars().nth(i) {
                matches += 1;
            }
        }
        
        matches as f64 / min_len as f64
    }
}

/// Entropy analyzer
pub struct EntropyAnalyzer;

impl EntropyAnalyzer {
    pub fn analyze(&self, text: &str) -> EntropyResult {
        let chars: Vec<char> = text.chars().collect();
        let char_freq: HashMap<char, usize> = chars.iter().fold(HashMap::new(), |mut acc, &c| {
            *acc.entry(c).or_insert(0) += 1;
            acc
        });
        
        let total_chars = chars.len() as f64;
        let mut entropy = 0.0;
        
        for &count in char_freq.values() {
            let p = count as f64 / total_chars;
            if p > 0.0 {
                entropy -= p * p.log2();
            }
        }
        
        let words: Vec<&str> = text.split_whitespace().collect();
        let word_freq: HashMap<&str, usize> = words.iter().fold(HashMap::new(), |mut acc, &&w| {
            *acc.entry(w).or_insert(0) += 1;
            acc
        });
        
        let total_words = words.len() as f64;
        let mut word_entropy = 0.0;
        
        for &count in word_freq.values() {
            let p = count as f64 / total_words;
            if p > 0.0 {
                word_entropy -= p * p.log2();
            }
        }
        
        let threshold = 4.0; // Adjustable threshold
        
        EntropyResult {
            per_char: entropy,
            per_word: word_entropy,
            is_suspicious: entropy > threshold || word_entropy > threshold,
            threshold,
        }
    }
}

/// Format analyzer
pub struct FormatAnalyzer;

impl FormatAnalyzer {
    pub fn analyze(&self, text: &str) -> FormatAnalysis {
        let words: Vec<&str> = text.split_whitespace().collect();
        let word_count = words.len();
        
        let total_word_length: usize = words.iter().map(|w| w.len()).sum();
        let avg_word_length = if word_count > 0 {
            total_word_length as f64 / word_count as f64
        } else {
            0.0
        };
        
        let contains_code = text.contains("function") || text.contains("class") || 
                           text.contains("import") || text.contains("def ") ||
                           text.contains("var ") || text.contains("const ");
        
        let contains_structured_data = text.contains("{") && text.contains("}") ||
                                     text.contains("[") && text.contains("]") ||
                                     text.contains("<") && text.contains(">");
        
        // Simple language detection (can be enhanced)
        let language_detected = if contains_code {
            if text.contains("function") || text.contains("var ") {
                Some("javascript".to_string())
            } else if text.contains("def ") {
                Some("python".to_string())
            } else if text.contains("class") && text.contains("public") {
                Some("java".to_string())
            } else {
                Some("code".to_string())
            }
        } else {
            None
        };
        
        FormatAnalysis {
            text_length: text.len(),
            word_count,
            avg_word_length,
            entropy_per_char: 0.0, // Will be calculated separately
            contains_code,
            contains_structured_data,
            language_detected,
        }
    }
}

impl EgressFirewall {
    pub fn new(ledger_url: String) -> Self {
        let mut firewall = Self {
            pii_detectors: Vec::new(),
            secret_detectors: Vec::new(),
            near_dupe_detector: Box::new(EnhancedDupeDetector::new(0.8)),
            policies: HashMap::new(),
            signing_key: None,
            ledger_url,
            streaming_tx: None,
            detection_history: Arc::new(Mutex::new(Vec::new())),
            llm_client: None,
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

    /// Enable streaming detection
    pub fn enable_streaming(&mut self) -> mpsc::Receiver<StreamingResult> {
        let (tx, rx) = mpsc::channel(100);
        self.streaming_tx = Some(tx);
        rx
    }

    /// Set LLM client for ambiguous cases
    pub fn set_llm_client(&mut self, client: Box<dyn LlmAnalyzer>) {
        self.llm_client = Some(client);
    }

    /// Process egress request with enhanced pipeline
    pub async fn process_egress(&self, request: EgressRequest) -> Result<EgressResponse, String> {
        let start_time = std::time::Instant::now();
        let mut warnings = Vec::new();
        
        // Get policy for tenant
        let policy = self.policies.get(&request.tenant)
            .ok_or_else(|| format!("No policy found for tenant: {}", request.tenant))?;
        
        // ENHANCED PIPELINE: Dictionary → Format/Entropy → SimHash → (opt)MinHash → LLM only if ambiguous
        
        // 1. Dictionary-based detection (PII, secrets)
        let pii_result = self.detect_pii(&request.text);
        let secrets_result = self.detect_secrets(&request.text);
        
        // 2. Format and entropy analysis
        let format_analyzer = FormatAnalyzer;
        let format_analysis = format_analyzer.analyze(&request.text);
        
        let entropy_analyzer = EntropyAnalyzer;
        let entropy_result = entropy_analyzer.analyze(&request.text);
        
        // 3. SimHash calculation
        let simhash = self.calculate_simhash(&request.text);
        
        // 4. MinHash calculation (optional, for longer texts)
        let minhash_signature = if request.text.len() > 100 {
            self.calculate_minhash(&request.text)
        } else {
            None
        };
        
        // 5. Near-duplicate detection using enhanced algorithms
        let near_dupe_result = self.detect_near_duplicates(&request.text).await;
        
        // 6. Check policy violations
        let policy_violations = self.check_policy_violations(&request.text, policy);
        
        // 7. Non-interference analysis
        let (non_interference, influencing_labels, requires_llm) = 
            self.analyze_non_interference(&request, policy, &pii_result, &secrets_result).await?;
        
        // 8. LLM analysis if required or ambiguous
        let mut llm_verdict = None;
        if requires_llm || matches!(non_interference, NonInterferenceVerdict::Ambiguous { .. }) {
            if let Some(llm_client) = &self.llm_client {
                llm_verdict = Some(llm_client.analyze_security(&request.text, &request.context)?);
            }
        }
        
        // 9. Determine if response should be blocked
        let (blocked, block_reason) = self.determine_block_status(
            &pii_result, &secrets_result, &near_dupe_result, 
            &policy_violations, &non_interference, &entropy_result, policy
        );
        
        // 10. Apply redactions if needed
        let mut processed_text = request.text.clone();
        if pii_result.redacted || secrets_result.redacted {
            processed_text = self.apply_redactions(&request.text, &pii_result, &secrets_result);
        }
        
        // 11. Generate warnings
        if pii_result.detected && !policy.pii_allowed {
            warnings.push("PII detected but not allowed by policy".to_string());
        }
        
        if secrets_result.detected && !policy.secrets_allowed {
            warnings.push("Secrets detected but not allowed by policy".to_string());
        }
        
        if near_dupe_result.is_duplicate {
            warnings.push("Near-duplicate content detected".to_string());
        }
        
        if entropy_result.is_suspicious {
            warnings.push("High entropy detected - potential encoding or encryption".to_string());
        }
        
        if !policy_violations.is_empty() {
            warnings.extend(policy_violations.iter().map(|v| format!("Policy violation: {}", v)));
        }
        
        // 12. Generate enhanced certificate
        let certificate = self.generate_enhanced_certificate(
            &request, &pii_result, &secrets_result, &near_dupe_result, 
            &policy_violations, &format_analysis, &entropy_result, 
            &simhash, &minhash_signature, &non_interference, 
            &influencing_labels, &llm_verdict
        ).await?;
        
        // 13. Store certificate in ledger
        self.store_certificate_in_ledger(&certificate).await?;
        
        // 14. Update detection history for near-duplicate analysis
        self.update_detection_history(&request.text).await;
        
        // 15. Send streaming results if enabled
        if let Some(tx) = &self.streaming_tx {
            let _ = tx.send(StreamingResult {
                cert_id: certificate.cert_id.clone(),
                detector: "comprehensive".to_string(),
                result: if blocked { "blocked".to_string() } else { "passed".to_string() },
                confidence: 0.95,
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            }).await;
        }
        
        let processing_time = start_time.elapsed();
        if processing_time.as_millis() > 400 {
            warnings.push(format!("Processing time {}ms exceeds 400ms SLO", processing_time.as_millis()));
        }
        
        Ok(EgressResponse {
            text: processed_text,
            certificate,
            warnings,
            blocked,
            block_reason,
        })
    }

    /// Detect PII in text
    fn detect_pii(&self, text: &str) -> PiiResult {
        let mut all_types = Vec::new();
        let mut max_confidence = 0.0;
        let mut any_redacted = false;
        let mut all_locations = Vec::new();
        
        for detector in &self.pii_detectors {
            let result = detector.detect(text);
            if result.detected {
                all_types.extend(result.types);
                max_confidence = max_confidence.max(result.confidence);
                any_redacted = any_redacted || result.redacted;
                all_locations.extend(result.locations);
            }
        }
        
        PiiResult {
            detected: !all_types.is_empty(),
            types: all_types,
            confidence: max_confidence,
            redacted: any_redacted,
            locations: all_locations,
        }
    }

    /// Detect secrets in text
    fn detect_secrets(&self, text: &str) -> SecretsResult {
        let mut all_types = Vec::new();
        let mut max_confidence = 0.0;
        let mut any_redacted = false;
        let mut all_locations = Vec::new();
        
        for detector in &self.secret_detectors {
            let result = detector.detect(text);
            if result.detected {
                all_types.extend(result.types);
                max_confidence = max_confidence.max(result.confidence);
                any_redacted = any_redacted || result.redacted;
                all_locations.extend(result.locations);
            }
        }
        
        SecretsResult {
            detected: !all_types.is_empty(),
            types: all_types,
            confidence: max_confidence,
            redacted: any_redacted,
            locations: all_locations,
        }
    }

    /// Detect near-duplicates using enhanced algorithms
    async fn detect_near_duplicates(&self, text: &str) -> NearDupeResult {
        let history = self.detection_history.lock().unwrap().clone();
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

    /// Analyze non-interference based on label flow and content analysis
    async fn analyze_non_interference(
        &self,
        request: &EgressRequest,
        policy: &PolicyTemplate,
        pii_result: &PiiResult,
        secrets_result: &SecretsResult,
    ) -> Result<(NonInterferenceVerdict, Vec<String>, bool), String> {
        // Extract labels from context
        let labels_out: Vec<String> = request.context
            .get("labels_out")
            .map(|s| s.split(',').map(|s| s.trim().to_string()).collect())
            .unwrap_or_default();

        let allowed_out: Vec<String> = request.context
            .get("allowed_out")
            .map(|s| s.split(',').map(|s| s.trim().to_string()).collect())
            .unwrap_or_default();

        let labels_in: Vec<String> = request.context
            .get("labels_in")
            .map(|s| s.split(',').map(|s| s.trim().to_string()).collect())
            .unwrap_or_default();

        // Check if labels_out are properly contained within allowed_out
        let mut violating_labels = Vec::new();
        for label in &labels_out {
            if !allowed_out.contains(label) {
                violating_labels.push(label.clone());
            }
        }

        if !violating_labels.is_empty() {
            return Ok((
                NonInterferenceVerdict::Failed {
                    reason: format!("Labels {} not allowed in output", violating_labels.join(", ")),
                    severity: "high".to_string(),
                },
                labels_in,
                false,
            ));
        }

        // Check if any labels from input influenced the output
        let influencing_labels: Vec<String> = labels_in.into_iter()
            .filter(|label| labels_out.contains(label))
            .collect();

        // Check for blocked influencing labels
        for label in &influencing_labels {
            if policy.non_interference_policy.blocked_influencing_labels.contains(label) {
                return Ok((
                    NonInterferenceVerdict::Failed {
                        reason: format!("Blocked influencing label: {}", label),
                        severity: "critical".to_string(),
                    },
                    influencing_labels,
                    false,
                ));
            }
        }

        // Check confidence threshold
        let confidence = self.calculate_confidence_score(pii_result, secrets_result);
        if confidence < policy.non_interference_policy.confidence_threshold {
            let requires_llm = policy.non_interference_policy.require_llm_verification;
            return Ok((
                NonInterferenceVerdict::Ambiguous {
                    confidence,
                    requires_llm,
                },
                influencing_labels,
                requires_llm,
            ));
        }

        Ok((
            NonInterferenceVerdict::Passed,
            influencing_labels,
            false,
        ))
    }

    /// Calculate confidence score for non-interference analysis
    fn calculate_confidence_score(&self, pii_result: &PiiResult, secrets_result: &SecretsResult) -> f64 {
        let mut score = 1.0;
        
        if pii_result.detected {
            score *= 0.8; // Reduce confidence if PII detected
        }
        
        if secrets_result.detected {
            score *= 0.7; // Reduce confidence if secrets detected
        }
        
        score
    }

    /// Determine if response should be blocked
    fn determine_block_status(
        &self,
        pii_result: &PiiResult,
        secrets_result: &SecretsResult,
        near_dupe_result: &NearDupeResult,
        policy_violations: &[String],
        non_interference: &NonInterferenceVerdict,
        entropy_result: &EntropyResult,
        policy: &PolicyTemplate,
    ) -> (bool, Option<String>) {
        // Block if critical PII/secret leaks
        if pii_result.detected && !policy.pii_allowed {
            return (true, Some("Critical PII leak detected".to_string()));
        }
        
        if secrets_result.detected && !policy.secrets_allowed {
            return (true, Some("Critical secret leak detected".to_string()));
        }
        
        // Block if non-interference failed
        if matches!(non_interference, NonInterferenceVerdict::Failed { .. }) {
            return (true, Some("Non-interference check failed".to_string()));
        }
        
        // Block if policy violations
        if !policy_violations.is_empty() {
            return (true, Some(format!("Policy violations: {}", policy_violations.join(", "))));
        }
        
        // Block if suspicious entropy
        if entropy_result.is_suspicious && policy.non_interference_policy.strict_mode {
            return (true, Some("Suspicious entropy detected in strict mode".to_string()));
        }
        
        (false, None)
    }

    /// Apply redactions to text
    fn apply_redactions(&self, text: &str, pii_result: &PiiResult, secrets_result: &SecretsResult) -> String {
        let mut redacted_text = text.to_string();
        
        // Sort locations by start position in reverse order to avoid index shifting
        let mut all_locations: Vec<&Location> = pii_result.locations.iter()
            .chain(secrets_result.locations.iter())
            .collect();
        all_locations.sort_by(|a, b| b.start.cmp(&a.start));
        
        for location in all_locations {
            let replacement = if location.text.contains('@') {
                "[EMAIL_REDACTED]"
            } else if location.text.chars().all(|c| c.is_numeric() || c == '-' || c == '.') {
                "[PHONE_REDACTED]"
            } else if location.text.len() == 11 && location.text.contains('-') {
                "[SSN_REDACTED]"
            } else if location.text.starts_with("sk-") || location.text.starts_with("pk_") {
                "[API_KEY_REDACTED]"
            } else {
                "[SECRET_REDACTED]"
            };
            
            redacted_text.replace_range(location.start..location.end, replacement);
        }
        
        redacted_text
    }

    /// Generate enhanced egress certificate
    async fn generate_enhanced_certificate(
        &self,
        request: &EgressRequest,
        pii_result: &PiiResult,
        secrets_result: &SecretsResult,
        near_dupe_result: &NearDupeResult,
        policy_violations: &[String],
        format_analysis: &FormatAnalysis,
        entropy_result: &EntropyResult,
        simhash: &str,
        minhash_signature: &Option<String>,
        non_interference: &NonInterferenceVerdict,
        influencing_labels: &[String],
        llm_verdict: &Option<String>,
    ) -> Result<EgressCertificate, String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let cert_id = Uuid::new_v4().to_string();
        let text_hash = self.calculate_text_hash(&request.text);
        let policy_hash = self.calculate_policy_hash(request.tenant.as_str());

        // Extract PII and secret types
        let pii_detected: Vec<String> = pii_result.types.clone();
        let secrets_detected: Vec<String> = secrets_result.types.clone();

        // Update format analysis with entropy
        let mut enhanced_format = format_analysis.clone();
        enhanced_format.entropy_per_char = entropy_result.per_char;

        let certificate = EgressCertificate {
            cert_id,
            plan_id: request.plan_id.clone(),
            tenant: request.tenant.clone(),
            detector_flags: DetectorFlags {
                pii_detected: pii_result.detected,
                secrets_detected: secrets_result.detected,
                near_dupe_detected: near_dupe_result.is_duplicate,
                policy_violations: !policy_violations.is_empty(),
                high_entropy: entropy_result.is_suspicious,
                suspicious_format: format_analysis.contains_code || format_analysis.contains_structured_data,
            },
            near_dupe_score: near_dupe_result.score,
            policy_hash,
            text_hash,
            timestamp: now,
            signer: None,
            non_interference: non_interference.clone(),
            influencing_labels: influencing_labels.to_vec(),
            attestation_ref: None,
            pii_detected,
            secrets_detected,
            entropy_score: entropy_result.per_char,
            format_analysis: enhanced_format,
            simhash: simhash.to_string(),
            minhash_signature: minhash_signature.clone(),
            llm_analysis_required: matches!(non_interference, NonInterferenceVerdict::Ambiguous { .. }),
            llm_verdict: llm_verdict.clone(),
        };

        // Sign certificate if signing key is available
        if let Some(key) = &self.signing_key {
            if let Some(signature) = self.sign_certificate(&certificate, key).await {
                let mut signed_cert = certificate.clone();
                signed_cert.signer = Some(signature);
                return Ok(signed_cert);
            }
        }

        Ok(certificate)
    }

    /// Calculate SHA-256 hash of text
    fn calculate_text_hash(&self, text: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(text.as_bytes());
        hex::encode(hasher.finalize())
    }

    /// Calculate SHA-256 hash of policy
    fn calculate_policy_hash(&self, tenant: &str) -> String {
        let policy = self.policies.get(tenant)
            .unwrap_or_else(|| panic!("No policy found for tenant: {}", tenant));
        let mut hasher = Sha256::new();
        hasher.update(format!("{:?}", policy).as_bytes());
        hex::encode(hasher.finalize())
    }

    /// Calculate SimHash
    fn calculate_simhash(&self, text: &str) -> String {
        // Use the enhanced detector's SimHash calculation
        if let Some(enhanced_detector) = self.near_dupe_detector.as_any().downcast_ref::<EnhancedDupeDetector>() {
            enhanced_detector.calculate_simhash(text)
        } else {
            // Fallback to basic hash
            let mut hasher = Sha256::new();
            hasher.update(text.as_bytes());
            hex::encode(hasher.finalize())
        }
    }

    /// Calculate MinHash
    fn calculate_minhash(&self, text: &str) -> Option<String> {
        if let Some(enhanced_detector) = self.near_dupe_detector.as_any().downcast_ref::<EnhancedDupeDetector>() {
            enhanced_detector.calculate_minhash(text)
        } else {
            None
        }
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
        // Create optimized HTTP client with connection pooling
        lazy_static! {
            static ref HTTP_CLIENT: reqwest::Client = reqwest::Client::builder()
                .pool_max_idle_per_host(10) // Optimize for typical load
                .pool_idle_timeout(Duration::from_secs(90)) // Keep connections alive
                .http2_prior_knowledge() // Force HTTP/2 for better performance
                .timeout(Duration::from_secs(30)) // Request timeout
                .connect_timeout(Duration::from_secs(10)) // Connection timeout
                .tcp_keepalive(Some(Duration::from_secs(30))) // TCP keepalive
                .build()
                .expect("Failed to create HTTP client");
        }
        let client = &*HTTP_CLIENT;

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

    /// Update detection history for near-duplicate analysis
    async fn update_detection_history(&self, text: &str) {
        if let Ok(mut history) = self.detection_history.lock() {
            history.push(text.to_string());
            // Keep only last 1000 texts to prevent memory bloat
            if history.len() > 1000 {
                history.remove(0);
            }
        }
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
        entropy_threshold: 4.0,
        non_interference_policy: NonInterferencePolicy {
            strict_mode: true,
            allowed_influencing_labels: vec!["sensitive".to_string()],
            blocked_influencing_labels: vec!["internal".to_string()],
            confidence_threshold: 0.95,
            require_llm_verification: true,
        },
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
            streaming: false,
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
            streaming: false,
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
            entropy_threshold: 4.0,
            non_interference_policy: NonInterferencePolicy {
                strict_mode: true,
                allowed_influencing_labels: vec!["sensitive".to_string()],
                blocked_influencing_labels: vec!["internal".to_string()],
                confidence_threshold: 0.95,
                require_llm_verification: true,
            },
        });

        let request = EgressRequest {
            text: "This is a secret document".to_string(),
            tenant: "test-tenant".to_string(),
            subject_id: "user_123".to_string(),
            plan_id: Some("plan_123".to_string()),
            context: HashMap::new(),
            streaming: false,
        };

        let policy = firewall.policies.get("test-tenant").unwrap();
        let violations = firewall.check_policy_violations(&request.text, policy);
        assert!(!violations.is_empty());
        assert!(violations[0].contains("Blacklisted phrase"));
    }
} 