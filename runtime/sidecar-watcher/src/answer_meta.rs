use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Answer metadata for accuracy verification and evidence linking
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnswerMeta {
    /// Sources used to generate the answer
    pub sources: Vec<SourceReference>,
    
    /// Hash of the generated answer for integrity verification
    pub answer_hash: String,
    
    /// Confidence score (0.0-1.0) based on multiple factors
    pub confidence: f64,
    
    /// Whether fallback response was used
    pub fallback_used: bool,
    
    /// Additional metadata for accuracy tracking
    pub metadata: HashMap<String, String>,
}

/// Reference to a source used in answer generation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceReference {
    /// Receipt ID from retrieval gateway
    pub receipt_id: String,
    
    /// Content hash for evidence linking
    pub content_hash: String,
    
    /// Relevance score for this source
    pub relevance_score: f64,
    
    /// Labels associated with this source
    pub labels: Vec<String>,
}

/// Confidence calculation factors
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfidenceFactors {
    /// Number of sources used
    pub source_count: usize,
    
    /// Coverage percentage of query terms
    pub coverage_percentage: f64,
    
    /// Average relevance score of sources
    pub avg_relevance: f64,
    
    /// Entropy/logprobs if available
    pub entropy: Option<f64>,
    
    /// Whether sources are recent
    pub source_freshness: f64,
}

impl AnswerMeta {
    /// Create new answer metadata
    pub fn new(
        sources: Vec<SourceReference>,
        answer_hash: String,
        confidence: f64,
        fallback_used: bool,
    ) -> Self {
        Self {
            sources,
            answer_hash,
            confidence,
            fallback_used,
            metadata: HashMap::new(),
        }
    }
    
    /// Calculate confidence based on multiple factors
    pub fn calculate_confidence(&self, factors: &ConfidenceFactors) -> f64 {
        let mut confidence = 0.0;
        
        // Source count factor (0-30%)
        let source_factor = (factors.source_count.min(5) as f64 / 5.0) * 0.3;
        confidence += source_factor;
        
        // Coverage factor (0-25%)
        let coverage_factor = factors.coverage_percentage * 0.25;
        confidence += coverage_factor;
        
        // Relevance factor (0-25%)
        let relevance_factor = factors.avg_relevance * 0.25;
        confidence += relevance_factor;
        
        // Entropy factor (0-10%)
        if let Some(entropy) = factors.entropy {
            let entropy_factor = (1.0 - entropy.min(1.0)) * 0.1;
            confidence += entropy_factor;
        }
        
        // Freshness factor (0-10%)
        let freshness_factor = factors.source_freshness * 0.1;
        confidence += freshness_factor;
        
        confidence.min(1.0)
    }
    
    /// Check if confidence meets threshold for fallback
    pub fn should_use_fallback(&self, threshold: f64) -> bool {
        self.confidence < threshold
    }
    
    /// Get source content hashes for evidence linking
    pub fn get_content_hashes(&self) -> Vec<String> {
        self.sources
            .iter()
            .map(|source| source.content_hash.clone())
            .collect()
    }
    
    /// Get receipt IDs for audit trail
    pub fn get_receipt_ids(&self) -> Vec<String> {
        self.sources
            .iter()
            .map(|source| source.receipt_id.clone())
            .collect()
    }
    
    /// Add metadata key-value pair
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }
    
    /// Get metadata value
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }
}

impl SourceReference {
    /// Create new source reference
    pub fn new(
        receipt_id: String,
        content_hash: String,
        relevance_score: f64,
        labels: Vec<String>,
    ) -> Self {
        Self {
            receipt_id,
            content_hash,
            relevance_score,
            labels,
        }
    }
    
    /// Check if source has specific label
    pub fn has_label(&self, label: &str) -> bool {
        self.labels.iter().any(|l| l == label)
    }
    
    /// Get labels as comma-separated string
    pub fn get_labels_string(&self) -> String {
        self.labels.join(",")
    }
}

impl ConfidenceFactors {
    /// Create new confidence factors
    pub fn new(
        source_count: usize,
        coverage_percentage: f64,
        avg_relevance: f64,
        entropy: Option<f64>,
        source_freshness: f64,
    ) -> Self {
        Self {
            source_count,
            coverage_percentage,
            avg_relevance,
            entropy,
            source_freshness,
        }
    }
    
    /// Calculate coverage percentage from query terms and sources
    pub fn calculate_coverage(query_terms: &[String], source_content: &str) -> f64 {
        let mut covered_terms = 0;
        let content_lower = source_content.to_lowercase();
        
        for term in query_terms {
            if content_lower.contains(&term.to_lowercase()) {
                covered_terms += 1;
            }
        }
        
        if query_terms.is_empty() {
            0.0
        } else {
            covered_terms as f64 / query_terms.len() as f64
        }
    }
    
    /// Calculate average relevance from source scores
    pub fn calculate_avg_relevance(sources: &[SourceReference]) -> f64 {
        if sources.is_empty() {
            return 0.0;
        }
        
        let total_relevance: f64 = sources.iter().map(|s| s.relevance_score).sum();
        total_relevance / sources.len() as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_answer_meta_creation() {
        let sources = vec![
            SourceReference::new(
                "receipt_1".to_string(),
                "hash_1".to_string(),
                0.8,
                vec!["public".to_string()],
            ),
        ];
        
        let meta = AnswerMeta::new(
            sources,
            "answer_hash".to_string(),
            0.75,
            false,
        );
        
        assert_eq!(meta.sources.len(), 1);
        assert_eq!(meta.confidence, 0.75);
        assert!(!meta.fallback_used);
    }
    
    #[test]
    fn test_confidence_calculation() {
        let factors = ConfidenceFactors::new(3, 0.8, 0.7, Some(0.3), 0.9);
        let sources = vec![
            SourceReference::new(
                "receipt_1".to_string(),
                "hash_1".to_string(),
                0.8,
                vec!["public".to_string()],
            ),
        ];
        
        let meta = AnswerMeta::new(
            sources,
            "answer_hash".to_string(),
            0.0, // Will be calculated
            false,
        );
        
        let confidence = meta.calculate_confidence(&factors);
        assert!(confidence > 0.0 && confidence <= 1.0);
    }
    
    #[test]
    fn test_fallback_threshold() {
        let meta = AnswerMeta::new(
            vec![],
            "answer_hash".to_string(),
            0.4,
            false,
        );
        
        assert!(meta.should_use_fallback(0.6));
        assert!(!meta.should_use_fallback(0.3));
    }
    
    #[test]
    fn test_coverage_calculation() {
        let query_terms = vec!["hello".to_string(), "world".to_string()];
        let content = "Hello there, how are you doing?";
        
        let coverage = ConfidenceFactors::calculate_coverage(&query_terms, content);
        assert_eq!(coverage, 0.5); // "hello" is covered, "world" is not
    }
} 