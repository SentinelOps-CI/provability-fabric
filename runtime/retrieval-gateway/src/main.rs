use anyhow::{Context, Result};
use axum::{
    extract::{Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    net::SocketAddr,
    sync::Arc,
    time::{SystemTime, UNIX_EPOCH},
    Duration,
};
use tokio::sync::RwLock;
use tower::ServiceBuilder;
use tower_http::{cors::CorsLayer, trace::TraceLayer};
use tracing::{debug, error, info, warn};
use uuid::Uuid;

mod abac;
mod cache;
mod receipt;
mod storage;

use abac::{AbacPolicy, QueryContext};
use cache::SemanticCache;
use receipt::{AccessReceipt, ReceiptSigner};
use storage::{StorageAdapter, VectorIndex};

/// Retrieval Gateway server state
#[derive(Clone)]
pub struct AppState {
    storage: Arc<dyn StorageAdapter>,
    abac_policy: Arc<AbacPolicy>,
    receipt_signer: Arc<ReceiptSigner>,
    receipt_cache: Arc<RwLock<HashMap<String, AccessReceipt>>>,
    semantic_cache: Arc<SemanticCache>,
}

/// Query request payload
#[derive(Debug, Deserialize)]
pub struct QueryRequest {
    pub query: String,
    pub tenant: String,
    pub subject_id: String,
    pub capability_token: String,
    pub labels_filter: Vec<String>,
    pub limit: Option<usize>,
}

/// Query response payload
#[derive(Debug, Serialize)]
pub struct QueryResponse {
    pub results: Vec<SearchResult>,
    pub receipt: AccessReceipt,
    pub total_count: usize,
    pub query_time_ms: u64,
}

/// Search result item
#[derive(Debug, Serialize)]
pub struct SearchResult {
    pub document_id: String,
    pub content: String,
    pub content_hash: String, // SHA-256 hash of content for evidence linking
    pub score: f64,
    pub metadata: HashMap<String, String>,
    pub labels: Vec<String>,
}

/// Receipt query parameters
#[derive(Debug, Deserialize)]
pub struct ReceiptQuery {
    pub receipt_id: String,
}

/// Health check response
#[derive(Debug, Serialize)]
pub struct HealthResponse {
    pub status: String,
    pub version: String,
    pub uptime_seconds: u64,
}

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize tracing
    tracing_subscriber::fmt::init();

    // Initialize components
    let storage = Arc::new(VectorIndex::new().await?);
    let abac_policy = Arc::new(AbacPolicy::load_from_file("abac.yaml").await?);
    let receipt_signer = Arc::new(ReceiptSigner::new().await?);
    let receipt_cache = Arc::new(RwLock::new(HashMap::new()));
    let semantic_cache = Arc::new(SemanticCache::new());

    let state = AppState {
        storage,
        abac_policy,
        receipt_signer,
        receipt_cache,
        semantic_cache,
    };

    // Create optimized HTTP client with connection pooling
    lazy_static::lazy_static! {
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

    // Build router
    let app = Router::new()
        .route("/query", post(handle_query))
        .route("/receipts", get(get_receipt))
        .route("/cache/stats", get(get_cache_stats))
        .route("/cache/invalidate/:tenant", post(invalidate_cache))
        .route("/health", get(health_check))
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CorsLayer::permissive()),
        )
        .with_state(state);

    // Start server
    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    info!("Retrieval Gateway listening on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .context("Server failed")?;

    Ok(())
}

/// Handle search query with ABAC enforcement
async fn handle_query(
    State(state): State<AppState>,
    Json(request): Json<QueryRequest>,
) -> Result<Json<QueryResponse>, StatusCode> {
    let start_time = std::time::Instant::now();

    // Validate capability token
    if !validate_capability_token(&request.capability_token, &request.tenant, &request.subject_id).await {
        return Err(StatusCode::FORBIDDEN);
    }

    // Create query context
    let context = QueryContext {
        tenant: request.tenant.clone(),
        subject_id: request.subject_id.clone(),
        query: request.query.clone(),
        query_hash: compute_query_hash(&request.query).await,
        index_shard: format!("shard_{}", request.tenant),
        labels_filter: request.labels_filter.clone(),
    };

    // Check ABAC policy
    if !state.abac_policy.evaluate(&context).await {
        return Err(StatusCode::FORBIDDEN);
    }

    // Try to get results from cache first
    let query_hash = context.query_hash.clone();
    let cached_results = state.semantic_cache.get(
        &query_hash,
        &request.labels_filter,
        &request.tenant,
    ).await;

    let results = if let Some(cached) = cached_results {
        debug!("Cache hit for query: {}", request.query);
        cached
    } else {
        debug!("Cache miss for query: {}", request.query);
        // Perform search
        let search_results = state.storage.search(&request.query, request.limit.unwrap_or(10)).await
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
        
        // Cache the results
        if let Err(e) = state.semantic_cache.put(
            &query_hash,
            &request.labels_filter,
            &request.tenant,
            search_results.clone(),
            None,
        ).await {
            warn!("Failed to cache results: {}", e);
        }
        
        search_results
    };

    // Add content hashes to results for evidence linking
    let results_with_hashes: Vec<SearchResult> = results
        .into_iter()
        .map(|result| {
            let content_hash = compute_content_hash(&result.content);
            SearchResult {
                document_id: result.document_id,
                content: result.content,
                content_hash, // Include content hash for evidence linking
                score: result.score,
                metadata: result.metadata,
                labels: result.labels,
            }
        })
        .collect();

    let query_time_ms = start_time.elapsed().as_millis() as u64;

    // Generate access receipt
    let receipt = generate_access_receipt(
        &state.receipt_signer,
        &context,
        &results_with_hashes,
        query_time_ms,
    ).await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    // Cache receipt
    {
        let mut cache = state.receipt_cache.write().await;
        cache.insert(receipt.receipt_id.clone(), receipt.clone());
    }

    // Submit to ledger
    if let Err(e) = submit_receipt_to_ledger(&receipt).await {
        warn!("Failed to submit receipt to ledger: {}", e);
    }

    Ok(Json(QueryResponse {
        results: results_with_hashes,
        receipt,
        total_count: results_with_hashes.len(),
        query_time_ms,
    }))
}

/// Get access receipt by ID
async fn get_receipt(
    State(state): State<AppState>,
    Query(params): Query<ReceiptQuery>,
) -> Result<Json<AccessReceipt>, StatusCode> {
    let cache = state.receipt_cache.read().await;
    
    match cache.get(&params.receipt_id) {
        Some(receipt) => Ok(Json(receipt.clone())),
        None => {
            warn!("Receipt not found: {}", params.receipt_id);
            Err(StatusCode::NOT_FOUND)
        }
    }
}

/// Get cache statistics for all tenants
async fn get_cache_stats(
    State(state): State<AppState>,
) -> Json<Vec<cache::TenantCacheStats>> {
    let stats = state.semantic_cache.get_all_stats().await;
    Json(stats)
}

/// Invalidate cache for a specific tenant
async fn invalidate_cache(
    State(state): State<AppState>,
    axum::extract::Path(tenant): axum::extract::Path<String>,
) -> StatusCode {
    match state.semantic_cache.invalidate_tenant(&tenant).await {
        Ok(_) => {
            info!("Cache invalidated for tenant: {}", tenant);
            StatusCode::OK
        }
        Err(_) => StatusCode::INTERNAL_SERVER_ERROR,
    }
}

/// Health check endpoint
async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "healthy".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        uptime_seconds: 0, // Would track actual uptime
    })
}

/// Validate capability token (simplified)
async fn validate_capability_token(token: &str, tenant: &str, subject_id: &str) -> bool {
    // In real implementation, would verify DSSE signature and check capabilities
    !token.is_empty() && !tenant.is_empty() && !subject_id.is_empty()
}

/// Compute hash of query for receipt
async fn compute_query_hash(query: &str) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(query.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Generate access receipt for query
async fn generate_access_receipt(
    signer: &ReceiptSigner,
    context: &QueryContext,
    results: &[SearchResult],
    query_time_ms: u64,
) -> Result<AccessReceipt> {
    let receipt_id = Uuid::new_v4().to_string();
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();

    // Extract content hashes for evidence linking
    let content_hashes: Vec<String> = results
        .iter()
        .map(|result| result.content_hash.clone())
        .collect();

    let receipt = AccessReceipt {
        receipt_id,
        tenant: context.tenant.clone(),
        subject_id: context.subject_id.clone(),
        query_hash: context.query_hash.clone(),
        index_shard: context.index_shard.clone(),
        timestamp,
        result_hash: compute_result_hash(results),
        content_hashes, // Include content hashes for evidence linking
        sign_alg: "ed25519".to_string(),
        sig: String::new(), // Will be populated by signer
    };

    // Sign the receipt
    let signed_receipt = signer.sign_receipt(&receipt).await?;
    Ok(signed_receipt)
}

/// Compute hash of search results
fn compute_result_hash(results: &[SearchResult]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    
    for result in results {
        hasher.update(result.document_id.as_bytes());
        hasher.update(result.content.as_bytes());
    }
    
    format!("{:x}", hasher.finalize())
}

/// Compute SHA-256 hash of content for evidence linking
fn compute_content_hash(content: &str) -> String {
    use sha2::{Sha256, Digest};
    let mut hasher = Sha256::new();
    hasher.update(content.as_bytes());
    hex::encode(hasher.finalize())
}

/// Submit receipt to ledger
async fn submit_receipt_to_ledger(receipt: &AccessReceipt) -> Result<()> {
    let client = &*lazy_static::lazy_static! {
        static ref HTTP_CLIENT: reqwest::Client = reqwest::Client::builder()
            .pool_max_idle_per_host(10) // Optimize for typical load
            .pool_idle_timeout(Duration::from_secs(90)) // Keep connections alive
            .http2_prior_knowledge() // Force HTTP/2 for better performance
            .timeout(Duration::from_secs(30)) // Request timeout
            .connect_timeout(Duration::from_secs(10)) // Connection timeout
            .tcp_keepalive(Some(Duration::from_secs(30))) // TCP keepalive
            .build()
            .expect("Failed to create HTTP client");
    };

    let ledger_endpoint = std::env::var("LEDGER_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:3000".to_string());

    let response = client
        .post(&format!("{}/receipts", ledger_endpoint))
        .json(receipt)
        .send()
        .await
        .context("Failed to submit receipt")?;

    if !response.status().is_success() {
        return Err(anyhow::anyhow!(
            "Ledger rejected receipt: {}",
            response.status()
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_query_hash() {
        let query = "test query";
        let hash1 = compute_query_hash(query).await;
        let hash2 = compute_query_hash(query).await;
        
        assert_eq!(hash1, hash2);
        assert_eq!(hash1.len(), 64); // SHA-256 hex string
    }

    #[test]
    fn test_result_hash() {
        let results = vec![
            SearchResult {
                document_id: "doc1".to_string(),
                content: "content1".to_string(),
                score: 0.9,
                metadata: HashMap::new(),
                labels: vec![],
            },
            SearchResult {
                document_id: "doc2".to_string(),
                content: "content2".to_string(),
                score: 0.8,
                metadata: HashMap::new(),
                labels: vec![],
            },
        ];

        let hash = compute_result_hash(&results);
        assert!(!hash.is_empty());
        assert_eq!(hash.len(), 64); // SHA-256 hex string
    }
}