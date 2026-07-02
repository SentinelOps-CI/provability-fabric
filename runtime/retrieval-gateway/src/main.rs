use anyhow::{Context, Result};
use axum::{
    extract::{Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    net::SocketAddr,
    sync::Arc,
    time::{Duration, SystemTime, UNIX_EPOCH},
};
use tokio::sync::RwLock;
use tower::ServiceBuilder;
use tower_http::{cors::CorsLayer, trace::TraceLayer};
use tracing::{debug, info, warn};
use uuid::Uuid;

mod abac;
mod cache;
mod receipt;
mod storage;

use abac::{AbacPolicy, QueryContext};
use cache::SemanticCache;
use receipt::{AccessReceipt, ReceiptSigner};
use storage::{StorageAdapter, VectorIndex};

lazy_static! {
    static ref HTTP_CLIENT: reqwest::Client = reqwest::Client::builder()
        .pool_max_idle_per_host(10)
        .pool_idle_timeout(Duration::from_secs(90))
        .timeout(Duration::from_secs(30))
        .connect_timeout(Duration::from_secs(10))
        .tcp_keepalive(Some(Duration::from_secs(30)))
        .build()
        .expect("Failed to create HTTP client");
}

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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub document_id: String,
    pub content: String,
    pub content_hash: String,
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
    tracing_subscriber::fmt::init();

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

    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    info!("Retrieval Gateway listening on {}", addr);

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .context("Failed to bind listener")?;
    axum::serve(listener, app).await.context("Server failed")?;

    Ok(())
}

/// Handle search query with ABAC enforcement
async fn handle_query(
    State(state): State<AppState>,
    Json(request): Json<QueryRequest>,
) -> Result<Json<QueryResponse>, StatusCode> {
    let start_time = std::time::Instant::now();

    if !validate_capability_token(&request.capability_token, &request.tenant, &request.subject_id)
        .await
    {
        return Err(StatusCode::FORBIDDEN);
    }

    let context = QueryContext {
        tenant: request.tenant.clone(),
        subject_id: request.subject_id.clone(),
        query: request.query.clone(),
        labels_filter: request.labels_filter.clone(),
        query_hash: compute_query_hash(&request.query).await,
        index_shard: format!("shard_{}", request.tenant),
    };

    if !state.abac_policy.evaluate(&context).await {
        return Err(StatusCode::FORBIDDEN);
    }

    if state.abac_policy.should_audit(&context) {
        debug!("Audit required for tenant={}", request.tenant);
    }
    let _rate_limits = state.abac_policy.get_rate_limits(&context);

    let query_hash = context.query_hash.clone();
    let cached_results = state
        .semantic_cache
        .get(&query_hash, &request.labels_filter, &request.tenant)
        .await;

    let results = if let Some(cached) = cached_results {
        debug!("Cache hit for query: {}", request.query);
        cached
    } else {
        debug!("Cache miss for query: {}", request.query);
        let search_results = state
            .storage
            .search_with_tenant_isolation(
                &request.query,
                &request.tenant,
                &request.labels_filter,
                request.limit.unwrap_or(10),
            )
            .await
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

        if let Err(e) = state
            .semantic_cache
            .put(
                &query_hash,
                &request.labels_filter,
                &request.tenant,
                search_results.clone(),
                None,
            )
            .await
        {
            warn!("Failed to cache results: {}", e);
        }

        search_results
    };

    let query_time_ms = start_time.elapsed().as_millis() as u64;

    let receipt = generate_access_receipt(
        &state.receipt_signer,
        &context,
        &results,
        query_time_ms,
    )
    .await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    {
        let mut cache = state.receipt_cache.write().await;
        cache.insert(receipt.receipt_id.clone(), receipt.clone());
    }

    if let Err(e) = submit_receipt_to_ledger(&receipt).await {
        warn!("Failed to submit receipt to ledger: {}", e);
    }

    let total_count = results.len();
    Ok(Json(QueryResponse {
        results,
        receipt,
        total_count,
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
async fn get_cache_stats(State(state): State<AppState>) -> Json<Vec<cache::TenantCacheStats>> {
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
        uptime_seconds: 0,
    })
}

/// Validate capability token (simplified)
async fn validate_capability_token(token: &str, tenant: &str, subject_id: &str) -> bool {
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
        .unwrap_or_default()
        .as_secs();

    let receipt = AccessReceipt {
        receipt_id,
        tenant: context.tenant.clone(),
        subject_id: context.subject_id.clone(),
        query_hash: context.query_hash.clone(),
        index_shard: context.index_shard.clone(),
        timestamp,
        result_hash: compute_result_hash(results),
        result_count: results.len(),
        query_time_ms,
        sign_alg: String::new(),
        sig: String::new(),
    };

    signer.sign_receipt(&receipt).await
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

/// Submit receipt to ledger
async fn submit_receipt_to_ledger(receipt: &AccessReceipt) -> Result<()> {
    let ledger_endpoint = std::env::var("LEDGER_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:3000".to_string());

    let response = HTTP_CLIENT
        .post(format!("{ledger_endpoint}/receipts"))
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
        assert_eq!(hash1.len(), 64);
    }

    #[test]
    fn test_result_hash() {
        let results = vec![
            SearchResult {
                document_id: "doc1".to_string(),
                content: "content1".to_string(),
                content_hash: "hash1".to_string(),
                score: 0.9,
                metadata: HashMap::new(),
                labels: vec![],
            },
            SearchResult {
                document_id: "doc2".to_string(),
                content: "content2".to_string(),
                content_hash: "hash2".to_string(),
                score: 0.8,
                metadata: HashMap::new(),
                labels: vec![],
            },
        ];

        let hash = compute_result_hash(&results);
        assert!(!hash.is_empty());
        assert_eq!(hash.len(), 64);
    }
}
