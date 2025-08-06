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
};
use tokio::sync::RwLock;
use tower::ServiceBuilder;
use tower_http::{cors::CorsLayer, trace::TraceLayer};
use tracing::{error, info, warn};
use uuid::Uuid;

mod abac;
mod receipt;
mod storage;

use abac::{AbacPolicy, QueryContext};
use receipt::{AccessReceipt, ReceiptSigner};
use storage::{StorageAdapter, VectorIndex};

/// Retrieval Gateway server state
#[derive(Clone)]
pub struct AppState {
    storage: Arc<dyn StorageAdapter>,
    abac_policy: Arc<AbacPolicy>,
    receipt_signer: Arc<ReceiptSigner>,
    receipt_cache: Arc<RwLock<HashMap<String, AccessReceipt>>>,
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

    let state = AppState {
        storage,
        abac_policy,
        receipt_signer,
        receipt_cache,
    };

    // Build router
    let app = Router::new()
        .route("/query", post(handle_query))
        .route("/receipts", get(get_receipt))
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
    let start_time = SystemTime::now();

    // Validate capability token
    if !validate_capability_token(&request.capability_token, &request.tenant, &request.subject_id).await {
        warn!("Invalid capability token for tenant: {}", request.tenant);
        return Err(StatusCode::UNAUTHORIZED);
    }

    // Create query context
    let query_context = QueryContext {
        tenant: request.tenant.clone(),
        subject_id: request.subject_id.clone(),
        labels_filter: request.labels_filter.clone(),
        query_hash: compute_query_hash(&request.query),
    };

    // ABAC authorization check
    match state.abac_policy.authorize_query(&query_context).await {
        Ok(authorized) if !authorized => {
            warn!("ABAC denied query for tenant: {}", request.tenant);
            return Err(StatusCode::FORBIDDEN);
        }
        Err(e) => {
            error!("ABAC evaluation failed: {}", e);
            return Err(StatusCode::INTERNAL_SERVER_ERROR);
        }
        _ => {}
    }

    // Execute query with tenant isolation
    let results = match state
        .storage
        .search_with_tenant_isolation(
            &request.query,
            &request.tenant,
            &request.labels_filter,
            request.limit.unwrap_or(10),
        )
        .await
    {
        Ok(results) => results,
        Err(e) => {
            error!("Search failed: {}", e);
            return Err(StatusCode::INTERNAL_SERVER_ERROR);
        }
    };

    // Compute query metrics
    let query_time_ms = start_time
        .elapsed()
        .unwrap_or_default()
        .as_millis() as u64;

    // Generate access receipt
    let receipt = match generate_access_receipt(
        &state.receipt_signer,
        &query_context,
        &results,
        query_time_ms,
    )
    .await
    {
        Ok(receipt) => receipt,
        Err(e) => {
            error!("Failed to generate receipt: {}", e);
            return Err(StatusCode::INTERNAL_SERVER_ERROR);
        }
    };

    // Cache receipt
    {
        let mut cache = state.receipt_cache.write().await;
        cache.insert(receipt.receipt_id.clone(), receipt.clone());
    }

    // Submit receipt to ledger
    if let Err(e) = submit_receipt_to_ledger(&receipt).await {
        warn!("Failed to submit receipt to ledger: {}", e);
    }

    let response = QueryResponse {
        results,
        receipt,
        total_count: results.len(),
        query_time_ms,
    };

    Ok(Json(response))
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
fn compute_query_hash(query: &str) -> String {
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
    let receipt_id = format!("receipt_{}", Uuid::new_v4().to_string().replace("-", ""));
    
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .context("Failed to get current time")?
        .as_secs();

    // Compute result hash
    let result_hash = compute_result_hash(results);

    let receipt = AccessReceipt {
        receipt_id,
        tenant: context.tenant.clone(),
        subject_id: context.subject_id.clone(),
        query_hash: context.query_hash.clone(),
        index_shard: format!("shard_{}", context.tenant),
        timestamp: now,
        result_hash,
        result_count: results.len(),
        query_time_ms,
        signature: "placeholder_signature".to_string(), // Would be actual DSSE signature
    };

    // Sign receipt
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
    let client = reqwest::Client::new();
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
        let hash1 = compute_query_hash(query);
        let hash2 = compute_query_hash(query);
        
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