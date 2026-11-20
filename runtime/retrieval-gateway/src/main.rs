/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

#![allow(dead_code)]

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
mod auth;
mod cache;
mod receipt;
mod result_commitment;
mod storage;

use abac::{AbacPolicy, QueryContext};
use auth::TokenVerifier;
use cache::SemanticCache;
use receipt::{AccessReceipt, ReceiptSigner};
use result_commitment::compute_result_commitment;
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
    token_verifier: Arc<TokenVerifier>,
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
    // Missing trusted public keys or issuer prevents service startup.
    let token_verifier = Arc::new(TokenVerifier::from_env()?);
    let receipt_signer = Arc::new(ReceiptSigner::new().await?);
    let receipt_cache = Arc::new(RwLock::new(HashMap::new()));
    let semantic_cache = Arc::new(SemanticCache::new());

    let state = AppState {
        storage,
        abac_policy,
        token_verifier,
        receipt_signer,
        receipt_cache,
        semantic_cache,
    };

    // Receipt lookup and cache administration have no authenticated
    // ownership protocol yet. Do not expose those privileged endpoints.
    let app = Router::new()
        .route("/query", post(handle_query))
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

    let claims = state
        .token_verifier
        .verify(&request.capability_token, &request.tenant, &request.subject_id)
        .map_err(|_| StatusCode::FORBIDDEN)?;
    let limit = request.limit.unwrap_or(10);
    if limit == 0 || limit > state.abac_policy.query_context.complexity_limits.max_results_per_query {
        return Err(StatusCode::BAD_REQUEST);
    }

    let context = QueryContext {
        tenant: request.tenant.clone(),
        subject_id: request.subject_id.clone(),
        query: request.query.clone(),
        labels_filter: request.labels_filter.clone(),
        query_hash: compute_query_hash(&request.query).await,
        index_shard: format!("shard_{}", request.tenant),
        allowed_labels: claims.allowed_labels,
        capabilities: claims.capabilities,
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
        .get(&query_hash, &request.labels_filter, &request.tenant, limit)
        .await;

    let results = if let Some(cached) = cached_results {
        debug!("Cache hit for tenant {}", request.tenant);
        cached
    } else {
        debug!("Cache miss for tenant {}", request.tenant);
        let search_results = state
            .storage
            .search_with_tenant_isolation(
                &request.query,
                &request.tenant,
                &request.labels_filter,
                limit,
            )
            .await
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

        if let Err(e) = state
            .semantic_cache
            .put(
                &query_hash,
                &request.labels_filter,
                &request.tenant,
                limit,
                search_results.clone(),
                None,
            )
            .await
        {
            warn!("Failed to cache results: {}", e);
        }

        search_results
    };

    // Defense in depth against a mislabeled storage or cache result.
    // Documents with an unknown or extra label must never be returned on
    // the strength of a different, authorized label.
    let results: Vec<_> = results.into_iter().filter(|result| {
        !result.labels.is_empty()
            && result.labels.iter().all(|label| context.labels_filter.contains(label))
    }).take(limit).collect();

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
        result_hash: compute_result_commitment(&context.tenant, results)?,
        result_count: results.len(),
        query_time_ms,
        sign_alg: String::new(),
        sig: String::new(),
    };

    signer.sign_receipt(&receipt).await
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

    use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine as _};
    use ed25519_dalek::{Signer, SigningKey};
    use crate::storage::Document;

    fn signed_fixture_token(
        signer: &SigningKey,
        tenant: &str,
        subject: &str,
        labels: &[&str],
        capabilities: &[&str],
    ) -> String {
        let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        let header = serde_json::json!({
            "alg": "EdDSA", "typ": "JWT", "kid": "fixture-issuer-key",
        });
        let claims = serde_json::json!({
            "iss": "fixture-issuer", "aud": "pf-retrieval-gateway",
            "sub": subject, "tenant": tenant, "iat": now - 2,
            "nbf": now - 2, "exp": now + 120,
            "jti": Uuid::new_v4().to_string(),
            "allowed_labels": labels, "capabilities": capabilities,
        });
        let header = URL_SAFE_NO_PAD.encode(serde_json::to_vec(&header).unwrap());
        let claims = URL_SAFE_NO_PAD.encode(serde_json::to_vec(&claims).unwrap());
        let signing_input = format!("{header}.{claims}");
        let sig = signer.sign(signing_input.as_bytes());
        format!("{signing_input}.{}", URL_SAFE_NO_PAD.encode(sig.to_bytes()))
    }

    async fn seeded_gateway_state() -> (AppState, SigningKey) {
        // These are independently authored test fixtures, not service
        // responses retrospectively interpreted as an authorization oracle.
        let index = VectorIndex::new().await.unwrap();
        let query_embedding = VectorIndex::generate_query_embedding("fixture query");
        for (id, tenant, labels) in [
            ("a-public-one", "tenant-a", vec!["public"]),
            ("a-public-two", "tenant-a", vec!["public"]),
            ("a-private", "tenant-a", vec!["private"]),
            ("a-mixed", "tenant-a", vec!["public", "secret"]),
            ("b-public", "tenant-b", vec!["public"]),
        ] {
            index.add_document(Document {
                id: id.into(),
                content: format!("fixture content {id}"),
                tenant: tenant.into(),
                labels: labels.into_iter().map(str::to_string).collect(),
                metadata: HashMap::new(),
                embedding: query_embedding.clone(),
                created_at: 1,
                updated_at: 1,
            }).await.unwrap();
        }
        let policy: AbacPolicy = serde_yaml::from_str(include_str!("../abac.yaml")).unwrap();
        policy.validate_configuration().unwrap();
        let signer = SigningKey::from_bytes(&[18_u8; 32]);
        let verifier = TokenVerifier::from_keys(
            HashMap::from([("fixture-issuer-key".into(), signer.verifying_key())]),
            "fixture-issuer".into(),
        ).unwrap();
        (
            AppState {
                storage: Arc::new(index),
                abac_policy: Arc::new(policy),
                token_verifier: Arc::new(verifier),
                receipt_signer: Arc::new(ReceiptSigner::for_test()),
                receipt_cache: Arc::new(RwLock::new(HashMap::new())),
                semantic_cache: Arc::new(SemanticCache::with_config(cache::CacheConfig {
                    cleanup_interval_seconds: 0,
                    ..cache::CacheConfig::default()
                })),
            },
            signer,
        )
    }

    fn seeded_request(
        signer: &SigningKey,
        tenant: &str,
        labels: Vec<&str>,
        capabilities: &[&str],
    ) -> QueryRequest {
        let token = signed_fixture_token(
            signer, tenant, "user_fixture", &labels, capabilities,
        );
        QueryRequest {
            query: "fixture query".into(),
            tenant: tenant.into(),
            subject_id: "user_fixture".into(),
            capability_token: token,
            labels_filter: labels.into_iter().map(str::to_string).collect(),
            limit: Some(10),
        }
    }

    #[tokio::test]
    async fn seeded_handler_enforces_tenant_and_mixed_label_isolation() {
        let (state, key) = seeded_gateway_state().await;
        let a = handle_query(
            State(state.clone()),
            Json(seeded_request(&key, "tenant-a", vec!["public"], &[])),
        ).await.unwrap().0;
        let mut a_ids: Vec<_> = a.results.iter().map(|r| r.document_id.as_str()).collect();
        a_ids.sort_unstable();
        assert_eq!(a_ids, vec!["a-public-one", "a-public-two"]);
        assert!(a.results.iter().all(|r| {
            r.labels.len() == 1 && r.labels[0] == "public"
        }));
        assert_eq!(a.receipt.tenant, "tenant-a");
        assert_eq!(a.receipt.result_count, 2);

        let b = handle_query(
            State(state),
            Json(seeded_request(&key, "tenant-b", vec!["public"], &[])),
        ).await.unwrap().0;
        assert_eq!(b.results.len(), 1);
        assert_eq!(b.results[0].document_id, "b-public");
        assert_eq!(b.receipt.tenant, "tenant-b");
        assert_eq!(b.receipt.result_count, 1);
    }

    #[tokio::test]
    async fn seeded_handler_never_reuses_limit_one_cache_for_limit_ten() {
        let (state, key) = seeded_gateway_state().await;
        let mut request = seeded_request(&key, "tenant-a", vec!["public"], &[]);
        request.limit = Some(1);
        let one = handle_query(State(state.clone()), Json(request)).await.unwrap().0;
        assert_eq!(one.results.len(), 1);
        let ten = handle_query(
            State(state),
            Json(seeded_request(&key, "tenant-a", vec!["public"], &[])),
        ).await.unwrap().0;
        assert_eq!(ten.results.len(), 2);
    }

    #[tokio::test]
    async fn seeded_handler_rejects_unsigned_forged_and_forbidden_scopes() {
        let (state, signer) = seeded_gateway_state().await;
        let mut legacy = seeded_request(&signer, "tenant-a", vec!["public"], &[]);
        legacy.capability_token = "legacy-any-string".into();
        assert!(matches!(
            handle_query(State(state.clone()), Json(legacy)).await,
            Err(StatusCode::FORBIDDEN),
        ));

        let mut foreign = seeded_request(&signer, "tenant-a", vec!["public"], &[]);
        foreign.tenant = "tenant-b".into();
        assert!(matches!(
            handle_query(State(state.clone()), Json(foreign)).await,
            Err(StatusCode::FORBIDDEN),
        ));

        let mut forged = seeded_request(&signer, "tenant-a", vec!["public"], &[]);
        forged.capability_token = signed_fixture_token(
            &SigningKey::from_bytes(&[19_u8; 32]),
            "tenant-a", "user_fixture", &["public"], &[],
        );
        assert!(matches!(
            handle_query(State(state.clone()), Json(forged)).await,
            Err(StatusCode::FORBIDDEN),
        ));

        for labels in [vec!["private"], vec!["secret"]] {
            let invalid = seeded_request(&signer, "tenant-a", labels, &[]);
            assert!(matches!(
                handle_query(State(state.clone()), Json(invalid)).await,
                Err(StatusCode::FORBIDDEN),
            ));
        }

        let authorized_private = seeded_request(
            &signer, "tenant-a", vec!["private"], &["private_access"],
        );
        let private = handle_query(
            State(state), Json(authorized_private),
        ).await.unwrap().0;
        assert_eq!(private.results.len(), 1);
        assert_eq!(private.results[0].document_id, "a-private");
    }

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

        let hash = compute_result_commitment("tenant1", &results).unwrap();
        assert!(hash.starts_with("sha256-v2:"));
        assert_eq!(hash.len(), 74);
    }
}
