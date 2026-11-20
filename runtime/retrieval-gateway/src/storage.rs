use anyhow::{Context, Result};
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use sqlx::Row;
use std::collections::HashMap;
use tokio::sync::RwLock;

fn content_hash_for(content: &str) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(content.as_bytes());
    hex::encode(hasher.finalize())
}

/// Storage adapter trait for vector index backends
#[async_trait]
pub trait StorageAdapter: Send + Sync {
    /// Search with tenant isolation and label filtering
    async fn search_with_tenant_isolation(
        &self,
        query: &str,
        tenant: &str,
        labels_filter: &[String],
        limit: usize,
    ) -> Result<Vec<crate::SearchResult>>;

    /// Get document by ID with tenant check
    async fn get_document(&self, doc_id: &str, tenant: &str) -> Result<Option<Document>>;

    /// Check if tenant has access to shard
    async fn validate_tenant_shard_access(&self, tenant: &str, shard: &str) -> Result<bool>;

    /// Get shard statistics
    async fn get_shard_stats(&self, tenant: &str) -> Result<ShardStats>;
}

/// Document structure in the index
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Document {
    pub id: String,
    pub content: String,
    pub tenant: String,
    pub labels: Vec<String>,
    pub metadata: HashMap<String, String>,
    pub embedding: Vec<f32>,
    pub created_at: u64,
    pub updated_at: u64,
}

/// Shard statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ShardStats {
    pub shard_id: String,
    pub tenant: String,
    pub document_count: usize,
    pub total_size_bytes: u64,
    pub last_updated: u64,
}

/// In-memory vector index implementation
pub struct VectorIndex {
    documents: RwLock<HashMap<String, Document>>,
    tenant_shards: RwLock<HashMap<String, String>>,
    embeddings: RwLock<HashMap<String, Vec<f32>>>,
}

impl VectorIndex {
    /// Create new vector index
    pub async fn new() -> Result<Self> {
        Ok(Self {
            documents: RwLock::new(HashMap::new()),
            tenant_shards: RwLock::new(HashMap::new()),
            embeddings: RwLock::new(HashMap::new()),
        })
    }

    /// Add document to index
    pub async fn add_document(&self, document: Document) -> Result<()> {
        let mut docs = self.documents.write().await;
        let mut shards = self.tenant_shards.write().await;
        let mut embeddings = self.embeddings.write().await;

        // Assign tenant to shard
        let shard_id = format!("shard_{}", document.tenant);
        shards.insert(document.tenant.clone(), shard_id);

        // Store embedding
        embeddings.insert(document.id.clone(), document.embedding.clone());

        // Store document
        docs.insert(document.id.clone(), document);

        Ok(())
    }

    /// Compute cosine similarity between embeddings
    fn cosine_similarity(a: &[f32], b: &[f32]) -> f32 {
        if a.len() != b.len() {
            return 0.0;
        }

        let dot_product: f32 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
        let norm_a: f32 = a.iter().map(|x| x * x).sum::<f32>().sqrt();
        let norm_b: f32 = b.iter().map(|x| x * x).sum::<f32>().sqrt();

        if norm_a == 0.0 || norm_b == 0.0 {
            0.0
        } else {
            dot_product / (norm_a * norm_b)
        }
    }

    /// Deterministic 128-dimensional synthetic query vector for integration
    /// testing. This is a hash-derived placeholder, not a semantic embedding.
    pub fn generate_query_embedding(query: &str) -> Vec<f32> {
        use sha2::{Digest, Sha256};

        let mut values = Vec::with_capacity(128);
        for counter in 0u8..4 {
            let mut hasher = Sha256::new();
            hasher.update(b"pf-retrieval/synthetic-embedding/v1\0");
            hasher.update((query.len() as u64).to_be_bytes());
            hasher.update(query.as_bytes());
            hasher.update([counter]);
            values.extend(
                hasher.finalize()
                    .iter()
                    .map(|&byte| (f32::from(byte) - 128.0) / 128.0),
            );
        }
        debug_assert_eq!(values.len(), 128);
        values
    }
}

#[async_trait]
impl StorageAdapter for VectorIndex {
    async fn search_with_tenant_isolation(
        &self,
        query: &str,
        tenant: &str,
        labels_filter: &[String],
        limit: usize,
    ) -> Result<Vec<crate::SearchResult>> {
        let docs = self.documents.read().await;
        let embeddings = self.embeddings.read().await;

        // Generate query embedding
        let query_embedding = Self::generate_query_embedding(query);

        // Filter documents by tenant and labels
        let mut candidates: Vec<_> = docs
            .values()
            .filter(|doc| {
                // Tenant isolation check
                if doc.tenant != tenant {
                    return false;
                }

                // Every document classification must be authorized.
                // An empty grant permits only documents with no labels.
                doc.labels.iter().all(|label| labels_filter.contains(label))
            })
            .collect();

        // Calculate similarity scores and sort
        candidates.sort_by(|a, b| {
            let score_a = if let Some(embedding_a) = embeddings.get(&a.id) {
                Self::cosine_similarity(&query_embedding, embedding_a)
            } else {
                0.0
            };

            let score_b = if let Some(embedding_b) = embeddings.get(&b.id) {
                Self::cosine_similarity(&query_embedding, embedding_b)
            } else {
                0.0
            };

            score_b.partial_cmp(&score_a).unwrap_or(std::cmp::Ordering::Equal)
        });

        // Take top results and convert to SearchResult
        let results = candidates
            .into_iter()
            .take(limit)
            .map(|doc| {
                let score = if let Some(embedding) = embeddings.get(&doc.id) {
                    Self::cosine_similarity(&query_embedding, embedding)
                } else {
                    0.0
                };

                crate::SearchResult {
                    document_id: doc.id.clone(),
                    content: doc.content.clone(),
                    content_hash: content_hash_for(&doc.content),
                    score: score as f64,
                    metadata: doc.metadata.clone(),
                    labels: doc.labels.clone(),
                }
            })
            .collect();

        Ok(results)
    }

    async fn get_document(&self, doc_id: &str, tenant: &str) -> Result<Option<Document>> {
        let docs = self.documents.read().await;
        
        match docs.get(doc_id) {
            Some(doc) if doc.tenant == tenant => Ok(Some(doc.clone())),
            Some(_) => {
                // Document exists but belongs to different tenant
                tracing::warn!("Cross-tenant document access attempt: {} -> {}", tenant, doc_id);
                Ok(None)
            }
            None => Ok(None),
        }
    }

    async fn validate_tenant_shard_access(&self, tenant: &str, shard: &str) -> Result<bool> {
        let shards = self.tenant_shards.read().await;
        
        match shards.get(tenant) {
            Some(tenant_shard) => Ok(tenant_shard == shard),
            None => Ok(false),
        }
    }

    async fn get_shard_stats(&self, tenant: &str) -> Result<ShardStats> {
        let docs = self.documents.read().await;
        let shards = self.tenant_shards.read().await;

        let shard_id = shards
            .get(tenant)
            .cloned()
            .unwrap_or_else(|| format!("shard_{}", tenant));

        let tenant_docs: Vec<_> = docs
            .values()
            .filter(|doc| doc.tenant == tenant)
            .collect();

        let document_count = tenant_docs.len();
        let total_size_bytes = tenant_docs
            .iter()
            .map(|doc| doc.content.len() as u64)
            .sum();

        let last_updated = tenant_docs
            .iter()
            .map(|doc| doc.updated_at)
            .max()
            .unwrap_or(0);

        Ok(ShardStats {
            shard_id,
            tenant: tenant.to_string(),
            document_count,
            total_size_bytes,
            last_updated,
        })
    }
}

/// PostgreSQL vector storage adapter
pub struct PostgresVectorAdapter {
    pool: sqlx::PgPool,
}

impl PostgresVectorAdapter {
    /// Create new PostgreSQL adapter
    pub async fn new(database_url: &str) -> Result<Self> {
        let pool = sqlx::PgPool::connect(database_url)
            .await
            .context("Failed to connect to PostgreSQL")?;

        Ok(Self { pool })
    }

    /// Run privileged, idempotent migrations; runtime roles have only SELECT.
    pub async fn init_schema(&self) -> Result<()> {
        let mut tx = self.pool.begin().await.context("begin schema transaction")?;
        sqlx::query("CREATE EXTENSION IF NOT EXISTS vector")
            .execute(&mut *tx).await.context("enable vector extension")?;
        sqlx::query(
            r#"CREATE TABLE IF NOT EXISTS documents (
                id TEXT PRIMARY KEY,
                tenant TEXT NOT NULL,
                content TEXT NOT NULL,
                labels TEXT[] NOT NULL,
                metadata JSONB NOT NULL,
                embedding vector(128),
                created_at BIGINT NOT NULL,
                updated_at BIGINT NOT NULL
            )"#,
        ).execute(&mut *tx).await.context("create documents table")?;

        for ddl in [
            "CREATE INDEX IF NOT EXISTS idx_documents_tenant ON documents (tenant)",
            "CREATE INDEX IF NOT EXISTS idx_documents_labels ON documents USING GIN (labels)",
            "CREATE INDEX IF NOT EXISTS idx_documents_embedding ON documents USING ivfflat (embedding vector_cosine_ops)",
            "ALTER TABLE documents ENABLE ROW LEVEL SECURITY",
            "ALTER TABLE documents FORCE ROW LEVEL SECURITY",
        ] {
            sqlx::query(ddl).execute(&mut *tx).await.context("initialize document indices and RLS")?;
        }

        // Restrictive RLS blocks cross-tenant access even if another permissive
        // policy exists. A matching permissive policy admits the current tenant.
        sqlx::query(
            r#"DO $policies$
            BEGIN
                IF NOT EXISTS (
                    SELECT 1 FROM pg_policies
                    WHERE schemaname = current_schema() AND tablename = 'documents'
                      AND policyname = 'pf_tenant_allow'
                ) THEN
                    CREATE POLICY pf_tenant_allow ON documents
                        AS PERMISSIVE FOR ALL
                        USING (tenant = current_setting('app.current_tenant', true))
                        WITH CHECK (tenant = current_setting('app.current_tenant', true));
                END IF;
                IF NOT EXISTS (
                    SELECT 1 FROM pg_policies
                    WHERE schemaname = current_schema() AND tablename = 'documents'
                      AND policyname = 'pf_tenant_guard'
                ) THEN
                    CREATE POLICY pf_tenant_guard ON documents
                        AS RESTRICTIVE FOR ALL
                        USING (tenant = current_setting('app.current_tenant', true))
                        WITH CHECK (tenant = current_setting('app.current_tenant', true));
                END IF;
            END
            $policies$"#,
        ).execute(&mut *tx).await.context("install restrictive tenant RLS")?;
        tx.commit().await.context("commit schema transaction")?;
        Ok(())
    }

    /// Set tenant context within the same acquired transaction as the query.
    async fn tenant_transaction(&self, tenant: &str) -> Result<sqlx::Transaction<'_, sqlx::Postgres>> {
        anyhow::ensure!(!tenant.is_empty(), "tenant must be nonempty");
        let mut tx = self.pool.begin().await.context("begin tenant transaction")?;
        sqlx::query("SELECT set_config('app.current_tenant', $1, true)")
            .bind(tenant)
            .execute(&mut *tx).await.context("set local tenant context")?;
        Ok(tx)
    }

}

#[async_trait]
/// Encode an internally derived, finite vector as pgvector text input.
/// It is supplied via a bound SQL parameter, never concatenated into SQL.
fn query_vector_literal(query: &str) -> String {
    let embedding = VectorIndex::generate_query_embedding(query);
    debug_assert_eq!(embedding.len(), 128);
    format!(
        "[{}]",
        embedding.iter().map(|value| value.to_string()).collect::<Vec<_>>().join(",")
    )
}

/// Decode the vector text returned by PostgreSQL into the documented shape.
fn decode_vector_text(value: Option<String>) -> Result<Vec<f32>> {
    let Some(text) = value else { return Ok(Vec::new()) };
    let inner = text.strip_prefix('[')
        .and_then(|x| x.strip_suffix(']'))
        .context("invalid pgvector text encoding")?;
    let values: Vec<f32> = inner
        .split(',')
        .map(|x| x.parse::<f32>().context("invalid pgvector component"))
        .collect::<Result<_>>()?;
    anyhow::ensure!(values.len() == 128, "unexpected vector dimensions");
    anyhow::ensure!(values.iter().all(|x| x.is_finite()), "nonfinite stored vector");
    Ok(values)
}

impl StorageAdapter for PostgresVectorAdapter {
    async fn search_with_tenant_isolation(
        &self,
        query: &str,
        tenant: &str,
        labels_filter: &[String],
        limit: usize,
    ) -> Result<Vec<crate::SearchResult>> {
        let mut tx = self.tenant_transaction(tenant).await?;
        let vector = query_vector_literal(query);
        let limit = i64::try_from(limit).context("result limit too large")?;

        // Full label containment rejects multi-label records if even one
        // classification is outside the request's grant. Empty grants only
        // admit documents with no labels.
        let rows = sqlx::query(
            r#"SELECT id, content, labels, metadata,
                      (embedding <=> ($1::text)::vector)::double precision AS distance
               FROM documents
               WHERE tenant = $2 AND labels <@ $3::text[]
                 AND embedding IS NOT NULL
               ORDER BY embedding <=> ($1::text)::vector, id
               LIMIT $4"#,
        )
        .bind(vector)
        .bind(tenant)
        .bind(labels_filter)
        .bind(limit)
        .fetch_all(&mut *tx)
        .await.context("fetch tenant-scoped search results")?;
        tx.commit().await.context("finish tenant-scoped vector search")?;

        rows.into_iter().map(|row| {
            let distance: f64 = row.try_get("distance")?;
            anyhow::ensure!(distance.is_finite(), "nonfinite vector distance");
            let content: String = row.try_get("content")?;
            Ok(crate::SearchResult {
                document_id: row.try_get("id")?,
                content_hash: content_hash_for(&content),
                content,
                score: 1.0 - distance,
                metadata: serde_json::from_value(row.try_get("metadata")?)
                    .context("invalid document metadata")?,
                labels: row.try_get("labels")?,
            })
        }).collect()
    }

    async fn get_document(&self, doc_id: &str, tenant: &str) -> Result<Option<Document>> {
        let mut tx = self.tenant_transaction(tenant).await?;
        let row = sqlx::query(
            r#"SELECT id, tenant, content, labels, metadata,
                      embedding::text AS embedding_text, created_at, updated_at
               FROM documents WHERE id = $1 AND tenant = $2"#,
        )
        .bind(doc_id).bind(tenant)
        .fetch_optional(&mut *tx).await.context("fetch tenant-scoped document")?;
        tx.commit().await.context("finish tenant-scoped document fetch")?;

        row.map(|row| {
            let created_at: i64 = row.try_get("created_at")?;
            let updated_at: i64 = row.try_get("updated_at")?;
            Ok(Document {
                id: row.try_get("id")?,
                content: row.try_get("content")?,
                tenant: row.try_get("tenant")?,
                labels: row.try_get("labels")?,
                metadata: serde_json::from_value(row.try_get("metadata")?)
                    .context("invalid document metadata")?,
                embedding: decode_vector_text(row.try_get("embedding_text")?)?,
                created_at: u64::try_from(created_at).context("negative creation timestamp")?,
                updated_at: u64::try_from(updated_at).context("negative update timestamp")?,
            })
        }).transpose()
    }

    async fn validate_tenant_shard_access(&self, tenant: &str, shard: &str) -> Result<bool> {
        // A logical shard name is not an independent tenant credential.
        Ok(!tenant.is_empty() && shard == format!("shard_{}", tenant))
    }

    async fn get_shard_stats(&self, tenant: &str) -> Result<ShardStats> {
        let mut tx = self.tenant_transaction(tenant).await?;
        let row = sqlx::query(
            r#"SELECT COUNT(*) AS document_count,
                      COALESCE(SUM(OCTET_LENGTH(content)), 0)::bigint AS total_size_bytes,
                      COALESCE(MAX(updated_at), 0)::bigint AS last_updated
               FROM documents WHERE tenant = $1"#,
        )
        .bind(tenant)
        .fetch_one(&mut *tx).await.context("fetch tenant-scoped statistics")?;
        tx.commit().await.context("finish tenant-scoped statistics")?;

        let count: i64 = row.try_get("document_count")?;
        let bytes: i64 = row.try_get("total_size_bytes")?;
        let updated: i64 = row.try_get("last_updated")?;
        Ok(ShardStats {
            shard_id: format!("shard_{}", tenant),
            tenant: tenant.to_string(),
            document_count: usize::try_from(count).context("negative document count")?,
            total_size_bytes: u64::try_from(bytes).context("negative content size")?,
            last_updated: u64::try_from(updated).context("negative update time")?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_vector_index_tenant_isolation() {
        let index = VectorIndex::new().await.unwrap();

        // Add documents for different tenants
        let doc1 = Document {
            id: "doc1".to_string(),
            content: "content for tenant1".to_string(),
            tenant: "tenant1".to_string(),
            labels: vec!["public".to_string()],
            metadata: HashMap::new(),
            embedding: vec![0.1; 128],
            created_at: 1000,
            updated_at: 1000,
        };

        let doc2 = Document {
            id: "doc2".to_string(),
            content: "content for tenant2".to_string(),
            tenant: "tenant2".to_string(),
            labels: vec!["public".to_string()],
            metadata: HashMap::new(),
            embedding: vec![0.2; 128],
            created_at: 1000,
            updated_at: 1000,
        };

        index.add_document(doc1).await.unwrap();
        index.add_document(doc2).await.unwrap();

        // Search should only return documents for the specified tenant
        let results = index
            .search_with_tenant_isolation("test query", "tenant1", &["public".to_string()], 10)
            .await
            .unwrap();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].document_id, "doc1");
    }

    #[tokio::test]
    async fn test_label_filtering() {
        let index = VectorIndex::new().await.unwrap();

        let doc1 = Document {
            id: "doc1".to_string(),
            content: "public content".to_string(),
            tenant: "tenant1".to_string(),
            labels: vec!["public".to_string()],
            metadata: HashMap::new(),
            embedding: vec![0.1; 128],
            created_at: 1000,
            updated_at: 1000,
        };

        let doc2 = Document {
            id: "doc2".to_string(),
            content: "private content".to_string(),
            tenant: "tenant1".to_string(),
            labels: vec!["private".to_string()],
            metadata: HashMap::new(),
            embedding: vec![0.2; 128],
            created_at: 1000,
            updated_at: 1000,
        };

        index.add_document(doc1).await.unwrap();
        index.add_document(doc2).await.unwrap();

        // Search with label filter should only return matching documents
        let results = index
            .search_with_tenant_isolation("test query", "tenant1", &["public".to_string()], 10)
            .await
            .unwrap();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].document_id, "doc1");
    }

    #[test]
    fn test_cosine_similarity() {
        let a = vec![1.0, 0.0, 0.0];
        let b = vec![1.0, 0.0, 0.0];
        let c = vec![0.0, 1.0, 0.0];

        assert!((VectorIndex::cosine_similarity(&a, &b) - 1.0).abs() < 1e-6);
        assert!((VectorIndex::cosine_similarity(&a, &c) - 0.0).abs() < 1e-6);
    }
}

#[cfg(test)]
mod postgres_rls_tests {
    use super::*;
    use sqlx::postgres::PgPoolOptions;

    /// Requires the disposable pgvector PostgreSQL service in CI.
    #[tokio::test]
    #[ignore = "requires PF_POSTGRES_TEST_ADMIN_URL and PF_POSTGRES_TEST_APP_URL"]
    async fn postgres_rls_tenant_and_label_isolation() {
        let admin_url = std::env::var("PF_POSTGRES_TEST_ADMIN_URL")
            .expect("disposable PostgreSQL administrator URL is required");
        let app_url = std::env::var("PF_POSTGRES_TEST_APP_URL")
            .expect("disposable PostgreSQL nonprivileged role URL is required");

        let admin = PostgresVectorAdapter::new(&admin_url).await.unwrap();
        admin.init_schema().await.unwrap();
        admin.init_schema().await.expect("idempotent schema migration");

        // This role and its test-only password exist solely in the disposable
        // CI database. No production role, credential, or permission is changed.
        sqlx::query(
            r#"DO $role$
            BEGIN
                IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = 'pf_retrieval_ci') THEN
                    CREATE ROLE pf_retrieval_ci LOGIN PASSWORD 'testpass';
                END IF;
            END
            $role$"#,
        )
        .execute(&admin.pool).await.unwrap();
        sqlx::query("GRANT USAGE ON SCHEMA public TO pf_retrieval_ci")
            .execute(&admin.pool).await.unwrap();
        sqlx::query("GRANT SELECT ON documents TO pf_retrieval_ci")
            .execute(&admin.pool).await.unwrap();
        sqlx::query("TRUNCATE TABLE documents")
            .execute(&admin.pool).await.unwrap();

        let vector = query_vector_literal("integration-query");
        let fixtures = vec![
            ("a-public", "tenant-a", vec!["public".to_string()], "first content"),
            ("a-classified", "tenant-a", vec!["public".to_string(), "secret".to_string()], "classified"),
            ("a-open", "tenant-a", Vec::new(), "public unlabeled"),
            ("b-public", "tenant-b", vec!["public".to_string()], "other tenant public"),
            ("b-secret", "tenant-b", vec!["secret".to_string()], "other tenant private"),
        ];
        for (id, tenant, labels, content) in fixtures {
            sqlx::query(
                r#"INSERT INTO documents (
                    id, tenant, labels, content, metadata,
                    embedding, created_at, updated_at
                ) VALUES ($1, $2, $3::text[], $4, $5::jsonb,
                          ($6::text)::vector, 1000, 1001)"#,
            )
            .bind(id).bind(tenant).bind(labels).bind(content)
            .bind(serde_json::json!({"origin": "disposable-test"}))
            .bind(&vector)
            .execute(&admin.pool).await.unwrap();
        }

        let pool = PgPoolOptions::new().max_connections(2)
            .connect(&app_url).await.expect("connect nonprivileged application role");
        let storage = PostgresVectorAdapter { pool };

        // The test role must never bypass database RLS.
        let role: (bool, bool) = sqlx::query_as(
            "SELECT rolbypassrls, rolsuper FROM pg_roles WHERE rolname = current_user",
        ).fetch_one(&storage.pool).await.unwrap();
        assert_eq!(role, (false, false));

        // No transaction-local tenant context: all documents are hidden.
        let direct: (i64,) = sqlx::query_as("SELECT COUNT(*) FROM documents")
            .fetch_one(&storage.pool).await.unwrap();
        assert_eq!(direct.0, 0);

        let public = vec!["public".to_string()];
        let full = vec!["public".to_string(), "secret".to_string()];
        let results = storage.search_with_tenant_isolation(
            "integration-query", "tenant-a", &public, 10,
        ).await.unwrap();
        let ids: Vec<_> = results.iter().map(|r| r.document_id.as_str()).collect();
        assert_eq!(ids.len(), 2);
        assert!(ids.contains(&"a-public"));
        assert!(ids.contains(&"a-open"));
        assert!(!ids.contains(&"a-classified"));

        let full_results = storage.search_with_tenant_isolation(
            "integration-query", "tenant-a", &full, 10,
        ).await.unwrap();
        assert_eq!(full_results.len(), 3);
        let empty_grant = storage.search_with_tenant_isolation(
            "integration-query", "tenant-a", &[], 10,
        ).await.unwrap();
        assert_eq!(empty_grant.len(), 1);
        assert_eq!(empty_grant[0].document_id, "a-open");

        // User-originated label strings are bound, never interpolated into SQL.
        let hostile = vec!["public' OR TRUE --".to_string()];
        let injection = storage.search_with_tenant_isolation(
            "integration-query", "tenant-a", &hostile, 10,
        ).await.unwrap();
        assert_eq!(injection.len(), 1);
        assert_eq!(injection[0].document_id, "a-open");

        let other = storage.search_with_tenant_isolation(
            "integration-query", "tenant-b", &public, 10,
        ).await.unwrap();
        assert_eq!(other.len(), 1);
        assert_eq!(other[0].document_id, "b-public");

        assert!(storage.get_document("b-public", "tenant-a").await.unwrap().is_none());
        let doc = storage.get_document("a-public", "tenant-a").await.unwrap().unwrap();
        assert_eq!(doc.embedding.len(), 128);
        assert_eq!(doc.metadata["origin"], "disposable-test");

        let stats_a = storage.get_shard_stats("tenant-a").await.unwrap();
        assert_eq!(stats_a.document_count, 3);
        assert_eq!(stats_a.last_updated, 1001);
        let stats_b = storage.get_shard_stats("tenant-b").await.unwrap();
        assert_eq!(stats_b.document_count, 2);
        let empty = storage.get_shard_stats("missing").await.unwrap();
        assert_eq!(empty.document_count, 0);
        assert_eq!(empty.total_size_bytes, 0);
        assert_eq!(empty.last_updated, 0);
        assert!(storage.get_shard_stats("").await.is_err());

        // Exercise pooled connection reuse and concurrent alternating tenants.
        for _ in 0..12 {
            let (a, b) = tokio::join!(
                storage.get_shard_stats("tenant-a"),
                storage.get_shard_stats("tenant-b")
            );
            assert_eq!(a.unwrap().document_count, 3);
            assert_eq!(b.unwrap().document_count, 2);
        }

        // Tenant GUC settings from prior transactions must not persist on pool
        // connections, even with the same two physical sessions being reused.
        let direct_again: (i64,) = sqlx::query_as("SELECT COUNT(*) FROM documents")
            .fetch_one(&storage.pool).await.unwrap();
        assert_eq!(direct_again.0, 0);

        // Explicit RLS guard must exist and must be restrictive.
        let policy: (bool,) = sqlx::query_as(
            "SELECT polpermissive FROM pg_policy WHERE polname = 'pf_tenant_guard'",
        ).fetch_one(&admin.pool).await.unwrap();
        assert!(!policy.0);
    }

    #[test]
    fn deterministic_embedding_has_expected_dimensions() {
        let embedding = VectorIndex::generate_query_embedding("integration-query");
        assert_eq!(embedding.len(), 128);
        assert!(embedding.iter().all(|v| v.is_finite()));
        assert_ne!(embedding, VectorIndex::generate_query_embedding("different"));
        assert_eq!(embedding, VectorIndex::generate_query_embedding("integration-query"));
        assert_eq!(decode_vector_text(Some(query_vector_literal("integration-query"))).unwrap().len(), 128);
        assert!(decode_vector_text(Some("[1,2]".to_string())).is_err());
    }

    #[tokio::test]
    async fn memory_index_enforces_complete_label_containment() {
        let index = VectorIndex::new().await.unwrap();
        for (id, labels) in [
            ("both", vec!["public".to_string(), "secret".to_string()]),
            ("open", Vec::new()),
        ] {
            index.add_document(Document {
                id: id.to_string(), content: "test".to_string(),
                tenant: "tenant-a".to_string(), labels, metadata: HashMap::new(),
                embedding: vec![0.1; 128], created_at: 1, updated_at: 2,
            }).await.unwrap();
        }
        let granted = vec!["public".to_string()];
        let visible = index.search_with_tenant_isolation("q", "tenant-a", &granted, 10)
            .await.unwrap();
        assert_eq!(visible.len(), 1);
        assert_eq!(visible[0].document_id, "open");
        let all = vec!["public".to_string(), "secret".to_string()];
        assert_eq!(index.search_with_tenant_isolation("q", "tenant-a", &all, 10).await.unwrap().len(), 2);
        assert_eq!(index.search_with_tenant_isolation("q", "tenant-a", &[], 10).await.unwrap().len(), 1);
    }
}
