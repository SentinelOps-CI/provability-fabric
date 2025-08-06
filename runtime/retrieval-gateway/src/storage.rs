use anyhow::{Context, Result};
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::RwLock;

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

    /// Generate query embedding (simplified)
    fn generate_query_embedding(&self, query: &str) -> Vec<f32> {
        // Simplified embedding generation based on query hash
        let hash = {
            use sha2::{Digest, Sha256};
            let mut hasher = Sha256::new();
            hasher.update(query.as_bytes());
            hasher.finalize()
        };

        // Convert hash to normalized embedding vector
        hash.iter()
            .take(128) // Use first 128 bytes
            .map(|&byte| (byte as f32 - 128.0) / 128.0) // Normalize to [-1, 1]
            .collect()
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
        let query_embedding = self.generate_query_embedding(query);

        // Filter documents by tenant and labels
        let mut candidates: Vec<_> = docs
            .values()
            .filter(|doc| {
                // Tenant isolation check
                if doc.tenant != tenant {
                    return false;
                }

                // Label filtering
                if !labels_filter.is_empty() {
                    let has_matching_label = labels_filter
                        .iter()
                        .any(|filter_label| doc.labels.contains(filter_label));
                    if !has_matching_label {
                        return false;
                    }
                }

                true
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
                    score,
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

    /// Initialize database schema
    pub async fn init_schema(&self) -> Result<()> {
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS documents (
                id TEXT PRIMARY KEY,
                tenant TEXT NOT NULL,
                content TEXT NOT NULL,
                labels TEXT[] NOT NULL,
                metadata JSONB NOT NULL,
                embedding vector(128),
                created_at BIGINT NOT NULL,
                updated_at BIGINT NOT NULL
            );
            
            CREATE INDEX IF NOT EXISTS idx_documents_tenant ON documents(tenant);
            CREATE INDEX IF NOT EXISTS idx_documents_labels ON documents USING GIN(labels);
            CREATE INDEX IF NOT EXISTS idx_documents_embedding ON documents USING ivfflat (embedding vector_cosine_ops);
            
            -- Row Level Security for tenant isolation
            ALTER TABLE documents ENABLE ROW LEVEL SECURITY;
            
            CREATE POLICY IF NOT EXISTS tenant_isolation_policy ON documents
                FOR ALL USING (tenant = current_setting('app.current_tenant', true));
            "#,
        )
        .execute(&self.pool)
        .await
        .context("Failed to initialize schema")?;

        Ok(())
    }
}

#[async_trait]
impl StorageAdapter for PostgresVectorAdapter {
    async fn search_with_tenant_isolation(
        &self,
        query: &str,
        tenant: &str,
        labels_filter: &[String],
        limit: usize,
    ) -> Result<Vec<crate::SearchResult>> {
        // Set tenant context for RLS
        sqlx::query("SET app.current_tenant = $1")
            .bind(tenant)
            .execute(&self.pool)
            .await
            .context("Failed to set tenant context")?;

        // Generate query embedding (simplified)
        let query_embedding = VectorIndex::new().await?.generate_query_embedding(query);

        // Build SQL query with label filtering
        let labels_condition = if labels_filter.is_empty() {
            "TRUE".to_string()
        } else {
            format!("labels && ARRAY[{}]", 
                labels_filter.iter()
                    .map(|l| format!("'{}'", l.replace("'", "''")))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };

        let sql = format!(
            r#"
            SELECT id, content, labels, metadata, 
                   (embedding <=> $1::vector) as distance
            FROM documents 
            WHERE {} 
            ORDER BY embedding <=> $1::vector 
            LIMIT $2
            "#,
            labels_condition
        );

        let rows = sqlx::query(&sql)
            .bind(query_embedding.as_slice())
            .bind(limit as i64)
            .fetch_all(&self.pool)
            .await
            .context("Failed to execute search query")?;

        let results = rows
            .into_iter()
            .map(|row| {
                let distance: f32 = row.get("distance");
                let score = 1.0 - distance; // Convert distance to similarity

                crate::SearchResult {
                    document_id: row.get("id"),
                    content: row.get("content"),
                    score,
                    metadata: serde_json::from_value(row.get("metadata")).unwrap_or_default(),
                    labels: row.get("labels"),
                }
            })
            .collect();

        Ok(results)
    }

    async fn get_document(&self, doc_id: &str, tenant: &str) -> Result<Option<Document>> {
        // Set tenant context for RLS
        sqlx::query("SET app.current_tenant = $1")
            .bind(tenant)
            .execute(&self.pool)
            .await
            .context("Failed to set tenant context")?;

        let row = sqlx::query(
            "SELECT * FROM documents WHERE id = $1"
        )
        .bind(doc_id)
        .fetch_optional(&self.pool)
        .await
        .context("Failed to fetch document")?;

        match row {
            Some(row) => {
                let doc = Document {
                    id: row.get("id"),
                    content: row.get("content"),
                    tenant: row.get("tenant"),
                    labels: row.get("labels"),
                    metadata: serde_json::from_value(row.get("metadata")).unwrap_or_default(),
                    embedding: vec![], // Would decode from vector type
                    created_at: row.get("created_at"),
                    updated_at: row.get("updated_at"),
                };
                Ok(Some(doc))
            }
            None => Ok(None),
        }
    }

    async fn validate_tenant_shard_access(&self, tenant: &str, shard: &str) -> Result<bool> {
        // For PostgreSQL, shard is determined by tenant
        let expected_shard = format!("shard_{}", tenant);
        Ok(shard == expected_shard)
    }

    async fn get_shard_stats(&self, tenant: &str) -> Result<ShardStats> {
        // Set tenant context for RLS
        sqlx::query("SET app.current_tenant = $1")
            .bind(tenant)
            .execute(&self.pool)
            .await
            .context("Failed to set tenant context")?;

        let row = sqlx::query(
            r#"
            SELECT 
                COUNT(*) as document_count,
                SUM(LENGTH(content)) as total_size_bytes,
                MAX(updated_at) as last_updated
            FROM documents
            "#
        )
        .fetch_one(&self.pool)
        .await
        .context("Failed to get shard stats")?;

        Ok(ShardStats {
            shard_id: format!("shard_{}", tenant),
            tenant: tenant.to_string(),
            document_count: row.get::<i64, _>("document_count") as usize,
            total_size_bytes: row.get::<i64, _>("total_size_bytes") as u64,
            last_updated: row.get::<i64, _>("last_updated") as u64,
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
            .search_with_tenant_isolation("test query", "tenant1", &["public"], 10)
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
            .search_with_tenant_isolation("test query", "tenant1", &["public"], 10)
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