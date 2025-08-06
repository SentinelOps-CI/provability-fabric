use axum::{
    extract::Path,
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use chrono::{DateTime, Utc};
use redis::AsyncCommands;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, warn};

mod attest;

#[derive(Debug, Serialize, Deserialize)]
pub struct Heartbeat {
    pub capsule_hash: String,
    pub timestamp: i64,
    pub metrics: HeartbeatMetrics,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HeartbeatMetrics {
    pub total_actions: u64,
    pub violations: u64,
    pub assumption_violations: u64,
    pub running_spend: f64,
    pub budget_limit: f64,
    pub spam_score_limit: f64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TerminateFrame {
    pub capsule_hash: String,
    pub timestamp: i64,
    pub reason: String,
}

#[derive(Debug, Serialize)]
pub struct LivenessResponse {
    pub alive: bool,
    pub last_heartbeat: Option<DateTime<Utc>>,
    pub age_seconds: Option<i64>,
}

struct AppState {
    redis_client: redis::Client,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Initialize tracing
    tracing_subscriber::fmt::init();

    // Connect to Redis
    let redis_url = std::env::var("REDIS_URL").unwrap_or_else(|_| "redis://localhost:6379".to_string());
    let redis_client = redis::Client::open(redis_url)?;
    
    // Test Redis connection
    let mut conn = redis_client.get_async_connection().await?;
    conn.ping().await?;
    info!("Connected to Redis");

    let state = Arc::new(AppState { redis_client });

    // Build application with routes
    let app = Router::new()
        .route("/health", get(health))
        .route("/heartbeat", post(handle_heartbeat))
        .route("/terminate", post(handle_terminate))
        .route("/liveness/:hash", get(handle_liveness))
        .with_state(state);

    let addr = std::net::SocketAddr::from(([0, 0, 0, 0], 8080));
    info!("Attestor service listening on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}

async fn health() -> StatusCode {
    StatusCode::OK
}

async fn handle_heartbeat(
    axum::extract::State(state): axum::extract::State<Arc<AppState>>,
    Json(heartbeat): Json<Heartbeat>,
) -> StatusCode {
    let mut conn = match state.redis_client.get_async_connection().await {
        Ok(conn) => conn,
        Err(e) => {
            warn!("Failed to get Redis connection: {}", e);
            return StatusCode::INTERNAL_SERVER_ERROR;
        }
    };

    // Store heartbeat in Redis with TTL
    let key = format!("heartbeat:{}", heartbeat.capsule_hash);
    let value = serde_json::to_string(&heartbeat).unwrap();
    
    if let Err(e) = conn.set_ex(&key, value, 30).await {
        warn!("Failed to store heartbeat: {}", e);
        return StatusCode::INTERNAL_SERVER_ERROR;
    }

    info!("Received heartbeat from {}", heartbeat.capsule_hash);
    StatusCode::OK
}

async fn handle_terminate(
    axum::extract::State(state): axum::extract::State<Arc<AppState>>,
    Json(terminate): Json<TerminateFrame>,
) -> StatusCode {
    let mut conn = match state.redis_client.get_async_connection().await {
        Ok(conn) => conn,
        Err(e) => {
            warn!("Failed to get Redis connection: {}", e);
            return StatusCode::INTERNAL_SERVER_ERROR;
        }
    };

    // Store termination event
    let key = format!("terminate:{}", terminate.capsule_hash);
    let value = serde_json::to_string(&terminate).unwrap();
    
    if let Err(e) = conn.set_ex(&key, value, 3600).await {
        warn!("Failed to store termination: {}", e);
        return StatusCode::INTERNAL_SERVER_ERROR;
    }

    info!("Received termination from {}: {}", terminate.capsule_hash, terminate.reason);
    StatusCode::OK
}

async fn handle_liveness(
    axum::extract::State(state): axum::extract::State<Arc<AppState>>,
    Path(hash): Path<String>,
) -> Json<LivenessResponse> {
    let mut conn = match state.redis_client.get_async_connection().await {
        Ok(conn) => conn,
        Err(e) => {
            warn!("Failed to get Redis connection: {}", e);
            return Json(LivenessResponse {
                alive: false,
                last_heartbeat: None,
                age_seconds: None,
            });
        }
    };

    let key = format!("heartbeat:{}", hash);
    let heartbeat_data: Option<String> = conn.get(&key).await.unwrap_or(None);

    match heartbeat_data {
        Some(data) => {
            if let Ok(heartbeat) = serde_json::from_str::<Heartbeat>(&data) {
                let now = Utc::now();
                let heartbeat_time = DateTime::from_timestamp(heartbeat.timestamp, 0).unwrap_or(now);
                let age_seconds = (now - heartbeat_time).num_seconds();
                
                // Consider alive if heartbeat is less than 15 seconds old
                let alive = age_seconds < 15;
                
                Json(LivenessResponse {
                    alive,
                    last_heartbeat: Some(heartbeat_time),
                    age_seconds: Some(age_seconds),
                })
            } else {
                Json(LivenessResponse {
                    alive: false,
                    last_heartbeat: None,
                    age_seconds: None,
                })
            }
        }
        None => Json(LivenessResponse {
            alive: false,
            last_heartbeat: None,
            age_seconds: None,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::http::StatusCode;
    use axum_test::TestServer;

    #[tokio::test]
    async fn test_health_endpoint() {
        let state = Arc::new(AppState {
            redis_client: redis::Client::open("redis://localhost:6379").unwrap(),
        });

        let app = Router::new()
            .route("/health", get(health))
            .with_state(state);

        let server = TestServer::new(app).unwrap();
        let response = server.get("/health").await;
        assert_eq!(response.status_code(), StatusCode::OK);
    }
}