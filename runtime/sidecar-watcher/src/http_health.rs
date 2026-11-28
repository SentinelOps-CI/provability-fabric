// SPDX-License-Identifier: Apache-2.0
// Minimal HTTP health endpoint for the runtime-sidecar.

use anyhow::Result;
use axum::http::StatusCode;
use axum::{routing::get, Json, Router};
use serde::Serialize;
use std::net::SocketAddr;
use time::{format_description::well_known::Rfc3339, OffsetDateTime};

#[derive(Serialize)]
struct Health {
    service: &'static str,
    status: &'static str,
    version: &'static str,
    timestamp: String,
}

fn health_at(now: OffsetDateTime) -> Result<Health, time::error::Format> {
    Ok(Health {
        service: "runtime-sidecar",
        status: "healthy",
        version: env!("CARGO_PKG_VERSION"),
        timestamp: now.format(&Rfc3339)?,
    })
}

async fn health_handler() -> Result<Json<Health>, StatusCode> {
    health_at(OffsetDateTime::now_utc()).map(Json).map_err(|error| {
        tracing::error!(%error, "Could not format health timestamp");
        StatusCode::INTERNAL_SERVER_ERROR
    })
}

async fn ping_handler() -> (StatusCode, &'static str) {
    (StatusCode::OK, "ok")
}

pub async fn serve_http(addr: SocketAddr) -> Result<()> {
    let app = Router::new()
        .route("/api/v1/health", get(health_handler))
        .route("/health", get(ping_handler)); // << plain text

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn health_timestamp_is_rfc3339_utc() {
        let health = health_at(OffsetDateTime::UNIX_EPOCH).expect("valid timestamp");
        assert_eq!(health.service, "runtime-sidecar");
        assert_eq!(health.status, "healthy");
        assert_eq!(health.version, env!("CARGO_PKG_VERSION"));
        assert_eq!(health.timestamp, "1970-01-01T00:00:00Z");
    }

    #[test]
    fn health_timestamp_preserves_subsecond_precision() {
        let instant = OffsetDateTime::from_unix_timestamp_nanos(123_456_789)
            .expect("valid timestamp");
        let health = health_at(instant).expect("valid timestamp");
        assert_eq!(health.timestamp, "1970-01-01T00:00:00.123456789Z");
    }

    #[tokio::test]
    async fn health_handler_reports_current_utc_timestamp() {
        let Json(health) = health_handler().await.expect("healthy response");
        let parsed = chrono::DateTime::parse_from_rfc3339(&health.timestamp)
            .expect("RFC3339 timestamp");
        assert_eq!(health.status, "healthy");
        assert_eq!(parsed.offset().local_minus_utc(), 0);
    }
}
