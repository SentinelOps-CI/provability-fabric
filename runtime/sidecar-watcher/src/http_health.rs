// SPDX-License-Identifier: Apache-2.0
// Minimal HTTP health endpoint for the runtime-sidecar.

use anyhow::Result;
use axum::http::StatusCode;
use axum::{routing::get, Json, Router};
use serde::Serialize;
use std::{net::SocketAddr, time::SystemTime};

#[derive(Serialize)]
struct Health {
    service: &'static str,
    status: &'static str,
    version: &'static str,
    timestamp: String,
}

async fn health_handler() -> Json<Health> {
    let ts = humantime::format_rfc3339(SystemTime::now()).to_string();
    Json(Health {
        service: "runtime-sidecar",
        status: "healthy",
        version: env!("CARGO_PKG_VERSION"),
        timestamp: ts,
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
