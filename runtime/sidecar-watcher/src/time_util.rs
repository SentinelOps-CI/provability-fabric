// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//! Fail-closed time and serialization helpers (F16 unwrap burn-down).

use serde::Serialize;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Unix seconds since epoch; 0 if system clock is unavailable.
pub fn unix_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Unix milliseconds since epoch; 0 if system clock is unavailable.
pub fn unix_millis() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

/// Unix nanoseconds since epoch; 0 if system clock is unavailable.
pub fn unix_nanos() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0)
}

/// Serialize to JSON string; empty object on failure.
pub fn json_string<T: Serialize>(value: &T) -> String {
    serde_json::to_string(value).unwrap_or_else(|_| "{}".to_string())
}

/// Serialize to JSON bytes; empty slice on failure.
pub fn json_vec<T: Serialize>(value: &T) -> Vec<u8> {
    serde_json::to_vec(value).unwrap_or_default()
}

/// Duration since epoch for comparisons; zero if clock unavailable.
pub fn duration_since_epoch() -> Duration {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or(Duration::ZERO)
}
