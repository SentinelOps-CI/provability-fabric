// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//! Emit pf-core.runtime_observation.v1 from a sidecar audit JSON line on stdin.

use sidecar_watcher::runtime_observation::{default_catalog_path, emit_from_audit_json};
use std::io::{self, Read};

fn main() -> anyhow::Result<()> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    let obs = emit_from_audit_json(input.trim(), default_catalog_path())?;
    println!("{}", serde_json::to_string_pretty(&obs)?);
    Ok(())
}
