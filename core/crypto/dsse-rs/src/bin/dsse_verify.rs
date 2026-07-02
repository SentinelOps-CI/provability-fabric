// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use pf_dsse::{verify_envelope, Envelope, ACCESS_RECEIPT_TYPE};
use std::env;
use std::fs;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: dsse-verify <envelope.json> [expected-payload-type]");
        process::exit(2);
    }
    let data = fs::read_to_string(&args[1]).unwrap_or_else(|e| {
        eprintln!("read envelope: {e}");
        process::exit(1);
    });
    let envelope: Envelope = serde_json::from_str(&data).unwrap_or_else(|e| {
        eprintln!("parse envelope: {e}");
        process::exit(1);
    });
    let expected = args
        .get(2)
        .map(String::as_str)
        .unwrap_or(ACCESS_RECEIPT_TYPE);
    let result = verify_envelope(&envelope, expected);
    println!("{}", serde_json::to_string(&result).unwrap());
    if !result.valid {
        process::exit(1);
    }
}
