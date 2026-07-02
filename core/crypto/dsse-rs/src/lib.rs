// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

pub mod verify;

pub use verify::{
    enforce_dsse, trust_root_configured, verify_access_receipt, verify_envelope, AccessReceiptPayload,
    Envelope, VerifyResult, ACCESS_RECEIPT_TYPE, ENV_ENFORCE_DSSE, ENV_JWKS_URL, ENV_TRUST_ROOT_PEM,
};
