// SPDX-License-Identifier: Apache-2.0

//! Request authorization under a separately provisioned Ed25519 issuer.
//!
//! The signature covers the exact request, including its deployment audience.
//! Freshness is evaluated for every request. No cache grants authority.
use super::{AttestationToken, AttestationValidation, KmsRequest};
use anyhow::{anyhow, bail, Context, Result};
use base64::{engine::general_purpose::STANDARD, Engine as _};
use crate::utc_timestamp::UtcTimestamp;
use ed25519_dalek::{Signature, VerifyingKey};
use std::collections::HashSet;

const DOMAIN: &[u8] = b"provability-fabric/kms-request-authority/v1\0";
const MAX_AGE_SECONDS: i64 = 60;

pub struct RequestAuthority {
    key: VerifyingKey,
    audience: String,
    policies: HashSet<String>,
    pods: HashSet<String>,
}

fn parse_allowlist(value: &str) -> Result<HashSet<String>> {
    let values: HashSet<String> = value.split(',').map(str::trim).map(str::to_owned).collect();
    if values.is_empty() || values.contains("") {
        bail!("empty authorization allowlist entry");
    }
    Ok(values)
}

impl RequestAuthority {
    pub fn from_env() -> Result<Self> {
        Self::from_config(
            &std::env::var("KMS_ATTESTATION_PUBLIC_KEY").context("missing issuer public key")?,
            &std::env::var("KMS_ATTESTATION_AUDIENCE").context("missing issuer audience")?,
            &std::env::var("KMS_ALLOWED_POLICY_HASHES").context("missing policy allowlist")?,
            &std::env::var("KMS_ALLOWED_POD_IDENTITIES").context("missing pod allowlist")?,
        )
    }

    fn from_config(key: &str, audience: &str, policies: &str, pods: &str) -> Result<Self> {
        let bytes: [u8; 32] = STANDARD.decode(key)?
            .try_into().map_err(|_| anyhow!("issuer public key must contain 32 bytes"))?;
        let key = VerifyingKey::from_bytes(&bytes)?;
        if key.is_weak() {
            bail!("weak issuer public key");
        }
        if audience.is_empty() || audience.trim() != audience {
            bail!("invalid deployment audience");
        }
        Ok(Self {
            key,
            audience: audience.to_owned(),
            policies: parse_allowlist(policies)?,
            pods: parse_allowlist(pods)?,
        })
    }

    pub fn validate(&self, request: &KmsRequest) -> AttestationValidation {
        self.validate_at(request, UtcTimestamp::now())
    }

    fn validate_at(&self, request: &KmsRequest, now: UtcTimestamp) -> AttestationValidation {
        let Some(token) = &request.attestation_token else {
            return denied("Attestation token required");
        };
        let token_fresh = token.timestamp.is_fresh_at(now, MAX_AGE_SECONDS);
        let policy_hash_match = self.policies.contains(&token.policy_hash);
        let pod_identity_valid = self.pods.contains(&token.pod_identity);

        let reason = if !token_fresh {
            "Attestation timestamp outside permitted window"
        } else if !policy_hash_match {
            "Policy hash not authorized"
        } else if !pod_identity_valid {
            "Pod identity not authorized"
        } else if token.token.is_empty() {
            "Attestation token identifier required"
        } else if !self.verify(request, token) {
            "Invalid request authorization signature"
        } else {
            return AttestationValidation {
                valid: true,
                reason: "Valid request authorization".to_string(),
                policy_hash_match,
                pod_identity_valid,
                token_fresh,
            };
        };
        AttestationValidation {
            valid: false,
            reason: reason.to_string(),
            policy_hash_match,
            pod_identity_valid,
            token_fresh,
        }
    }

    fn verify(&self, request: &KmsRequest, token: &AttestationToken) -> bool {
        let Ok(raw) = STANDARD.decode(&token.signature) else { return false; };
        let Ok(signature) = Signature::from_slice(&raw) else { return false; };
        let Ok(message) = signed_request_bytes(&self.audience, request, token) else {
            return false;
        };
        self.key.verify_strict(&message, &signature).is_ok()
    }
}

pub fn denied(reason: &str) -> AttestationValidation {
    AttestationValidation {
        valid: false,
        reason: reason.to_owned(),
        policy_hash_match: false,
        pod_identity_valid: false,
        token_fresh: false,
    }
}

fn append_field(out: &mut Vec<u8>, value: &[u8]) -> Result<()> {
    let len = u32::try_from(value.len()).context("signed field exceeds wire limit")?;
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(value);
    Ok(())
}

/// Versioned, unambiguous binary signature input. Variable-length fields use
/// a four-byte big-endian byte count; the optional data uses a presence byte.
fn signed_request_bytes(audience: &str, request: &KmsRequest, token: &AttestationToken) -> Result<Vec<u8>> {
    let mut out = DOMAIN.to_vec();
    for value in [
        audience, &token.token, &token.pod_identity, &token.policy_hash,
        &request.operation, &request.key_id,
    ] {
        append_field(&mut out, value.as_bytes())?;
    }
    out.extend_from_slice(&token.timestamp.timestamp().to_be_bytes());
    out.extend_from_slice(&token.timestamp.timestamp_subsec_nanos().to_be_bytes());
    match &request.data {
        None => out.push(0),
        Some(data) => {
            out.push(1);
            append_field(&mut out, data.as_bytes())?;
        }
    }
    Ok(out)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    // Deterministic fixture only. Never an operator key or deployed trust root.
    pub(crate) fn fixture_key() -> SigningKey { SigningKey::from_bytes(&[41; 32]) }

    pub(crate) fn fixture_authority() -> RequestAuthority {
        RequestAuthority::from_config(
            &STANDARD.encode(fixture_key().verifying_key().to_bytes()),
            "isolated-test", "policy-a,policy-b", "pod-a,pod-b",
        ).unwrap()
    }

    pub(crate) fn signed_fixture(now: UtcTimestamp) -> KmsRequest {
        let mut request = KmsRequest {
            operation: "sign".into(),
            key_id: "test-key".into(),
            data: Some("test message".into()),
            attestation_token: Some(AttestationToken {
                token: "fixture-id".into(), pod_identity: "pod-a".into(),
                policy_hash: "policy-a".into(), timestamp: now, signature: String::new(),
            }),
        };
        sign_fixture(&mut request, "isolated-test", &fixture_key());
        request
    }

    fn sign_fixture(request: &mut KmsRequest, audience: &str, key: &SigningKey) {
        let message = signed_request_bytes(audience, request, request.attestation_token.as_ref().unwrap()).unwrap();
        request.attestation_token.as_mut().unwrap().signature = STANDARD.encode(key.sign(&message).to_bytes());
    }

    #[test]
    fn exact_request_passes_and_every_mutation_fails() {
        let now = UtcTimestamp::from_timestamp(1_700_000_000, 250_000_000).unwrap();
        let authority = fixture_authority();
        assert!(authority.validate_at(&signed_fixture(now), now).valid);
        let changes: [fn(&mut KmsRequest); 9] = [
            |r| r.operation = "decrypt".into(),
            |r| r.key_id = "other-key".into(),
            |r| r.data = Some("different message".into()),
            |r| r.data = None,
            |r| r.attestation_token.as_mut().unwrap().token = "other-id".into(),
            |r| r.attestation_token.as_mut().unwrap().pod_identity = "pod-b".into(),
            |r| r.attestation_token.as_mut().unwrap().policy_hash = "policy-b".into(),
            |r| { let token = r.attestation_token.as_mut().unwrap(); token.timestamp = token.timestamp.checked_add_millis(-1).unwrap(); },
            |r| r.attestation_token.as_mut().unwrap().signature = "sig_placeholder".into(),
        ];
        for mutate in changes {
            let mut request = signed_fixture(now);
            mutate(&mut request);
            assert!(!authority.validate_at(&request, now).valid);
        }
        let mut missing = signed_fixture(now);
        missing.attestation_token = None;
        assert!(!authority.validate_at(&missing, now).valid);
    }

    #[test]
    fn freshness_is_checked_on_every_request_at_subsecond_boundaries() {
        let now = UtcTimestamp::from_timestamp(1_700_000_000, 250_000_000).unwrap();
        let authority = fixture_authority();
        for (offset, expected) in [(0, true), (-60_000, true), (-60_001, false), (1, false)] {
            let request = signed_fixture(now.checked_add_millis(offset).unwrap());
            assert_eq!(authority.validate_at(&request, now).valid, expected, "offset {offset}");
        }
        let request = signed_fixture(now);
        assert!(authority.validate_at(&request, now).valid);
        assert!(!authority.validate_at(&request, now.checked_add_millis(60_001).unwrap()).valid);
    }

    #[test]
    fn wrong_issuer_audience_and_disallowed_claims_fail_even_with_valid_signatures() {
        let now = UtcTimestamp::from_timestamp(1_700_000_000, 0).unwrap();
        let authority = fixture_authority();
        let mut request = signed_fixture(now);
        sign_fixture(&mut request, "other-deployment", &fixture_key());
        assert!(!authority.validate_at(&request, now).valid);
        sign_fixture(&mut request, "isolated-test", &SigningKey::from_bytes(&[42; 32]));
        assert!(!authority.validate_at(&request, now).valid);
        request.attestation_token.as_mut().unwrap().pod_identity = "unauthorized".into();
        sign_fixture(&mut request, "isolated-test", &fixture_key());
        assert!(!authority.validate_at(&request, now).valid);
        request.attestation_token.as_mut().unwrap().pod_identity = "pod-a".into();
        request.attestation_token.as_mut().unwrap().policy_hash = "unauthorized".into();
        sign_fixture(&mut request, "isolated-test", &fixture_key());
        assert!(!authority.validate_at(&request, now).valid);
    }

    #[test]
    fn exact_nanosecond_authorization_boundaries() {
        let now = UtcTimestamp::from_timestamp(1_700_000_000, 250_000_000).unwrap();
        let authority = fixture_authority();
        for (seconds, nanos, expected) in [
            (1_699_999_940, 249_999_999, false),
            (1_699_999_940, 250_000_000, true),
            (1_699_999_940, 250_000_001, true),
            (1_700_000_000, 250_000_000, true),
            (1_700_000_000, 250_000_001, false),
        ] {
            let request = signed_fixture(UtcTimestamp::from_timestamp(seconds, nanos).unwrap());
            assert_eq!(authority.validate_at(&request, now).valid, expected, "{seconds}.{nanos}");
        }
    }

    #[test]
    fn independently_generated_signature_vectors_preserve_wire_bytes() {
        // Generated independently using Python struct.pack and cryptography's
        // Ed25519 implementation. Deterministic test-only issuer; never deployed.
        let authority = fixture_authority();
        assert_eq!(STANDARD.encode(authority.key.to_bytes()), "+kg0FH9uaQw2k+/2EzYEZAPNiuKhTzGzxAc1hWkjlWU=");
        let cases = [
            ("2023-11-14T23:13:20.250+01:00", Some("test message"),
             "5d17888cb113df25e91db06d7b815148d539722190c37ab4d5e602e9e71b2972",
             "zcR8evZPWgDNC4a3Bjo36XYdl0AerIuYcUBpJCoFt85kn4P+XeZR/Rl3/yiFjEGFsXVHxnjSvGwRCgomsE25CA=="),
            ("1969-12-31T23:59:59.999999999Z", Some("test message"),
             "3d6d08d9af52abe785180009df79835973f41629737a655042a6ce4c6662d23b",
             "xY0uDcwfGzWqTO0XXnrE+clDJx2BDMB3GoyX6IXVoBWC3HC7YE/g0AkELYgcSScxZMGfRodGL3V20AUXj3jNCg=="),
            ("2023-11-14T22:13:20Z", None,
             "3df09ad7f26f290a1f9d08d0b3864edeee6f21868f87799585e8f0aec8e7ad77",
             "25/exVr0V9E7Jjazu5gdAtEHRVcjVbPZ3Uq7ex4TlPIuyYpsnCPznay6bAesrLQ8AZWWc6afxRU+dN8zWHbLCQ=="),
            ("2023-11-14T22:13:20Z", Some(""),
             "ac467899b5dcefb0b8d48e3f9c1f337cbb6d1742472ebde7005af4d66c5d9843",
             "lnJj3DpH/kTWsEuYN1+RWVVK8kmzJXZt7vjLqiCoUzybFk9p1Y8TR8YNtXt2b/8OZHg8QOWh1WeUgxkSAHcUCA=="),
        ];
        use sha2::{Digest, Sha256};
        for (wire, data, expected_hash, signature) in cases {
            let instant = UtcTimestamp::parse(wire).unwrap();
            let mut request = signed_fixture(instant);
            request.data = data.map(str::to_owned);
            request.attestation_token.as_mut().unwrap().signature = signature.into();
            let token = request.attestation_token.as_ref().unwrap();
            let message = signed_request_bytes("isolated-test", &request, token).unwrap();
            assert_eq!(hex::encode(Sha256::digest(message)), expected_hash);
            assert!(authority.validate_at(&request, instant).valid);
            // Confirm the new serializer preserves the signed instant.
            let decoded: KmsRequest = serde_json::from_str(&serde_json::to_string(&request).unwrap()).unwrap();
            assert!(authority.validate_at(&decoded, instant).valid);
        }
    }

    #[test]
    fn malformed_configuration_is_rejected() {
        let key = STANDARD.encode(fixture_key().verifying_key().to_bytes());
        assert!(RequestAuthority::from_config("bad", "a", "p", "pod").is_err());
        assert!(RequestAuthority::from_config(&key, "", "p", "pod").is_err());
        assert!(RequestAuthority::from_config(&key, "a", "p,", "pod").is_err());
        assert!(RequestAuthority::from_config(&key, "a", "p", "").is_err());
    }
}
