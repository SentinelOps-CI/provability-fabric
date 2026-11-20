//! Verified Ed25519 JWTs for retrieval capability requests.
//!
//! The verifier accepts only locally configured trusted public keys. It never
//! uses a URL, embedded JWK, or caller-controlled issuer as a trust root.
//! Bearer tokens remain replayable until expiry; this module does not assert
//! one-time-use semantics or revocation of already-issued credentials.

use anyhow::{bail, Context, Result};
use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine as _};
use ed25519_dalek::{Signature, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::time::{SystemTime, UNIX_EPOCH};

const AUDIENCE: &str = "pf-retrieval-gateway";
const MAX_TOKEN_BYTES: usize = 8192;
const MAX_LIFETIME_SECONDS: u64 = 3600;
const MAX_FUTURE_IAT_SECONDS: u64 = 30;

/// Bound claims from a successfully authenticated token.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CapabilityClaims {
    pub iss: String,
    pub aud: String,
    pub sub: String,
    pub tenant: String,
    pub iat: u64,
    pub nbf: u64,
    pub exp: u64,
    pub jti: String,
    pub allowed_labels: Vec<String>,
    pub capabilities: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProtectedHeader {
    alg: String,
    typ: String,
    kid: String,
}

/// An immutable set of trusted Ed25519 public keys and the expected issuer.
pub struct TokenVerifier {
    keys: HashMap<String, VerifyingKey>,
    issuer: String,
}

impl TokenVerifier {
    /// Construct from deployment-managed *public* keys.
    ///
    /// RETRIEVAL_JWT_VERIFY_KEYS_JSON is a JSON mapping of key IDs to base64url
    /// (unpadded) 32-byte Ed25519 public keys. RETRIEVAL_JWT_ISSUER is the
    /// exact expected issuer. Absence of either aborts service startup.
    pub fn from_env() -> Result<Self> {
        let json = std::env::var("RETRIEVAL_JWT_VERIFY_KEYS_JSON")
            .context("RETRIEVAL_JWT_VERIFY_KEYS_JSON is mandatory")?;
        let issuer = std::env::var("RETRIEVAL_JWT_ISSUER")
            .context("RETRIEVAL_JWT_ISSUER is mandatory")?;
        let encoded: HashMap<String, String> =
            serde_json::from_str(&json).context("Invalid verifier key map")?;
        if encoded.is_empty() {
            bail!("At least one trusted verifier key is mandatory");
        }
        let mut keys = HashMap::with_capacity(encoded.len());
        for (kid, key_b64) in encoded {
            if kid.trim().is_empty() {
                bail!("Verifier key ID must be nonempty");
            }
            let raw = URL_SAFE_NO_PAD.decode(key_b64.as_bytes())
                .context("Invalid base64url verifier key")?;
            let bytes: [u8; 32] = raw.try_into()
                .map_err(|_| anyhow::anyhow!("Verifier keys must be 32 bytes"))?;
            keys.insert(
                kid,
                VerifyingKey::from_bytes(&bytes).context("Invalid Ed25519 public key")?,
            );
        }
        Self::from_keys(keys, issuer)
    }

    pub(crate) fn from_keys(keys: HashMap<String, VerifyingKey>, issuer: String) -> Result<Self> {
        if keys.is_empty() || issuer.trim().is_empty() {
            bail!("Trusted keys and nonempty issuer are mandatory");
        }
        Ok(Self { keys, issuer })
    }

    /// Authenticate a compact EdDSA JWT and verify all request-bound claims.
    pub fn verify(
        &self,
        token: &str,
        expected_tenant: &str,
        expected_subject: &str,
    ) -> Result<CapabilityClaims> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .context("System clock predates Unix epoch")?
            .as_secs();
        self.verify_at(token, expected_tenant, expected_subject, now)
    }

    fn verify_at(
        &self,
        token: &str,
        expected_tenant: &str,
        expected_subject: &str,
        now: u64,
    ) -> Result<CapabilityClaims> {
        if token.is_empty() || token.len() > MAX_TOKEN_BYTES
            || expected_tenant.trim().is_empty() || expected_subject.trim().is_empty()
        {
            bail!("Empty, oversized, or unbound capability token");
        }
        let mut parts = token.split('.');
        let protected = parts.next().unwrap_or_default();
        let payload = parts.next().unwrap_or_default();
        let signature = parts.next().unwrap_or_default();
        if protected.is_empty() || payload.is_empty() || signature.is_empty()
            || parts.next().is_some()
        {
            bail!("Invalid compact JWT structure");
        }
        let header_raw = URL_SAFE_NO_PAD.decode(protected)
            .context("Invalid protected header encoding")?;
        let header: ProtectedHeader = serde_json::from_slice(&header_raw)
            .context("Invalid protected header")?;
        if header.alg != "EdDSA" || header.typ != "JWT" {
            bail!("Unsupported JWT algorithm or type");
        }
        let key = self.keys.get(&header.kid).context("Unknown verifier key ID")?;
        let sig_bytes = URL_SAFE_NO_PAD.decode(signature)
            .context("Invalid signature encoding")?;
        let sig = Signature::from_slice(&sig_bytes).context("Invalid Ed25519 signature size")?;
        let signing_input = format!("{protected}.{payload}");
        key.verify_strict(signing_input.as_bytes(), &sig)
            .context("Invalid JWT signature")?;

        // Parse claims only once their bytes have been authenticated.
        let claim_bytes = URL_SAFE_NO_PAD.decode(payload)
            .context("Invalid claims encoding")?;
        let claims: CapabilityClaims = serde_json::from_slice(&claim_bytes)
            .context("Invalid signed claims")?;
        if claims.iss != self.issuer || claims.aud != AUDIENCE
            || claims.tenant != expected_tenant || claims.sub != expected_subject
            || claims.jti.trim().is_empty()
        {
            bail!("Invalid issuer, audience, identity binding, or token ID");
        }
        if claims.iat > now.saturating_add(MAX_FUTURE_IAT_SECONDS)
            || claims.nbf > now || claims.nbf > claims.exp
            || claims.exp <= now || claims.exp <= claims.iat
            || claims.exp.saturating_sub(claims.iat) > MAX_LIFETIME_SECONDS
        {
            bail!("Token is expired, premature, or exceeds lifetime policy");
        }
        if claims.allowed_labels.is_empty()
            || claims.allowed_labels.iter().any(|s| s.trim().is_empty() || s == "*")
            || claims.capabilities.iter().any(|s| s.trim().is_empty() || s == "*")
        {
            bail!("Invalid label or capability scope");
        }
        let labels: HashSet<_> = claims.allowed_labels.iter().collect();
        let capabilities: HashSet<_> = claims.capabilities.iter().collect();
        if labels.len() != claims.allowed_labels.len()
            || capabilities.len() != claims.capabilities.len()
        {
            bail!("Duplicate label or capability scopes");
        }
        Ok(claims)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn fixture(issuer: &str) -> (SigningKey, TokenVerifier) {
        let signer = key(7);
        let verifier = TokenVerifier::from_keys(
            HashMap::from([("key-a".into(), signer.verifying_key())]),
            issuer.into(),
        ).unwrap();
        (signer, verifier)
    }

    fn claims(now: u64) -> CapabilityClaims {
        CapabilityClaims {
            iss: "test-issuer".into(),
            aud: AUDIENCE.into(),
            sub: "alice".into(),
            tenant: "tenant-a".into(),
            iat: now - 60,
            nbf: now - 60,
            exp: now + 60,
            jti: "nonce-1".into(),
            allowed_labels: vec!["public".into()],
            capabilities: vec![],
        }
    }

    fn signed(signer: &SigningKey, kid: &str, c: &CapabilityClaims) -> String {
        let header = ProtectedHeader {
            alg: "EdDSA".into(), typ: "JWT".into(), kid: kid.into(),
        };
        sign_with_header(signer, &header, c)
    }

    fn sign_with_header(
        signer: &SigningKey, header: &ProtectedHeader, c: &CapabilityClaims,
    ) -> String {
        let header = URL_SAFE_NO_PAD.encode(serde_json::to_vec(header).unwrap());
        let claims = URL_SAFE_NO_PAD.encode(serde_json::to_vec(c).unwrap());
        let message = format!("{header}.{claims}");
        let signature = signer.sign(message.as_bytes());
        format!("{message}.{}", URL_SAFE_NO_PAD.encode(signature.to_bytes()))
    }

    #[test]
    fn authentic_token_has_bound_scopes() {
        let now = 1_900_000_000;
        let (signer, verifier) = fixture("test-issuer");
        let c = verifier.verify_at(
            &signed(&signer, "key-a", &claims(now)), "tenant-a", "alice", now,
        ).unwrap();
        assert_eq!(c.allowed_labels, ["public"]);
        assert_eq!(c.tenant, "tenant-a");
    }

    #[test]
    fn reject_forged_or_tampered_token() {
        let now = 1_900_000_000;
        let (signer, verifier) = fixture("test-issuer");
        let mut token = signed(&signer, "key-a", &claims(now));
        token.pop();
        token.push('A');
        assert!(verifier.verify_at(&token, "tenant-a", "alice", now).is_err());
        assert!(verifier.verify_at(
            &signed(&key(9), "key-a", &claims(now)), "tenant-a", "alice", now,
        ).is_err());
    }

    #[test]
    fn reject_untrusted_key_and_algorithm() {
        let now = 1_900_000_000;
        let (signer, verifier) = fixture("test-issuer");
        assert!(verifier.verify_at(
            &signed(&signer, "other", &claims(now)), "tenant-a", "alice", now,
        ).is_err());
        let header = ProtectedHeader { alg: "none".into(), typ: "JWT".into(), kid: "key-a".into() };
        assert!(verifier.verify_at(
            &sign_with_header(&signer, &header, &claims(now)), "tenant-a", "alice", now,
        ).is_err());
    }

    #[test]
    fn reject_wrong_subject_tenant_audience_or_issuer() {
        let now = 1_900_000_000;
        let (signer, verifier) = fixture("test-issuer");
        let token = signed(&signer, "key-a", &claims(now));
        assert!(verifier.verify_at(&token, "tenant-b", "alice", now).is_err());
        assert!(verifier.verify_at(&token, "tenant-a", "bob", now).is_err());
        let mut c = claims(now);
        c.iss = "unknown".into();
        assert!(verifier.verify_at(
            &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
        ).is_err());
        c = claims(now);
        c.aud = "some-other-service".into();
        assert!(verifier.verify_at(
            &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
        ).is_err());
    }

    #[test]
    fn reject_expiration_future_issuance_and_overlong_lifetime() {
        let now = 1_900_000_000;
        let (signer, verifier) = fixture("test-issuer");
        let mut c = claims(now);
        c.exp = now;
        assert!(verifier.verify_at(
            &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
        ).is_err());
        c = claims(now);
        c.iat = now + 31;
        c.nbf = now;
        c.exp = now + 100;
        assert!(verifier.verify_at(
            &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
        ).is_err());
        c = claims(now);
        c.nbf = now + 1;
        assert!(verifier.verify_at(
            &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
        ).is_err());
        c = claims(now);
        c.exp = c.iat + 3601;
        assert!(verifier.verify_at(
            &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
        ).is_err());
    }

    #[test]
    fn reject_empty_duplicate_and_wildcard_scopes() {
        let now = 1_900_000_000;
        let (signer, verifier) = fixture("test-issuer");
        for labels in [vec![], vec!["*".into()], vec!["public".into(), "public".into()]] {
            let mut c = claims(now);
            c.allowed_labels = labels;
            assert!(verifier.verify_at(
                &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
            ).is_err());
        }
        let mut c = claims(now);
        c.capabilities = vec!["private_access".into(), "private_access".into()];
        assert!(verifier.verify_at(
            &signed(&signer, "key-a", &c), "tenant-a", "alice", now,
        ).is_err());
    }

    #[test]
    fn reject_bad_structure_and_absent_key_configuration() {
        let now = 1_900_000_000;
        let (_, verifier) = fixture("test-issuer");
        let oversized = "x".repeat(MAX_TOKEN_BYTES + 1);
        for token in ["", "bad", "a.b.c.d", "a.b", oversized.as_str()] {
            assert!(verifier.verify_at(token, "tenant-a", "alice", now).is_err());
        }
        assert!(TokenVerifier::from_keys(HashMap::new(), "test-issuer".into()).is_err());
        assert!(TokenVerifier::from_keys(HashMap::from([(
            "a".into(), key(4).verifying_key(),
        )]), "".into()).is_err());
    }

    #[test]
    fn rotation_accepts_both_explicitly_trusted_keys() {
        let now = 1_900_000_000;
        let first = key(3);
        let second = key(4);
        let verifier = TokenVerifier::from_keys(
            HashMap::from([
                ("old".into(), first.verifying_key()),
                ("new".into(), second.verifying_key()),
            ]),
            "test-issuer".into(),
        ).unwrap();
        assert!(verifier.verify_at(
            &signed(&first, "old", &claims(now)), "tenant-a", "alice", now,
        ).is_ok());
        assert!(verifier.verify_at(
            &signed(&second, "new", &claims(now)), "tenant-a", "alice", now,
        ).is_ok());
        assert!(verifier.verify_at(
            &signed(&key(5), "new", &claims(now)), "tenant-a", "alice", now,
        ).is_err());
    }
}
