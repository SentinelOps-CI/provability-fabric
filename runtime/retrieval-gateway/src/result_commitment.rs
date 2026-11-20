//! Versioned, deterministic commitment to the exact ordered retrieval response.
//!
//! The signed receipt's result_hash contains the prefix and digest. Historical
//! 64-character SHA-256 hashes are legacy v1 evidence and are never promoted
//! to this stronger v2 interpretation.

use anyhow::{bail, Result};
use sha2::{Digest, Sha256};

use crate::SearchResult;

const DOMAIN: &[u8] = b"provability-fabric/retrieval-result/v2\0";
pub const V2_PREFIX: &str = "sha256-v2:";

/// Recognize the two explicitly different wire-format commitment versions.
pub fn valid_result_hash(value: &str) -> bool {
    if let Some(digest) = value.strip_prefix(V2_PREFIX) {
        digest.len() == 64 && digest.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    } else {
        value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
    }
}

fn write_count(hash: &mut Sha256, number: usize) -> Result<()> {
    let count: u64 = number.try_into()?;
    hash.update(count.to_be_bytes());
    Ok(())
}

fn write_utf8(hash: &mut Sha256, value: &str) -> Result<()> {
    write_count(hash, value.len())?;
    hash.update(value.as_bytes());
    Ok(())
}

/// Commitment preimage specification:
///
/// 1. DOMAIN bytes, including trailing NUL.
/// 2. Tenant as u64-BE UTF-8 byte length followed by its bytes.
/// 3. Ordered result count as u64-BE.
/// 4. For each result in returned order: length-prefixed document ID, content,
///    and content hash; finite IEEE-754 binary64 score in network byte order
///    (both zero signs map to positive zero); ordered label count and strings;
///    metadata count and key/value strings in ascending UTF-8 key-byte order.
///
/// Every variable-length field has an unambiguous u64 length. The commitment
/// binds the response fields and the request tenant, not the validity of the
/// returned document, classification decision, or signed receipt trust root.
pub fn compute_result_commitment(tenant: &str, results: &[SearchResult]) -> Result<String> {
    if tenant.is_empty() {
        bail!("result commitment tenant must be nonempty");
    }

    let mut hash = Sha256::new();
    hash.update(DOMAIN);
    write_utf8(&mut hash, tenant)?;
    write_count(&mut hash, results.len())?;

    for result in results {
        if !result.score.is_finite() {
            bail!("retrieval result contains a nonfinite score");
        }

        write_utf8(&mut hash, &result.document_id)?;
        write_utf8(&mut hash, &result.content)?;
        write_utf8(&mut hash, &result.content_hash)?;

        let score = if result.score == 0.0 { 0.0 } else { result.score };
        hash.update(score.to_bits().to_be_bytes());

        write_count(&mut hash, result.labels.len())?;
        for label in &result.labels {
            write_utf8(&mut hash, label)?;
        }

        let mut entries: Vec<_> = result.metadata.iter().collect();
        entries.sort_unstable_by(|(left, _), (right, _)| left.as_bytes().cmp(right.as_bytes()));
        write_count(&mut hash, entries.len())?;
        for (key, value) in entries {
            write_utf8(&mut hash, key)?;
            write_utf8(&mut hash, value)?;
        }
    }

    Ok(format!("{}{:x}", V2_PREFIX, hash.finalize()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use std::collections::HashMap;

    #[derive(Deserialize)]
    struct ReferenceVector {
        name: String,
        tenant: String,
        results: Vec<SearchResult>,
        expected_result_hash: String,
    }

    #[derive(Deserialize)]
    struct Fixture {
        schema_version: u32,
        encoding: String,
        vectors: Vec<ReferenceVector>,
    }

    fn vectors() -> Vec<ReferenceVector> {
        let fixture: Fixture = serde_json::from_str(include_str!(
            "../../../tests/fixtures/crypto/retrieval_result_commitment_v2.json"
        ))
        .expect("valid independent cross-language fixture");
        assert_eq!(fixture.schema_version, 2);
        assert_eq!(fixture.encoding, "pf-retrieval-result-v2-binary");
        fixture.vectors
    }

    #[test]
    fn independent_reference_vectors_match() {
        let list = vectors();
        assert!(list.len() >= 5);
        for item in list {
            assert_eq!(
                compute_result_commitment(&item.tenant, &item.results).unwrap(),
                item.expected_result_hash,
                "vector {} differs",
                item.name
            );
        }
    }

    #[test]
    fn previously_ambiguous_field_boundaries_differ() {
        let list = vectors();
        let a = &list[1];
        let b = &list[2];
        assert_eq!(
            [a.results[0].document_id.as_str(), a.results[0].content.as_str()].concat(),
            [b.results[0].document_id.as_str(), b.results[0].content.as_str()].concat()
        );
        assert_ne!(a.expected_result_hash, b.expected_result_hash);
    }

    #[test]
    fn tampering_with_any_response_field_changes_commitment() {
        let list = vectors();
        let item = &list[1];
        let original = compute_result_commitment(&item.tenant, &item.results).unwrap();

        let mut altered = item.results.clone();
        altered[0].document_id.push('x');
        assert_ne!(original, compute_result_commitment(&item.tenant, &altered).unwrap());

        let mut altered = item.results.clone();
        altered[0].content.push('x');
        assert_ne!(original, compute_result_commitment(&item.tenant, &altered).unwrap());

        let mut altered = item.results.clone();
        altered[0].content_hash.push('x');
        assert_ne!(original, compute_result_commitment(&item.tenant, &altered).unwrap());

        let mut altered = item.results.clone();
        altered[0].score += 0.125;
        assert_ne!(original, compute_result_commitment(&item.tenant, &altered).unwrap());

        let mut altered = item.results.clone();
        altered[0].labels.push("classified".to_string());
        assert_ne!(original, compute_result_commitment(&item.tenant, &altered).unwrap());

        let mut altered = item.results.clone();
        altered[0].metadata.insert("alpha".to_string(), "changed".to_string());
        assert_ne!(original, compute_result_commitment(&item.tenant, &altered).unwrap());

        assert_ne!(original, compute_result_commitment("different-tenant", &item.results).unwrap());

        let mut ordered = list[4].results.clone();
        let before = compute_result_commitment(&list[4].tenant, &ordered).unwrap();
        ordered.reverse();
        assert_ne!(before, compute_result_commitment(&list[4].tenant, &ordered).unwrap());
    }

    #[test]
    fn unordered_metadata_map_iteration_is_canonical() {
        let vector = &vectors()[1];
        let mut same = vector.results.clone();
        let mut reordered = HashMap::new();
        for (key, value) in same[0].metadata.iter().collect::<Vec<_>>().into_iter().rev() {
            reordered.insert(key.clone(), value.clone());
        }
        same[0].metadata = reordered;
        assert_eq!(
            compute_result_commitment(&vector.tenant, &same).unwrap(),
            vector.expected_result_hash
        );
    }

    #[test]
    fn signed_zero_normalized_and_nonfinite_scores_rejected() {
        let vector = &vectors()[3];
        let mut same = vector.results.clone();
        same[0].score = -0.0;
        assert_eq!(
            compute_result_commitment(&vector.tenant, &same).unwrap(),
            vector.expected_result_hash
        );
        for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            same[0].score = invalid;
            assert!(compute_result_commitment(&vector.tenant, &same).is_err());
        }
        assert!(compute_result_commitment("", &[]).is_err());
    }

    #[test]
    fn v1_and_v2_hash_formats_have_disjoint_semantics() {
        assert!(valid_result_hash(&"a".repeat(64)));
        assert!(valid_result_hash(&"A".repeat(64))); // historical hex encoding
        assert!(valid_result_hash(&format!("{}{}", V2_PREFIX, "a".repeat(64))));
        assert!(!valid_result_hash(&format!("{}{}", V2_PREFIX, "A".repeat(64))));
        assert!(!valid_result_hash(&format!("{}{}", V2_PREFIX, "g".repeat(64))));
        assert!(!valid_result_hash(&"g".repeat(64)));
        assert!(!valid_result_hash(&"a".repeat(65)));
        assert!(!valid_result_hash("sha256-v3:invalid"));
    }
}
