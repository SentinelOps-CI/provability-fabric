//! Utility functions for the Provability Fabric Core SDK

use crate::error::{Error, Result};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Generate a unique identifier
pub fn generate_id() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or(Duration::from_secs(0))
        .as_nanos();
    format!("id_{}", now)
}

/// Generate a unique identifier with prefix
pub fn generate_id_with_prefix(prefix: &str) -> String {
    format!("{}_{}", prefix, generate_id())
}

/// Generate a hash from content
pub fn generate_hash(content: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(content);
    format!("sha256:{}", hex::encode(hasher.finalize()))
}

/// Generate a hash from string content
pub fn generate_string_hash(content: &str) -> String {
    generate_hash(content.as_bytes())
}

/// Validate email format
pub fn validate_email(email: &str) -> bool {
    use regex::Regex;
    lazy_static::lazy_static! {
        static ref EMAIL_REGEX: Regex = Regex::new(
            r"^[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$"
        ).unwrap();
    }
    EMAIL_REGEX.is_match(email)
}

/// Validate URL format
pub fn validate_url(url: &str) -> bool {
    use regex::Regex;
    lazy_static::lazy_static! {
        static ref URL_REGEX: Regex = Regex::new(
            r"^https?://[^\s/$.?#].[^\s]*$"
        ).unwrap();
    }
    URL_REGEX.is_match(url)
}

/// Validate UUID format
pub fn validate_uuid(uuid: &str) -> bool {
    use regex::Regex;
    lazy_static::lazy_static! {
        static ref UUID_REGEX: Regex = Regex::new(
            r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$"
        ).unwrap();
    }
    UUID_REGEX.is_match(uuid.to_lowercase())
}

/// Validate hash format
pub fn validate_hash(hash: &str) -> bool {
    use regex::Regex;
    lazy_static::lazy_static! {
        static ref HASH_REGEX: Regex = Regex::new(
            r"^(sha256|sha512|blake3):[a-f0-9]{64,128}$"
        ).unwrap();
    }
    HASH_REGEX.is_match(hash.to_lowercase())
}

/// Validate timestamp format
pub fn validate_timestamp(timestamp: &str) -> bool {
    use chrono::{DateTime, Utc};
    DateTime::parse_from_rfc3339(timestamp).is_ok() || 
    DateTime::parse_from_rfc2822(timestamp).is_ok() ||
    timestamp.parse::<i64>().is_ok()
}

/// Parse duration string (e.g., "1h", "30m", "45s")
pub fn parse_duration(duration_str: &str) -> Result<Duration> {
    let mut total_seconds = 0u64;
    let mut current_number = String::new();
    
    for ch in duration_str.chars() {
        match ch {
            '0'..='9' => current_number.push(ch),
            'h' => {
                let hours: u64 = current_number.parse()
                    .map_err(|_| Error::invalid_argument("Invalid hours format"))?;
                total_seconds += hours * 3600;
                current_number.clear();
            }
            'm' => {
                let minutes: u64 = current_number.parse()
                    .map_err(|_| Error::invalid_argument("Invalid minutes format"))?;
                total_seconds += minutes * 60;
                current_number.clear();
            }
            's' => {
                let seconds: u64 = current_number.parse()
                    .map_err(|_| Error::invalid_argument("Invalid seconds format"))?;
                total_seconds += seconds;
                current_number.clear();
            }
            _ => return Err(Error::invalid_argument("Invalid duration format")),
        }
    }
    
    if !current_number.is_empty() {
        return Err(Error::invalid_argument("Incomplete duration format"));
    }
    
    Ok(Duration::from_secs(total_seconds))
}

/// Format duration as human-readable string
pub fn format_duration(duration: Duration) -> String {
    let total_seconds = duration.as_secs();
    let hours = total_seconds / 3600;
    let minutes = (total_seconds % 3600) / 60;
    let seconds = total_seconds % 60;
    
    let mut parts = Vec::new();
    if hours > 0 {
        parts.push(format!("{}h", hours));
    }
    if minutes > 0 {
        parts.push(format!("{}m", minutes));
    }
    if seconds > 0 || parts.is_empty() {
        parts.push(format!("{}s", seconds));
    }
    
    parts.join("")
}

/// Retry operation with exponential backoff
pub async fn retry_with_backoff<F, Fut, T, E>(
    mut operation: F,
    max_attempts: u32,
    base_delay: Duration,
    max_delay: Duration,
) -> Result<T>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = std::result::Result<T, E>>,
    E: std::fmt::Debug,
{
    let mut attempt = 1;
    let mut delay = base_delay;
    
    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                if attempt >= max_attempts {
                    return Err(Error::internal(format!("Operation failed after {} attempts: {:?}", max_attempts, e)));
                }
                
                tracing::warn!("Operation failed (attempt {}/{}): {:?}, retrying in {:?}", 
                    attempt, max_attempts, e, delay);
                
                tokio::time::sleep(delay).await;
                
                attempt += 1;
                delay = std::cmp::min(delay * 2, max_delay);
            }
        }
    }
}

/// Measure execution time of a function
pub async fn measure_time<F, Fut, T>(f: F) -> (T, Duration)
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = T>,
{
    let start = Instant::now();
    let result = f().await;
    let elapsed = start.elapsed();
    (result, elapsed)
}

/// Measure execution time of a synchronous function
pub fn measure_time_sync<F, T>(f: F) -> (T, Duration)
where
    F: FnOnce() -> T,
{
    let start = Instant::now();
    let result = f();
    let elapsed = start.elapsed();
    (result, elapsed)
}

/// Convert bytes to human-readable format
pub fn format_bytes(bytes: u64) -> String {
    const UNITS: [&str; 5] = ["B", "KB", "MB", "GB", "TB"];
    let mut size = bytes as f64;
    let mut unit_index = 0;
    
    while size >= 1024.0 && unit_index < UNITS.len() - 1 {
        size /= 1024.0;
        unit_index += 1;
    }
    
    if unit_index == 0 {
        format!("{} {}", size as u64, UNITS[unit_index])
    } else {
        format!("{:.2} {}", size, UNITS[unit_index])
    }
}

/// Convert human-readable bytes to u64
pub fn parse_bytes(bytes_str: &str) -> Result<u64> {
    let bytes_str = bytes_str.trim();
    let (number_str, unit) = bytes_str.split_at(
        bytes_str.chars()
            .position(|c| !c.is_ascii_digit() && c != '.')
            .unwrap_or(bytes_str.len())
    );
    
    let number: f64 = number_str.parse()
        .map_err(|_| Error::invalid_argument("Invalid number format"))?;
    
    let multiplier = match unit.to_uppercase().as_str() {
        "B" | "" => 1,
        "KB" => 1024,
        "MB" => 1024 * 1024,
        "GB" => 1024 * 1024 * 1024,
        "TB" => 1024 * 1024 * 1024 * 1024,
        _ => return Err(Error::invalid_argument("Invalid unit format")),
    };
    
    Ok((number * multiplier as f64) as u64)
}

/// Generate a random string
pub fn generate_random_string(length: usize) -> String {
    use rand::{distributions::Alphanumeric, Rng};
    rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(length)
        .map(char::from)
        .collect()
}

/// Generate a secure random string
pub fn generate_secure_random_string(length: usize) -> Result<String> {
    use rand::{distributions::Alphanumeric, Rng};
    let mut rng = rand::rngs::OsRng::new()
        .map_err(|_| Error::internal("Failed to initialize secure RNG"))?;
    
    Ok(rng
        .sample_iter(&Alphanumeric)
        .take(length)
        .map(char::from)
        .collect())
}

/// Truncate string to specified length
pub fn truncate_string(s: &str, max_length: usize) -> String {
    if s.len() <= max_length {
        s.to_string()
    } else {
        format!("{}...", &s[..max_length - 3])
    }
}

/// Escape special characters in string
pub fn escape_string(s: &str) -> String {
    s.replace("\\", "\\\\")
        .replace("\"", "\\\"")
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
}

/// Unescape special characters in string
pub fn unescape_string(s: &str) -> Result<String> {
    let mut result = String::new();
    let mut chars = s.chars().peekable();
    
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some(c) => return Err(Error::invalid_argument(format!("Invalid escape sequence: \\{}", c))),
                None => return Err(Error::invalid_argument("Incomplete escape sequence")),
            }
        } else {
            result.push(ch);
        }
    }
    
    Ok(result)
}

/// Merge two HashMaps, with values from the second map taking precedence
pub fn merge_hashmaps<K, V>(mut map1: HashMap<K, V>, map2: HashMap<K, V>) -> HashMap<K, V>
where
    K: std::hash::Hash + Eq,
    V: Clone,
{
    for (key, value) in map2 {
        map1.insert(key, value);
    }
    map1
}

/// Deep clone a HashMap
pub fn deep_clone_hashmap<K, V>(map: &HashMap<K, V>) -> HashMap<K, V>
where
    K: Clone + std::hash::Hash + Eq,
    V: Clone,
{
    map.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
}

/// Check if a string contains only ASCII characters
pub fn is_ascii_only(s: &str) -> bool {
    s.chars().all(|c| c.is_ascii())
}

/// Check if a string contains only printable ASCII characters
pub fn is_printable_ascii_only(s: &str) -> bool {
    s.chars().all(|c| c.is_ascii() && !c.is_ascii_control())
}

/// Normalize line endings to Unix format (LF)
pub fn normalize_line_endings(s: &str) -> String {
    s.replace("\r\n", "\n").replace("\r", "\n")
}

/// Count words in a string
pub fn count_words(s: &str) -> usize {
    s.split_whitespace().count()
}

/// Count characters in a string (excluding whitespace)
pub fn count_characters_no_whitespace(s: &str) -> usize {
    s.chars().filter(|c| !c.is_whitespace()).count()
}

/// Check if a string is a valid JSON
pub fn is_valid_json(s: &str) -> bool {
    serde_json::from_str::<serde_json::Value>(s).is_ok()
}

/// Check if a string is a valid base64
pub fn is_valid_base64(s: &str) -> bool {
    use base64::{Engine as _, engine::general_purpose::STANDARD};
    STANDARD.decode(s).is_ok()
}

/// Encode bytes to base64
pub fn encode_base64(bytes: &[u8]) -> String {
    use base64::{Engine as _, engine::general_purpose::STANDARD};
    STANDARD.encode(bytes)
}

/// Decode base64 to bytes
pub fn decode_base64(s: &str) -> Result<Vec<u8>> {
    use base64::{Engine as _, engine::general_purpose::STANDARD};
    STANDARD.decode(s)
        .map_err(|e| Error::invalid_argument(format!("Invalid base64: {}", e)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_id() {
        let id1 = generate_id();
        let id2 = generate_id();
        assert_ne!(id1, id2);
        assert!(id1.starts_with("id_"));
    }

    #[test]
    fn test_generate_hash() {
        let hash = generate_string_hash("test");
        assert!(hash.starts_with("sha256:"));
        assert_eq!(hash.len(), 71); // "sha256:" + 64 hex chars
    }

    #[test]
    fn test_validate_email() {
        assert!(validate_email("test@example.com"));
        assert!(validate_email("user.name+tag@domain.co.uk"));
        assert!(!validate_email("invalid-email"));
        assert!(!validate_email("@example.com"));
    }

    #[test]
    fn test_validate_url() {
        assert!(validate_url("https://example.com"));
        assert!(validate_url("http://sub.domain.com/path?query=value"));
        assert!(!validate_url("not-a-url"));
        assert!(!validate_url("ftp://example.com"));
    }

    #[test]
    fn test_parse_duration() {
        assert_eq!(parse_duration("1h").unwrap(), Duration::from_secs(3600));
        assert_eq!(parse_duration("30m").unwrap(), Duration::from_secs(1800));
        assert_eq!(parse_duration("45s").unwrap(), Duration::from_secs(45));
        assert_eq!(parse_duration("1h30m45s").unwrap(), Duration::from_secs(5445));
        
        assert!(parse_duration("invalid").is_err());
    }

    #[test]
    fn test_format_duration() {
        assert_eq!(format_duration(Duration::from_secs(3661)), "1h1m1s");
        assert_eq!(format_duration(Duration::from_secs(65)), "1m5s");
        assert_eq!(format_duration(Duration::from_secs(30)), "30s");
    }

    #[test]
    fn test_format_bytes() {
        assert_eq!(format_bytes(1024), "1.00 KB");
        assert_eq!(format_bytes(1048576), "1.00 MB");
        assert_eq!(format_bytes(500), "500 B");
    }

    #[test]
    fn test_parse_bytes() {
        assert_eq!(parse_bytes("1 KB").unwrap(), 1024);
        assert_eq!(parse_bytes("1.5 MB").unwrap(), 1572864);
        assert_eq!(parse_bytes("500 B").unwrap(), 500);
        
        assert!(parse_bytes("invalid").is_err());
    }

    #[test]
    fn test_truncate_string() {
        assert_eq!(truncate_string("Hello World", 8), "Hello...");
        assert_eq!(truncate_string("Short", 10), "Short");
    }

    #[test]
    fn test_escape_unescape_string() {
        let original = "Hello\nWorld\t\"quoted\"";
        let escaped = escape_string(original);
        let unescaped = unescape_string(&escaped).unwrap();
        assert_eq!(unescaped, original);
    }

    #[test]
    fn test_is_valid_json() {
        assert!(is_valid_json("{\"key\": \"value\"}"));
        assert!(is_valid_json("[1, 2, 3]"));
        assert!(!is_valid_json("invalid json"));
    }

    #[test]
    fn test_base64_encoding() {
        let data = b"Hello, World!";
        let encoded = encode_base64(data);
        let decoded = decode_base64(&encoded).unwrap();
        assert_eq!(decoded, data);
    }

    #[tokio::test]
    async fn test_retry_with_backoff() {
        let mut attempts = 0;
        let result = retry_with_backoff(
            || async {
                attempts += 1;
                if attempts < 3 {
                    Err("temporary failure")
                } else {
                    Ok("success")
                }
            },
            3,
            Duration::from_millis(10),
            Duration::from_millis(100),
        ).await;
        
        assert!(result.is_ok());
        assert_eq!(attempts, 3);
    }

    #[tokio::test]
    async fn test_measure_time() {
        let (result, elapsed) = measure_time(|| async {
            tokio::time::sleep(Duration::from_millis(10)).await;
            "test"
        }).await;
        
        assert_eq!(result, "test");
        assert!(elapsed >= Duration::from_millis(10));
    }
}
