# Attestation Service

*This directory contains the hardware enclave attestation service for the Provability Fabric Core, providing secure verification of AWS Nitro, AMD SEV, and other hardware enclave attestations.*

## 🎯 Overview

The Attestation Service provides hardware-based security verification through enclave attestation. It verifies the integrity and authenticity of hardware enclaves, ensuring that cryptographic operations are performed in trusted, isolated environments.

## 🏗️ Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   Client        │    │   Attestation    │    │   Hardware      │
│   Application   │───▶│   Service        │───▶│   Enclaves      │
│                 │    │                  │    │                 │
│ Attestation     │    │ - Nitro Verifier │    │ - AWS Nitro     │
│ Request         │    │ - SEV Verifier   │    │ - AMD SEV       │
│                 │    │ - SGX Verifier   │    │ - Intel SGX     │
│ Verification    │◀───│ - Measurement    │◀───│ - Attestation   │
│ Result          │    │   Validation     │    │   Documents     │
└─────────────────┘    └──────────────────┘    └─────────────────┘
```

### Key Components

1. **NitroVerifier**: AWS Nitro enclave attestation verification
2. **SEVVerifier**: AMD SEV attestation verification
3. **SGXVerifier**: Intel SGX attestation verification
4. **MeasurementValidator**: PCR and measurement validation
5. **CertificateValidator**: Certificate chain verification

## 🚀 Quick Start

### Prerequisites

```bash
# Install Rust and Cargo
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install required dependencies
cargo add anyhow
cargo add serde
cargo add tokio
cargo add tracing
cargo add sha2
cargo add base64

# Verify installation
cargo --version
```

### Basic Usage

```rust
use runtime::attestor::nitro::{NitroVerifier, NitroMeasurements, NitroAttestationDoc};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create expected measurements
    let measurements = NitroMeasurements {
        expected_pcrs: HashMap::from([
            ("0".to_string(), "expected_pcr_0_hash".to_string()),
            ("1".to_string(), "expected_pcr_1_hash".to_string()),
            ("2".to_string(), "expected_pcr_2_hash".to_string()),
        ]),
        expected_module_id: "expected_module_id".to_string(),
        expected_digest: "expected_digest".to_string(),
        max_age_seconds: 3600, // 1 hour
    };
    
    // Create verifier with trusted CA certificates
    let trusted_ca_certs = vec![
        std::fs::read("path/to/trusted_ca.pem")?,
    ];
    
    let verifier = NitroVerifier::new(measurements, trusted_ca_certs);
    
    // Load attestation document
    let attestation_doc = load_attestation_document()?;
    
    // Verify attestation
    let result = verifier.verify_attestation(&attestation_doc).await?;
    
    match result {
        AttestationResult::Valid { enclave_id, measurements, expires_at } => {
            println!("✅ Attestation valid for enclave: {}", enclave_id);
            println!("   Measurements: {:?}", measurements);
            println!("   Expires at: {}", expires_at);
        },
        AttestationResult::Invalid { reason, details } => {
            println!("❌ Attestation invalid: {}", reason);
            println!("   Details: {}", details);
        },
        AttestationResult::Expired { attested_at, current_time } => {
            println!("⏰ Attestation expired");
            println!("   Attested at: {}", attested_at);
            println!("   Current time: {}", current_time);
        },
    }
    
    Ok(())
}
```

## 🔐 AWS Nitro Enclave Attestation

### Attestation Document Structure

```rust
/// Nitro enclave attestation document structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NitroAttestationDoc {
    /// Unique module identifier
    pub module_id: String,
    
    /// Module digest hash
    pub digest: String,
    
    /// Attestation timestamp
    pub timestamp: u64,
    
    /// Validity period
    pub validity: Validity,
    
    /// Platform Configuration Registers (PCRs)
    pub pcrs: HashMap<String, String>,
    
    /// Attestation certificate
    pub certificate: String,
    
    /// Certificate authority bundle
    pub cabundle: Vec<String>,
    
    /// Document signature
    pub signature: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Validity {
    /// Not valid before timestamp
    pub not_before: u64,
    
    /// Not valid after timestamp
    pub not_after: u64,
}
```

### Verification Process

```rust
impl NitroVerifier {
    /// Verify a Nitro attestation document
    pub async fn verify_attestation(
        &self,
        attestation_doc: &NitroAttestationDoc,
    ) -> Result<AttestationResult> {
        // 1. Verify document signature
        if !self.verify_signature(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid signature".to_string(),
                details: "Document signature verification failed".to_string(),
            });
        }
        
        // 2. Verify certificate chain
        if !self.verify_certificate_chain(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid certificate chain".to_string(),
                details: "Certificate chain verification failed".to_string(),
            });
        }
        
        // 3. Verify timestamp validity
        let current_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
            
        if current_time < attestation_doc.validity.not_before {
            return Ok(AttestationResult::Invalid {
                reason: "Document not yet valid".to_string(),
                details: format!("Document valid from {}", attestation_doc.validity.not_before),
            });
        }
        
        if current_time > attestation_doc.validity.not_after {
            return Ok(AttestationResult::Expired {
                attested_at: attestation_doc.timestamp,
                current_time,
            });
        }
        
        // 4. Validate PCR measurements
        if !self.validate_pcr_measurements(&attestation_doc.pcrs).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid PCR measurements".to_string(),
                details: "PCR measurements do not match expected values".to_string(),
            });
        }
        
        Ok(AttestationResult::Valid {
            enclave_id: attestation_doc.module_id.clone(),
            measurements: attestation_doc.pcrs.clone(),
            expires_at: attestation_doc.validity.not_after,
        })
    }
}
```

### PCR Measurement Validation

```rust
impl NitroVerifier {
    /// Validate PCR measurements against expected values
    async fn validate_pcr_measurements(
        &self,
        pcrs: &HashMap<String, String>,
    ) -> Result<bool> {
        for (pcr_id, expected_value) in &self.measurements.expected_pcrs {
            if let Some(actual_value) = pcrs.get(pcr_id) {
                if actual_value != expected_value {
                    warn!(
                        "PCR {} mismatch: expected {}, got {}",
                        pcr_id, expected_value, actual_value
                    );
                    return Ok(false);
                }
            } else {
                warn!("Required PCR {} not found in attestation", pcr_id);
                return Ok(false);
            }
        }
        
        Ok(true)
    }
}
```

## 🛡️ AMD SEV Attestation

### SEV Attestation Structure

```rust
/// SEV attestation document structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SEVAttestationDoc {
    /// Platform information
    pub platform_info: PlatformInfo,
    
    /// SEV report data
    pub report: Vec<u8>,
    
    /// Report signature
    pub signature: Vec<u8>,
    
    /// Certificate chain
    pub cert_chain: Vec<Vec<u8>>,
    
    /// Attestation timestamp
    pub timestamp: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlatformInfo {
    /// Platform family
    pub family: String,
    
    /// Platform model
    pub model: String,
    
    /// Platform version
    pub version: String,
    
    /// Platform state
    pub state: String,
}
```

### SEV Verification

```rust
/// SEV attestation verifier
pub struct SEVVerifier {
    /// Trusted root certificate
    trusted_root_cert: Vec<u8>,
    
    /// Expected measurements
    expected_measurements: SEVMeasurements,
}

impl SEVVerifier {
    /// Verify SEV attestation document
    pub async fn verify_attestation(
        &self,
        attestation_doc: &SEVAttestationDoc,
    ) -> Result<AttestationResult> {
        // Verify SEV report signature
        if !self.verify_report_signature(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid report signature".to_string(),
                details: "SEV report signature verification failed".to_string(),
            });
        }
        
        // Validate certificate chain
        if !self.verify_certificate_chain(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid certificate chain".to_string(),
                details: "SEV certificate chain verification failed".to_string(),
            });
        }
        
        // Check platform measurements
        if !self.validate_platform_measurements(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid platform measurements".to_string(),
                details: "Platform measurements do not match expected values".to_string(),
            });
        }
        
        // Verify timestamp validity
        let current_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
            
        if current_time > attestation_doc.timestamp + self.expected_measurements.max_age_seconds {
            return Ok(AttestationResult::Expired {
                attested_at: attestation_doc.timestamp,
                current_time,
            });
        }
        
        Ok(AttestationResult::Valid {
            enclave_id: format!("sev_{}", attestation_doc.timestamp),
            measurements: self.extract_measurements(attestation_doc),
            expires_at: attestation_doc.timestamp + self.expected_measurements.max_age_seconds,
        })
    }
}
```

## 🔍 Intel SGX Attestation

### SGX Attestation Structure

```rust
/// SGX attestation document structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SGXAttestationDoc {
    /// Quote data
    pub quote: Vec<u8>,
    
    /// Quote signature
    pub signature: Vec<u8>,
    
    /// Attestation key certificate
    pub attestation_key_cert: Vec<u8>,
    
    /// Platform certificate
    pub platform_cert: Vec<u8>,
    
    /// Root certificate
    pub root_cert: Vec<u8>,
    
    /// Timestamp
    pub timestamp: u64,
}

/// SGX attestation verifier
pub struct SGXVerifier {
    /// Trusted root certificate
    trusted_root_cert: Vec<u8>,
    
    /// Expected measurements
    expected_measurements: SGXMeasurements,
}

impl SGXVerifier {
    /// Verify SGX attestation document
    pub async fn verify_attestation(
        &self,
        attestation_doc: &SGXAttestationDoc,
    ) -> Result<AttestationResult> {
        // Verify quote signature
        if !self.verify_quote_signature(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid quote signature".to_string(),
                details: "SGX quote signature verification failed".to_string(),
            });
        }
        
        // Validate certificate chain
        if !self.verify_certificate_chain(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid certificate chain".to_string(),
                details: "SGX certificate chain verification failed".to_string(),
            });
        }
        
        // Check enclave measurements
        if !self.validate_enclave_measurements(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid enclave measurements".to_string(),
                details: "Enclave measurements do not match expected values".to_string(),
            });
        }
        
        Ok(AttestationResult::Valid {
            enclave_id: format!("sgx_{}", attestation_doc.timestamp),
            measurements: self.extract_measurements(attestation_doc),
            expires_at: attestation_doc.timestamp + self.expected_measurements.max_age_seconds,
        })
    }
}
```

## 📊 Attestation Results

### Result Types

```rust
/// Attestation verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttestationResult {
    /// Valid attestation
    Valid {
        /// Enclave identifier
        enclave_id: String,
        
        /// Enclave measurements
        measurements: HashMap<String, String>,
        
        /// Expiration timestamp
        expires_at: u64,
    },
    
    /// Invalid attestation
    Invalid {
        /// Reason for invalidation
        reason: String,
        
        /// Detailed explanation
        details: String,
    },
    
    /// Expired attestation
    Expired {
        /// When attestation was created
        attested_at: u64,
        
        /// Current timestamp
        current_time: u64,
    },
}
```

### Result Processing

```rust
/// Process attestation result
fn process_attestation_result(result: &AttestationResult) -> bool {
    match result {
        AttestationResult::Valid { enclave_id, measurements, expires_at } => {
            info!("✅ Attestation valid for enclave: {}", enclave_id);
            info!("   Measurements: {:?}", measurements);
            info!("   Expires at: {}", expires_at);
            true
        },
        AttestationResult::Invalid { reason, details } => {
            error!("❌ Attestation invalid: {}", reason);
            error!("   Details: {}", details);
            false
        },
        AttestationResult::Expired { attested_at, current_time } => {
            warn!("⏰ Attestation expired");
            warn!("   Attested at: {}", attested_at);
            warn!("   Current time: {}", current_time);
            false
        },
    }
}
```

## 🔒 Security Features

### Cryptographic Verification

1. **Signature Verification**: Ed25519 signature validation for attestation documents
2. **Certificate Chain Validation**: X.509 certificate chain verification
3. **Timestamp Validation**: Attestation document validity period checking
4. **Measurement Validation**: PCR and enclave measurement verification
5. **Root of Trust**: Hardware-based root of trust validation

### Threat Mitigation

- **Replay Attacks**: Timestamp validation and nonce checking
- **Man-in-the-Middle**: Certificate chain validation
- **Tampering**: Cryptographic signature verification
- **Spoofing**: Hardware-based measurement validation
- **Time-based Attacks**: Clock synchronization and validation

## 🧪 Testing

### Unit Tests

```bash
# Run all tests
cargo test

# Run specific test categories
cargo test --lib
cargo test --test integration
```

### Integration Tests

```rust
#[tokio::test]
async fn test_nitro_verification() {
    let measurements = create_test_measurements();
    let trusted_certs = load_test_certificates();
    let verifier = NitroVerifier::new(measurements, trusted_certs);
    
    let attestation_doc = create_test_attestation_doc();
    let result = verifier.verify_attestation(&attestation_doc).await.unwrap();
    
    match result {
        AttestationResult::Valid { enclave_id, .. } => {
            assert_eq!(enclave_id, "test_enclave");
        },
        _ => panic!("Expected valid attestation"),
    }
}

#[tokio::test]
async fn test_expired_attestation() {
    let measurements = create_test_measurements();
    let trusted_certs = load_test_certificates();
    let verifier = NitroVerifier::new(measurements, trusted_certs);
    
    let expired_doc = create_expired_attestation_doc();
    let result = verifier.verify_attestation(&expired_doc).await.unwrap();
    
    match result {
        AttestationResult::Expired { .. } => {
            // Expected behavior
        },
        _ => panic!("Expected expired attestation"),
    }
}
```

### Performance Tests

```rust
#[tokio::test]
async fn test_verification_performance() {
    let measurements = create_test_measurements();
    let trusted_certs = load_test_certificates();
    let verifier = NitroVerifier::new(measurements, trusted_certs);
    
    let attestation_docs = create_multiple_attestation_docs(100);
    
    let start = std::time::Instant::now();
    let mut results = Vec::new();
    
    for doc in attestation_docs {
        let result = verifier.verify_attestation(&doc).await.unwrap();
        results.push(result);
    }
    
    let duration = start.elapsed();
    
    // Performance requirements
    assert!(duration.as_millis() < 1000); // Should complete in <1 second
    assert_eq!(results.len(), 100);
}
```

## 🔧 Configuration

### Environment Variables

```bash
# Attestation settings
export ATTESTATION_MAX_AGE_SECONDS=3600
export ATTESTATION_REQUIRE_SIGNATURE=true
export ATTESTATION_VALIDATE_CERT_CHAIN=true
export ATTESTATION_CHECK_TIMESTAMPS=true

# Performance tuning
export ATTESTATION_BATCH_SIZE=100
export ATTESTATION_PARALLEL=true
export ATTESTATION_CACHE_SIZE=1000
```

### Configuration Files

```toml
# Cargo.toml
[dependencies]
anyhow = "1.0"
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }
tracing = "0.1"
sha2 = "0.10"
base64 = "0.21"
```

## 📚 API Reference

### NitroVerifier

```rust
impl NitroVerifier {
    /// Create new verifier
    pub fn new(measurements: NitroMeasurements, trusted_ca_certs: Vec<Vec<u8>>) -> Self
    
    /// Verify attestation document
    pub async fn verify_attestation(&self, attestation_doc: &NitroAttestationDoc) -> Result<AttestationResult>
    
    /// Validate PCR measurements
    async fn validate_pcr_measurements(&self, pcrs: &HashMap<String, String>) -> Result<bool>
    
    /// Verify document signature
    async fn verify_signature(&self, attestation_doc: &NitroAttestationDoc) -> Result<bool>
    
    /// Verify certificate chain
    async fn verify_certificate_chain(&self, attestation_doc: &NitroAttestationDoc) -> Result<bool>
}
```

### SEVVerifier

```rust
impl SEVVerifier {
    /// Create new verifier
    pub fn new(trusted_root_cert: Vec<u8>, expected_measurements: SEVMeasurements) -> Self
    
    /// Verify attestation document
    pub async fn verify_attestation(&self, attestation_doc: &SEVAttestationDoc) -> Result<AttestationResult>
    
    /// Verify report signature
    async fn verify_report_signature(&self, attestation_doc: &SEVAttestationDoc) -> Result<bool>
    
    /// Validate platform measurements
    async fn validate_platform_measurements(&self, attestation_doc: &SEVAttestationDoc) -> Result<bool>
}
```

### SGXVerifier

```rust
impl SGXVerifier {
    /// Create new verifier
    pub fn new(trusted_root_cert: Vec<u8>, expected_measurements: SGXMeasurements) -> Self
    
    /// Verify attestation document
    pub async fn verify_attestation(&self, attestation_doc: &SGXAttestationDoc) -> Result<AttestationResult>
    
    /// Verify quote signature
    async fn verify_quote_signature(&self, attestation_doc: &SGXAttestationDoc) -> Result<bool>
    
    /// Validate enclave measurements
    async fn validate_enclave_measurements(&self, attestation_doc: &SGXAttestationDoc) -> Result<bool>
}
```

## 🔮 Future Enhancements

### Planned Features

1. **Additional Enclave Support**: ARM TrustZone, RISC-V security extensions
2. **Advanced Attestation**: Multi-party attestation protocols
3. **Zero-Knowledge Proofs**: Privacy-preserving attestation
4. **Remote Attestation**: Network-based attestation verification
5. **Attestation Aggregation**: Batch attestation verification

### Research Areas

1. **Post-Quantum Attestation**: Quantum-resistant attestation protocols
2. **Advanced Measurements**: AI-based measurement validation
3. **Attestation Privacy**: Privacy-preserving attestation techniques
4. **Cross-Platform Attestation**: Multi-vendor attestation support
5. **Attestation Formalization**: Mathematical security proofs

## 📚 Additional Resources

- **[AWS Nitro Enclaves](https://docs.aws.amazon.com/enclaves/)**: AWS Nitro documentation
- **[AMD SEV](https://developer.amd.com/sev/)**: AMD SEV documentation
- **[Intel SGX](https://www.intel.com/content/www/us/en/developer/tools/software-guard-extensions/overview.html)**: Intel SGX documentation
- **[Attestation Standards](https://www.ietf.org/standards/rfcs/)**: IETF attestation RFCs

## 🤝 Contributing

### Development Setup

```bash
# Clone repository
git clone https://github.com/provability-fabric/provability-fabric.git
cd provability-fabric

# Install dependencies
cargo build

# Run tests
cargo test

# Run benchmarks
cargo bench
```

### Code Guidelines

- **Security First**: All attestation operations must be secure by default
- **Performance**: Optimize for high-throughput verification
- **Error Handling**: Use proper error types and propagation
- **Documentation**: Document all public APIs and security considerations
- **Testing**: Maintain high test coverage with security-focused tests

---

## 🎯 Summary

The Attestation Service provides hardware-based security verification through enclave attestation. With support for AWS Nitro, AMD SEV, and Intel SGX, the service ensures the integrity and authenticity of hardware enclaves while maintaining high performance and security standards.

For questions or contributions, please refer to the main project documentation or open an issue in the repository.
