//! Provability Fabric Core SDK for Rust
//!
//! This SDK provides Rust bindings for the Provability Fabric Core API,
//! enabling developers to interact with the policy kernel, access receipts,
//! egress firewall, and safety case services.
//!
//! # Features
//!
//! - **Policy Kernel**: Plan validation and policy enforcement
//! - **Access Receipts**: Data access verification and management
//! - **Egress Firewall**: Content scanning and certificate generation
//! - **Safety Cases**: AI system safety validation and compliance
//!
//! # Quick Start
//!
//! ```rust
//! use provability_fabric_core_sdk_rust::{
//!     PolicyKernelClient,
//!     AccessReceiptClient,
//!     EgressFirewallClient,
//!     SafetyCaseClient,
//! };
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // Create clients
//!     let kernel_client = PolicyKernelClient::new("http://localhost:50051").await?;
//!     let receipt_client = AccessReceiptClient::new("http://localhost:50052").await?;
//!     let firewall_client = EgressFirewallClient::new("http://localhost:50053").await?;
//!     let safety_client = SafetyCaseClient::new("http://localhost:50054").await?;
//!     
//!     // Use the clients...
//!     Ok(())
//! }
//! ```

pub mod client;
pub mod error;
pub mod types;
pub mod utils;

// Re-export generated protobuf types
pub use tonic::transport::Channel;

// Re-export client types
pub use client::{AccessReceiptClient, EgressFirewallClient, PolicyKernelClient, SafetyCaseClient};

// Re-export error types
pub use error::{Error, Result};

// Re-export utility types
pub use types::*;
pub use utils::*;

// Include generated protobuf code
pub mod generated {
    tonic::include_proto!("provability_fabric.api.v1");
}

// Re-export common types from generated code
pub use generated::{egress::*, kernel::*, plan::*, receipt::*, safety_case::*};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sdk_compilation() {
        // This test ensures the SDK compiles correctly
        assert!(true);
    }
}
