//! gRPC client implementations for Provability Fabric Core services

use tonic::transport::{Channel, Endpoint};
use tonic::metadata::MetadataValue;
use tonic::service::Interceptor;
use std::time::Duration;

use crate::error::{Error, Result};
use crate::generated::{
    policy_kernel_service_client::PolicyKernelServiceClient,
    access_receipt_service_client::AccessReceiptServiceClient,
    egress_firewall_service_client::EgressFirewallServiceClient,
    safety_case_service_client::SafetyCaseClient,
};

/// Authentication interceptor for adding auth headers
#[derive(Clone)]
pub struct AuthInterceptor {
    auth_token: MetadataValue<tonic::metadata::Ascii>,
}

impl AuthInterceptor {
    pub fn new(token: String) -> Result<Self> {
        let auth_token = MetadataValue::try_from(format!("Bearer {}", token))?;
        Ok(Self { auth_token })
    }
}

impl Interceptor for AuthInterceptor {
    fn call(&mut self, mut request: tonic::Request<()>) -> Result<tonic::Request<()>, tonic::Status> {
        request.metadata_mut().insert("authorization", self.auth_token.clone());
        Ok(request)
    }
}

/// Policy Kernel client for plan validation and enforcement
#[derive(Clone)]
pub struct PolicyKernelClient {
    client: PolicyKernelServiceClient<Channel>,
}

impl PolicyKernelClient {
    /// Create a new Policy Kernel client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = PolicyKernelServiceClient::new(channel);
        Ok(Self { client })
    }

    /// Create a new authenticated Policy Kernel client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .intercept_with(AuthInterceptor::new(auth_token)?)
            .connect()
            .await?;

        let client = PolicyKernelServiceClient::new(channel);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &PolicyKernelServiceClient<Channel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut PolicyKernelServiceClient<Channel> {
        &mut self.client
    }
}

/// Access Receipt client for data access verification
#[derive(Clone)]
pub struct AccessReceiptClient {
    client: AccessReceiptServiceClient<Channel>,
}

impl AccessReceiptClient {
    /// Create a new Access Receipt client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = AccessReceiptServiceClient::new(channel);
        Ok(Self { client })
    }

    /// Create a new authenticated Access Receipt client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .intercept_with(AuthInterceptor::new(auth_token)?)
            .connect()
            .await?;

        let client = AccessReceiptServiceClient::new(channel);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &AccessReceiptServiceClient<Channel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut AccessReceiptServiceClient<Channel> {
        &mut self.client
    }
}

/// Egress Firewall client for content scanning
#[derive(Clone)]
pub struct EgressFirewallClient {
    client: EgressFirewallServiceClient<Channel>,
}

impl EgressFirewallClient {
    /// Create a new Egress Firewall client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = EgressFirewallServiceClient::new(channel);
        Ok(Self { client })
    }

    /// Create a new authenticated Egress Firewall client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .intercept_with(AuthInterceptor::new(auth_token)?)
            .connect()
            .await?;

        let client = EgressFirewallServiceClient::new(channel);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &EgressFirewallServiceClient<Channel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut EgressFirewallServiceClient<Channel> {
        &mut self.client
    }
}

/// Safety Case client for AI system validation
#[derive(Clone)]
pub struct SafetyCaseClient {
    client: SafetyCaseClient<Channel>,
}

impl SafetyCaseClient {
    /// Create a new Safety Case client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = SafetyCaseClient::new(channel);
        Ok(Self { client })
    }

    /// Create a new authenticated Safety Case client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .intercept_with(AuthInterceptor::new(auth_token)?)
            .connect()
            .await?;

        let client = SafetyCaseClient::new(channel);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &SafetyCaseClient<Channel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut SafetyCaseClient<Channel> {
        &mut self.client
    }
}

/// Client configuration options
#[derive(Clone, Debug)]
pub struct ClientConfig {
    /// Connection timeout
    pub connect_timeout: Duration,
    /// Request timeout
    pub request_timeout: Duration,
    /// Maximum message size
    pub max_message_size: usize,
    /// Enable compression
    pub enable_compression: bool,
    /// Retry configuration
    pub retry_config: RetryConfig,
}

impl Default for ClientConfig {
    fn default() -> Self {
        Self {
            connect_timeout: Duration::from_secs(10),
            request_timeout: Duration::from_secs(30),
            max_message_size: 1024 * 1024 * 4, // 4MB
            enable_compression: true,
            retry_config: RetryConfig::default(),
        }
    }
}

/// Retry configuration for client operations
#[derive(Clone, Debug)]
pub struct RetryConfig {
    /// Maximum retry attempts
    pub max_attempts: u32,
    /// Base delay between retries
    pub base_delay: Duration,
    /// Maximum delay between retries
    pub max_delay: Duration,
    /// Backoff multiplier
    pub backoff_multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            backoff_multiplier: 2.0,
        }
    }
}

/// Builder for creating clients with custom configuration
pub struct ClientBuilder {
    config: ClientConfig,
}

impl ClientBuilder {
    /// Create a new client builder
    pub fn new() -> Self {
        Self {
            config: ClientConfig::default(),
        }
    }

    /// Set connection timeout
    pub fn connect_timeout(mut self, timeout: Duration) -> Self {
        self.config.connect_timeout = timeout;
        self
    }

    /// Set request timeout
    pub fn request_timeout(mut self, timeout: Duration) -> Self {
        self.config.request_timeout = timeout;
        self
    }

    /// Set maximum message size
    pub fn max_message_size(mut self, size: usize) -> Self {
        self.config.max_message_size = size;
        self
    }

    /// Enable/disable compression
    pub fn enable_compression(mut self, enable: bool) -> Self {
        self.config.enable_compression = enable;
        self
    }

    /// Set retry configuration
    pub fn retry_config(mut self, config: RetryConfig) -> Self {
        self.config.retry_config = config;
        self
    }

    /// Build a Policy Kernel client
    pub async fn build_policy_kernel_client(self, addr: &str) -> Result<PolicyKernelClient> {
        let mut endpoint = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .max_message_size(self.config.max_message_size);

        if self.config.enable_compression {
            endpoint = endpoint.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }

        let channel = endpoint.connect().await?;
        let client = PolicyKernelServiceClient::new(channel);
        Ok(PolicyKernelClient { client })
    }

    /// Build an Access Receipt client
    pub async fn build_access_receipt_client(self, addr: &str) -> Result<AccessReceiptClient> {
        let mut endpoint = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .max_message_size(self.config.max_message_size);

        if self.config.enable_compression {
            endpoint = endpoint.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }

        let channel = endpoint.connect().await?;
        let client = AccessReceiptServiceClient::new(channel);
        Ok(AccessReceiptClient { client })
    }

    /// Build an Egress Firewall client
    pub async fn build_egress_firewall_client(self, addr: &str) -> Result<EgressFirewallClient> {
        let mut endpoint = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .max_message_size(self.config.max_message_size);

        if self.config.enable_compression {
            endpoint = endpoint.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }

        let channel = endpoint.connect().await?;
        let client = EgressFirewallServiceClient::new(channel);
        Ok(EgressFirewallClient { client })
    }

    /// Build a Safety Case client
    pub async fn build_safety_case_client(self, addr: &str) -> Result<SafetyCaseClient> {
        let mut endpoint = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .max_message_size(self.config.max_message_size);

        if self.config.enable_compression {
            endpoint = endpoint.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }

        let channel = endpoint.connect().await?;
        let client = SafetyCaseClient::new(channel);
        Ok(SafetyCaseClient { client })
    }
}

impl Default for ClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_client_builder() {
        let config = ClientConfig {
            connect_timeout: Duration::from_secs(5),
            request_timeout: Duration::from_secs(15),
            max_message_size: 1024 * 1024, // 1MB
            enable_compression: false,
            retry_config: RetryConfig::default(),
        };

        let builder = ClientBuilder::new()
            .connect_timeout(config.connect_timeout)
            .request_timeout(config.request_timeout)
            .max_message_size(config.max_message_size)
            .enable_compression(config.enable_compression);

        assert_eq!(builder.config.connect_timeout, config.connect_timeout);
        assert_eq!(builder.config.request_timeout, config.request_timeout);
        assert_eq!(builder.config.max_message_size, config.max_message_size);
        assert_eq!(builder.config.enable_compression, config.enable_compression);
    }
}
