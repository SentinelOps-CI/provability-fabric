//! gRPC client implementations for Provability Fabric Core services

use tonic::transport::{Channel, Endpoint};
use tonic::metadata::MetadataValue;
use tonic::service::{Interceptor, interceptor::InterceptedService};
use std::time::Duration;

use crate::error::{Error, Result};
use crate::generated::{
    policy_kernel_service_client::PolicyKernelServiceClient,
    access_receipt_service_client::AccessReceiptServiceClient,
    egress_firewall_service_client::EgressFirewallServiceClient,
    safety_case_service_client::SafetyCaseServiceClient,
};

/// Authentication interceptor for adding auth headers
#[derive(Clone, Default)]
pub struct AuthInterceptor {
    auth_token: Option<MetadataValue<tonic::metadata::Ascii>>,
}

impl AuthInterceptor {
    pub fn new(token: String) -> Result<Self> {
        if token.is_empty() || token.bytes().any(|byte| byte.is_ascii_whitespace()) {
            return Err(Error::auth("Invalid bearer token"));
        }
        let mut auth_token = MetadataValue::try_from(format!("Bearer {}", token))
            .map_err(|_| Error::auth("Invalid bearer metadata"))?;
        auth_token.set_sensitive(true);
        Ok(Self { auth_token: Some(auth_token) })
    }
}

impl Interceptor for AuthInterceptor {
    fn call(&mut self, mut request: tonic::Request<()>) -> std::result::Result<tonic::Request<()>, tonic::Status> {
        if let Some(token) = &self.auth_token {
            request.metadata_mut().insert("authorization", token.clone());
        }
        Ok(request)
    }
}

pub type SdkChannel = InterceptedService<Channel, AuthInterceptor>;

/// Policy Kernel client for plan validation and enforcement
#[derive(Clone)]
pub struct PolicyKernelClient {
    client: PolicyKernelServiceClient<SdkChannel>,
}

impl PolicyKernelClient {
    /// Create a new Policy Kernel client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = PolicyKernelServiceClient::with_interceptor(channel, AuthInterceptor::default());
        Ok(Self { client })
    }

    /// Create a new authenticated Policy Kernel client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = PolicyKernelServiceClient::with_interceptor(channel, AuthInterceptor::new(auth_token)?);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &PolicyKernelServiceClient<SdkChannel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut PolicyKernelServiceClient<SdkChannel> {
        &mut self.client
    }
}

/// Access Receipt client for data access verification
#[derive(Clone)]
pub struct AccessReceiptClient {
    client: AccessReceiptServiceClient<SdkChannel>,
}

impl AccessReceiptClient {
    /// Create a new Access Receipt client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = AccessReceiptServiceClient::with_interceptor(channel, AuthInterceptor::default());
        Ok(Self { client })
    }

    /// Create a new authenticated Access Receipt client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = AccessReceiptServiceClient::with_interceptor(channel, AuthInterceptor::new(auth_token)?);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &AccessReceiptServiceClient<SdkChannel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut AccessReceiptServiceClient<SdkChannel> {
        &mut self.client
    }
}

/// Egress Firewall client for content scanning
#[derive(Clone)]
pub struct EgressFirewallClient {
    client: EgressFirewallServiceClient<SdkChannel>,
}

impl EgressFirewallClient {
    /// Create a new Egress Firewall client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = EgressFirewallServiceClient::with_interceptor(channel, AuthInterceptor::default());
        Ok(Self { client })
    }

    /// Create a new authenticated Egress Firewall client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = EgressFirewallServiceClient::with_interceptor(channel, AuthInterceptor::new(auth_token)?);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &EgressFirewallServiceClient<SdkChannel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut EgressFirewallServiceClient<SdkChannel> {
        &mut self.client
    }
}

/// Safety Case client for AI system validation
#[derive(Clone)]
pub struct SafetyCaseClient {
    client: SafetyCaseServiceClient<SdkChannel>,
}

impl SafetyCaseClient {
    /// Create a new Safety Case client
    pub async fn new(addr: &str) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = SafetyCaseServiceClient::with_interceptor(channel, AuthInterceptor::default());
        Ok(Self { client })
    }

    /// Create a new authenticated Safety Case client
    pub async fn new_with_auth(addr: &str, auth_token: String) -> Result<Self> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .connect()
            .await?;

        let client = SafetyCaseServiceClient::with_interceptor(channel, AuthInterceptor::new(auth_token)?);
        Ok(Self { client })
    }

    /// Get the underlying gRPC client
    pub fn client(&self) -> &SafetyCaseServiceClient<SdkChannel> {
        &self.client
    }

    /// Get a mutable reference to the underlying gRPC client
    pub fn client_mut(&mut self) -> &mut SafetyCaseServiceClient<SdkChannel> {
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
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .connect().await?;
        let mut client = PolicyKernelServiceClient::with_interceptor(channel, AuthInterceptor::default())
            .max_decoding_message_size(self.config.max_message_size)
            .max_encoding_message_size(self.config.max_message_size);
        if self.config.enable_compression {
            client = client.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }
        Ok(PolicyKernelClient { client })
    }

    /// Build an Access Receipt client
    pub async fn build_access_receipt_client(self, addr: &str) -> Result<AccessReceiptClient> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .connect().await?;
        let mut client = AccessReceiptServiceClient::with_interceptor(channel, AuthInterceptor::default())
            .max_decoding_message_size(self.config.max_message_size)
            .max_encoding_message_size(self.config.max_message_size);
        if self.config.enable_compression {
            client = client.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }
        Ok(AccessReceiptClient { client })
    }

    /// Build an Egress Firewall client
    pub async fn build_egress_firewall_client(self, addr: &str) -> Result<EgressFirewallClient> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .connect().await?;
        let mut client = EgressFirewallServiceClient::with_interceptor(channel, AuthInterceptor::default())
            .max_decoding_message_size(self.config.max_message_size)
            .max_encoding_message_size(self.config.max_message_size);
        if self.config.enable_compression {
            client = client.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }
        Ok(EgressFirewallClient { client })
    }

    /// Build a Safety Case client
    pub async fn build_safety_case_client(self, addr: &str) -> Result<SafetyCaseClient> {
        let channel = Endpoint::from_shared(addr.to_string())?
            .timeout(self.config.request_timeout)
            .connect_timeout(self.config.connect_timeout)
            .connect().await?;
        let mut client = SafetyCaseServiceClient::with_interceptor(channel, AuthInterceptor::default())
            .max_decoding_message_size(self.config.max_message_size)
            .max_encoding_message_size(self.config.max_message_size);
        if self.config.enable_compression {
            client = client.accept_compressed(tonic::codec::CompressionEncoding::Gzip)
                .send_compressed(tonic::codec::CompressionEncoding::Gzip);
        }
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

#[cfg(test)]
mod rpc_tests {
    use super::*;
    use crate::generated::{self as wire, access_receipt_service_server::{AccessReceiptService, AccessReceiptServiceServer}};
    use tonic::{Request, Response, Status};
    use tokio_stream::wrappers::TcpListenerStream;

    #[derive(Default)]
    struct Fixture;

    #[tonic::async_trait]
    impl AccessReceiptService for Fixture {
        async fn create_receipt(&self, _: Request<wire::CreateReceiptRequest>) -> std::result::Result<Response<wire::CreateReceiptResponse>, Status> {
            Err(Status::unimplemented("fixture"))
        }
        async fn verify_receipt(&self, _: Request<wire::VerifyReceiptRequest>) -> std::result::Result<Response<wire::VerifyReceiptResponse>, Status> {
            Err(Status::unimplemented("fixture"))
        }
        async fn revoke_receipt(&self, _: Request<wire::RevokeReceiptRequest>) -> std::result::Result<Response<wire::RevokeReceiptResponse>, Status> {
            Err(Status::unimplemented("fixture"))
        }
        async fn get_receipt(&self, _: Request<wire::GetReceiptRequest>) -> std::result::Result<Response<wire::GetReceiptResponse>, Status> {
            Err(Status::unimplemented("fixture"))
        }
        async fn list_receipts(&self, _: Request<wire::ListReceiptsRequest>) -> std::result::Result<Response<wire::ListReceiptsResponse>, Status> {
            Err(Status::unimplemented("fixture"))
        }
        async fn batch_verify_receipts(&self, _: Request<wire::BatchVerifyReceiptsRequest>) -> std::result::Result<Response<wire::BatchVerifyReceiptsResponse>, Status> {
            Err(Status::unimplemented("fixture"))
        }
        async fn get_receipt_stats(&self, _: Request<wire::GetReceiptStatsRequest>) -> std::result::Result<Response<wire::GetReceiptStatsResponse>, Status> {
            Err(Status::unimplemented("fixture"))
        }
        async fn health_check(&self, request: Request<wire::HealthCheckRequest>) -> std::result::Result<Response<wire::HealthCheckResponse>, Status> {
            if request.metadata().get("authorization").and_then(|v| v.to_str().ok()) != Some("Bearer fixture-token") {
                return Err(Status::unauthenticated("missing or invalid fixture authorization"));
            }
            Ok(Response::new(wire::HealthCheckResponse {
                version: "fixture".into(), ..Default::default()
            }))
        }
    }

    #[tokio::test]
    async fn test_real_grpc_authorization_and_dispatch() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let server = tokio::spawn(async move {
            tonic::transport::Server::builder()
                .add_service(AccessReceiptServiceServer::new(Fixture))
                .serve_with_incoming(TcpListenerStream::new(listener)).await.unwrap();
        });
        let addr = format!("http://{address}");
        let mut unauth = AccessReceiptClient::new(&addr).await.unwrap();
        let failure = unauth.client_mut().health_check(wire::HealthCheckRequest::default()).await.unwrap_err();
        assert_eq!(failure.code(), tonic::Code::Unauthenticated);
        let mut auth = AccessReceiptClient::new_with_auth(&addr, "fixture-token".into()).await.unwrap();
        let response = auth.client_mut().health_check(wire::HealthCheckRequest::default()).await.unwrap().into_inner();
        assert_eq!(response.version, "fixture");
        assert!(AuthInterceptor::new("bad\nvalue".into()).is_err());
        server.abort();
    }
}
