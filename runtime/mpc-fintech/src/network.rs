// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//! High-Performance Network Manager for MPC Financial Operations
//! 
//! This module provides optimized networking with sub-millisecond latency
//! targets for financial MPC operations.

use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use serde::{Deserialize, Serialize};
use tracing::{info, debug, warn};

use crate::NetworkConfig;

/// Network manager for MPC operations
pub struct NetworkManager {
    /// Network configuration
    config: NetworkConfig,
    /// Active connections to MPC parties
    connections: Arc<RwLock<HashMap<u32, Connection>>>,
    /// Connection pool for performance
    connection_pool: Arc<Mutex<ConnectionPool>>,
    /// Network statistics
    stats: Arc<Mutex<NetworkStats>>,
}

/// Individual connection to an MPC party
#[derive(Debug, Clone)]
struct Connection {
    /// Party identifier
    party_id: u32,
    /// Connection state
    state: ConnectionState,
    /// Connection endpoint
    endpoint: String,
    /// Last activity timestamp
    last_activity: std::time::Instant,
    /// Connection metrics
    metrics: ConnectionMetrics,
}

/// Connection state
#[derive(Debug, Clone)]
enum ConnectionState {
    /// Connection is establishing
    Connecting,
    /// Connection is active and ready
    Active,
    /// Connection is temporarily unavailable
    Unavailable,
    /// Connection is closed
    Closed,
}

/// Connection metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ConnectionMetrics {
    /// Round-trip time in microseconds
    rtt_us: u64,
    /// Bytes sent
    bytes_sent: u64,
    /// Bytes received
    bytes_received: u64,
    /// Number of messages sent
    messages_sent: u64,
    /// Number of messages received
    messages_received: u64,
    /// Connection errors
    error_count: u64,
}

/// Connection pool for managing multiple connections
struct ConnectionPool {
    /// Available connections
    available: Vec<Connection>,
    /// Maximum pool size
    max_size: usize,
    /// Current pool utilization
    utilization: f64,
}

/// Network statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkStats {
    /// Total active connections
    pub active_connections: u32,
    /// Average round-trip time
    pub avg_rtt_us: u64,
    /// Total throughput in bytes per second
    pub throughput_bps: u64,
    /// Network error rate
    pub error_rate_percent: f64,
    /// Statistics timestamp
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

impl NetworkManager {
    /// Create a new network manager
    pub async fn new(config: NetworkConfig) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        info!("Initializing network manager");
        
        let manager = Self {
            config,
            connections: Arc::new(RwLock::new(HashMap::new())),
            connection_pool: Arc::new(Mutex::new(ConnectionPool {
                available: Vec::new(),
                max_size: 100,
                utilization: 0.0,
            })),
            stats: Arc::new(Mutex::new(NetworkStats {
                active_connections: 0,
                avg_rtt_us: 0,
                throughput_bps: 0,
                error_rate_percent: 0.0,
                timestamp: chrono::Utc::now(),
            })),
        };
        
        // Initialize connections to all parties
        manager.initialize_connections().await?;
        
        info!("Network manager initialized successfully");
        Ok(manager)
    }
    
    /// Initialize connections to all MPC parties
    async fn initialize_connections(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut connections = self.connections.write().await;
        
        for (&party_id, endpoint) in &self.config.party_addresses {
            info!("Establishing connection to party {} at {}", party_id, endpoint);
            
            let connection = Connection {
                party_id,
                state: ConnectionState::Connecting,
                endpoint: endpoint.clone(),
                last_activity: std::time::Instant::now(),
                metrics: ConnectionMetrics {
                    rtt_us: 0,
                    bytes_sent: 0,
                    bytes_received: 0,
                    messages_sent: 0,
                    messages_received: 0,
                    error_count: 0,
                },
            };
            
            // In production, this would establish actual network connections
            let mut active_connection = connection;
            active_connection.state = ConnectionState::Active;
            
            connections.insert(party_id, active_connection);
        }
        
        info!("All party connections established");
        Ok(())
    }
    
    /// Send message to specific party
    pub async fn send_message(
        &self,
        party_id: u32,
        message: &[u8],
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let start_time = std::time::Instant::now();
        
        // Get connection for party
        let mut connections = self.connections.write().await;
        let connection = connections.get_mut(&party_id)
            .ok_or_else(|| format!("No connection to party {}", party_id))?;
        
        if !matches!(connection.state, ConnectionState::Active) {
            return Err(format!("Connection to party {} not active", party_id).into());
        }
        
        // In production, this would send actual network message
        debug!("Sending {} bytes to party {}", message.len(), party_id);
        
        // Update connection metrics
        connection.metrics.bytes_sent += message.len() as u64;
        connection.metrics.messages_sent += 1;
        connection.last_activity = std::time::Instant::now();
        
        // Calculate RTT (simulated)
        let rtt = start_time.elapsed();
        connection.metrics.rtt_us = rtt.as_micros() as u64;
        
        Ok(())
    }
    
    /// Broadcast message to all parties
    pub async fn broadcast_message(
        &self,
        message: &[u8],
    ) -> Result<Vec<u32>, Box<dyn std::error::Error + Send + Sync>> {
        debug!("Broadcasting {} bytes to all parties", message.len());
        
        let connections = self.connections.read().await;
        let party_ids: Vec<u32> = connections.keys().cloned().collect();
        drop(connections);
        
        let mut successful_parties = Vec::new();
        
        for party_id in party_ids {
            match self.send_message(party_id, message).await {
                Ok(_) => successful_parties.push(party_id),
                Err(e) => warn!("Failed to send message to party {}: {}", party_id, e),
            }
        }
        
        info!("Broadcast completed: {}/{} parties reached", 
              successful_parties.len(), self.config.party_addresses.len());
        
        Ok(successful_parties)
    }
    
    /// Receive message from party (simulated)
    pub async fn receive_message(
        &self,
        party_id: u32,
    ) -> Result<Vec<u8>, Box<dyn std::error::Error + Send + Sync>> {
        let mut connections = self.connections.write().await;
        let connection = connections.get_mut(&party_id)
            .ok_or_else(|| format!("No connection to party {}", party_id))?;
        
        // Simulate receiving a message
        let mock_message = format!("response_from_party_{}", party_id).into_bytes();
        
        // Update metrics
        connection.metrics.bytes_received += mock_message.len() as u64;
        connection.metrics.messages_received += 1;
        connection.last_activity = std::time::Instant::now();
        
        debug!("Received {} bytes from party {}", mock_message.len(), party_id);
        Ok(mock_message)
    }
    
    /// Get network statistics
    pub async fn get_stats(&self) -> NetworkStats {
        let mut stats = self.stats.lock().await;
        
        // Update statistics
        let connections = self.connections.read().await;
        let active_count = connections.values()
            .filter(|c| matches!(c.state, ConnectionState::Active))
            .count() as u32;
        
        let total_rtt: u64 = connections.values()
            .map(|c| c.metrics.rtt_us)
            .sum();
        
        let avg_rtt = if active_count > 0 {
            total_rtt / active_count as u64
        } else {
            0
        };
        
        let total_bytes_sent: u64 = connections.values()
            .map(|c| c.metrics.bytes_sent)
            .sum();
        
        let total_errors: u64 = connections.values()
            .map(|c| c.metrics.error_count)
            .sum();
        
        let total_messages: u64 = connections.values()
            .map(|c| c.metrics.messages_sent + c.metrics.messages_received)
            .sum();
        
        let error_rate = if total_messages > 0 {
            (total_errors as f64 / total_messages as f64) * 100.0
        } else {
            0.0
        };
        
        stats.active_connections = active_count;
        stats.avg_rtt_us = avg_rtt;
        stats.throughput_bps = total_bytes_sent; // Simplified calculation
        stats.error_rate_percent = error_rate;
        stats.timestamp = chrono::Utc::now();
        
        stats.clone()
    }
    
    /// Check connection health
    pub async fn check_connection_health(&self) -> Result<Vec<HealthCheck>, Box<dyn std::error::Error + Send + Sync>> {
        debug!("Checking connection health for all parties");
        
        let connections = self.connections.read().await;
        let mut health_checks = Vec::new();
        
        for (party_id, connection) in connections.iter() {
            let is_healthy = matches!(connection.state, ConnectionState::Active) &&
                           connection.metrics.rtt_us < 10_000 && // 10ms threshold
                           connection.metrics.error_count < 10;
            
            health_checks.push(HealthCheck {
                party_id: *party_id,
                healthy: is_healthy,
                rtt_us: connection.metrics.rtt_us,
                error_count: connection.metrics.error_count,
                last_activity_secs_ago: connection.last_activity.elapsed().as_secs(),
            });
        }
        
        Ok(health_checks)
    }
    
    /// Shutdown network manager
    pub async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        info!("Shutting down network manager");
        
        let mut connections = self.connections.write().await;
        for (party_id, connection) in connections.iter_mut() {
            info!("Closing connection to party {}", party_id);
            connection.state = ConnectionState::Closed;
        }
        
        info!("Network manager shutdown complete");
        Ok(())
    }
}

/// Health check result for a party connection
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheck {
    /// Party identifier
    pub party_id: u32,
    /// Health status
    pub healthy: bool,
    /// Current round-trip time
    pub rtt_us: u64,
    /// Error count
    pub error_count: u64,
    /// Seconds since last activity
    pub last_activity_secs_ago: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{NetworkOptimization, TlsConfig};
    
    #[tokio::test]
    async fn test_network_manager_creation() {
        let mut party_addresses = HashMap::new();
        party_addresses.insert(0, "127.0.0.1:8001".to_string());
        party_addresses.insert(1, "127.0.0.1:8002".to_string());
        party_addresses.insert(2, "127.0.0.1:8003".to_string());
        
        let config = NetworkConfig {
            party_addresses,
            tls_config: TlsConfig {
                ca_cert_path: "/test/ca.pem".to_string(),
                client_cert_path: "/test/client.pem".to_string(),
                client_key_path: "/test/client-key.pem".to_string(),
                enable_mtls: true,
            },
            connection_timeout_ms: 5000,
            optimization: NetworkOptimization {
                tcp_nodelay: true,
                send_buffer_size: 65536,
                recv_buffer_size: 65536,
                max_connections_per_party: 10,
                enable_compression: false,
            },
        };
        
        let network_manager = NetworkManager::new(config).await;
        assert!(network_manager.is_ok());
    }
    
    #[tokio::test]
    async fn test_message_sending() {
        let mut party_addresses = HashMap::new();
        party_addresses.insert(0, "127.0.0.1:8001".to_string());
        party_addresses.insert(1, "127.0.0.1:8002".to_string());
        
        let config = NetworkConfig {
            party_addresses,
            tls_config: TlsConfig {
                ca_cert_path: "/test/ca.pem".to_string(),
                client_cert_path: "/test/client.pem".to_string(),
                client_key_path: "/test/client-key.pem".to_string(),
                enable_mtls: true,
            },
            connection_timeout_ms: 5000,
            optimization: NetworkOptimization {
                tcp_nodelay: true,
                send_buffer_size: 65536,
                recv_buffer_size: 65536,
                max_connections_per_party: 10,
                enable_compression: false,
            },
        };
        
        let network_manager = NetworkManager::new(config).await.unwrap();
        
        let message = b"test message";
        let result = network_manager.send_message(0, message).await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_broadcast_message() {
        let mut party_addresses = HashMap::new();
        party_addresses.insert(0, "127.0.0.1:8001".to_string());
        party_addresses.insert(1, "127.0.0.1:8002".to_string());
        party_addresses.insert(2, "127.0.0.1:8003".to_string());
        
        let config = NetworkConfig {
            party_addresses,
            tls_config: TlsConfig {
                ca_cert_path: "/test/ca.pem".to_string(),
                client_cert_path: "/test/client.pem".to_string(),
                client_key_path: "/test/client-key.pem".to_string(),
                enable_mtls: true,
            },
            connection_timeout_ms: 5000,
            optimization: NetworkOptimization {
                tcp_nodelay: true,
                send_buffer_size: 65536,
                recv_buffer_size: 65536,
                max_connections_per_party: 10,
                enable_compression: false,
            },
        };
        
        let network_manager = NetworkManager::new(config).await.unwrap();
        
        let message = b"broadcast test message";
        let result = network_manager.broadcast_message(message).await;
        assert!(result.is_ok());
        
        let successful_parties = result.unwrap();
        assert_eq!(successful_parties.len(), 3);
    }
    
    #[tokio::test]
    async fn test_connection_health_check() {
        let mut party_addresses = HashMap::new();
        party_addresses.insert(0, "127.0.0.1:8001".to_string());
        
        let config = NetworkConfig {
            party_addresses,
            tls_config: TlsConfig {
                ca_cert_path: "/test/ca.pem".to_string(),
                client_cert_path: "/test/client.pem".to_string(),
                client_key_path: "/test/client-key.pem".to_string(),
                enable_mtls: true,
            },
            connection_timeout_ms: 5000,
            optimization: NetworkOptimization {
                tcp_nodelay: true,
                send_buffer_size: 65536,
                recv_buffer_size: 65536,
                max_connections_per_party: 10,
                enable_compression: false,
            },
        };
        
        let network_manager = NetworkManager::new(config).await.unwrap();
        
        let health_checks = network_manager.check_connection_health().await.unwrap();
        assert_eq!(health_checks.len(), 1);
        assert!(health_checks[0].healthy);
    }
}
