/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use std::env;
use std::error::Error;
use std::process;

mod lib;
use lib::{HttpGetAdapter, HttpGetEffect};

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // Configure seccomp if enabled
    #[cfg(feature = "seccomp")]
    {
        if let Err(e) = lib::seccomp::configure_seccomp() {
            eprintln!("Failed to configure seccomp: {}", e);
            process::exit(1);
        }
    }
    
    // Parse command line arguments
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <url>", args[0]);
        process::exit(1);
    }
    
    let url = &args[1];
    
    // Create effect signature
    let effect_signature = HttpGetEffect {
        url: url.to_string(),
        method: "GET".to_string(),
        max_redirects: 0, // No redirects for security
        timeout_ms: 30000,
        max_content_length: 10 * 1024 * 1024, // 10MB max
        allowed_domains: vec![], // Allow all domains for this example
        user_agent: "ProvabilityFabric-HttpGet/1.0".to_string(),
    };
    
    // Create adapter
    let mut adapter = match HttpGetAdapter::new(effect_signature) {
        Ok(adapter) => adapter,
        Err(e) => {
            eprintln!("Failed to create adapter: {}", e);
            process::exit(1);
        }
    };
    
    // Execute request
    match adapter.execute(url).await {
        Ok(response) => {
            println!("HTTP Response:");
            println!("Status: {}", response.status_code);
            println!("Content Length: {:?}", response.content_length);
            println!("Content Type: {:?}", response.content_type);
            println!("Final URL: {}", response.final_url);
            println!("Response Time: {}ms", response.response_time_ms);
            println!("Body (first 100 bytes): {}", 
                String::from_utf8_lossy(&response.body[..response.body.len().min(100)]));
            
            // Print security metadata
            println!("\nSecurity Metadata:");
            println!("DNS Resolved: {}", response.security_metadata.dns_resolved);
            println!("IP Address: {}", response.security_metadata.ip_address);
            println!("Request Timestamp: {}", response.security_metadata.request_timestamp);
            println!("Response Timestamp: {}", response.security_metadata.response_timestamp);
            
            // Print adapter statistics
            let stats = adapter.get_stats();
            println!("\nAdapter Statistics:");
            for (key, value) in stats {
                println!("{}: {}", key, value);
            }
        }
        Err(e) => {
            eprintln!("Request failed: {}", e);
            process::exit(1);
        }
    }
    
    Ok(())
}
