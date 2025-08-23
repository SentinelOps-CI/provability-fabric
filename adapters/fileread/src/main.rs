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
use lib::{FileReadAdapter, FileReadEffect};

fn main() -> Result<(), Box<dyn Error>> {
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
        eprintln!("Usage: {} <file_path>", args[0]);
        process::exit(1);
    }

    let file_path = &args[1];

    // Create effect signature
    let effect_signature = FileReadEffect {
        allowed_paths: vec![
            "/tmp".to_string(),
            "/var/log".to_string(),
            "/proc".to_string(),
        ],
        max_file_size: 100 * 1024 * 1024, // 100MB max
        allowed_extensions: vec![],       // Allow all extensions for this example
        read_only: true,
        max_read_operations: 1000,
        timeout_ms: 30000,
        checksum_verification: true,
        symlink_following: false, // Security: don't follow symlinks
    };

    // Create adapter
    let mut adapter = match FileReadAdapter::new(effect_signature) {
        Ok(adapter) => adapter,
        Err(e) => {
            eprintln!("Failed to create adapter: {}", e);
            process::exit(1);
        }
    };

    // Execute file read
    match adapter.execute(file_path) {
        Ok(response) => {
            println!("File Read Response:");
            println!("File Size: {} bytes", response.file_size);
            println!("Checksum: {}", response.checksum);
            println!("Read Time: {}ms", response.read_time_ms);

            // Print file metadata
            println!("\nFile Metadata:");
            println!("Path: {}", response.file_metadata.path);
            println!("Inode: {}", response.file_metadata.inode);
            println!("Device: {}", response.file_metadata.device);
            println!("Permissions: {:o}", response.file_metadata.permissions);
            println!("Owner: {}", response.file_metadata.owner);
            println!("Group: {}", response.file_metadata.group);

            if let Some(created) = response.file_metadata.created {
                println!("Created: {}", created);
            }
            if let Some(modified) = response.file_metadata.modified {
                println!("Modified: {}", modified);
            }
            if let Some(accessed) = response.file_metadata.accessed {
                println!("Accessed: {}", accessed);
            }

            // Print security metadata
            println!("\nSecurity Metadata:");
            println!(
                "Path Resolved: {}",
                response.security_metadata.path_resolved
            );
            println!(
                "Symlink Count: {}",
                response.security_metadata.symlink_count
            );
            println!(
                "Hardlink Count: {}",
                response.security_metadata.hardlink_count
            );
            println!(
                "Read Timestamp: {}",
                response.security_metadata.read_timestamp
            );
            println!(
                "Access Pattern: {}",
                response.security_metadata.access_pattern
            );

            // Print file content (first 200 bytes)
            let content_preview = if response.content.len() > 200 {
                &response.content[..200]
            } else {
                &response.content
            };

            println!("\nContent Preview (first {} bytes):", content_preview.len());
            if let Ok(content_str) = String::from_utf8(content_preview.to_vec()) {
                println!("{}", content_str);
            } else {
                println!("[Binary content - {} bytes]", content_preview.len());
            }

            // Print adapter statistics
            let stats = adapter.get_stats();
            println!("\nAdapter Statistics:");
            for (key, value) in stats {
                println!("{}: {}", key, value);
            }
        }
        Err(e) => {
            eprintln!("File read failed: {}", e);
            process::exit(1);
        }
    }

    Ok(())
}
