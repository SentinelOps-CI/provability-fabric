use std::env;
use std::path::PathBuf;

fn main() {
    // Check if we're building with Hyperscan support
    if cfg!(feature = "hyperscan") {
        build_hyperscan();
    }

    // Always rebuild if build script changes
    println!("cargo:rerun-if-changed=build.rs");
}

fn build_hyperscan() {
    // Try to find Hyperscan using pkg-config first
    if let Ok(library) = pkg_config::probe_library("libhyperscan") {
        for path in library.include_paths {
            println!("cargo:include={}", path.display());
        }
        return;
    }

    // Fallback: try to find Hyperscan in common locations
    let possible_paths = [
        "/usr/local/include",
        "/usr/include",
        "/opt/homebrew/include",            // macOS Homebrew
        "/usr/local/opt/hyperscan/include", // macOS Homebrew
    ];

    let mut found = false;
    for path in &possible_paths {
        if std::path::Path::new(path).exists() {
            println!("cargo:include={}", path);
            found = true;
            break;
        }
    }

    if !found {
        // If we can't find Hyperscan, try to build it from source
        build_hyperscan_from_source();
    }

    // Link against Hyperscan
    println!("cargo:rustc-link-lib=hyperscan");

    // Add runtime library path
    let possible_lib_paths = [
        "/usr/local/lib",
        "/usr/lib",
        "/usr/local/lib64",
        "/usr/lib64",
        "/opt/homebrew/lib",            // macOS Homebrew
        "/usr/local/opt/hyperscan/lib", // macOS Homebrew
    ];

    for path in &possible_lib_paths {
        if std::path::Path::new(path).exists() {
            println!("cargo:rustc-link-search=native={}", path);
            break;
        }
    }
}

fn build_hyperscan_from_source() {
    // This is a fallback for when Hyperscan is not installed
    // In production, you would typically install Hyperscan via package manager

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let hyperscan_dir = out_dir.join("hyperscan");

    // Clone Hyperscan if it doesn't exist
    if !hyperscan_dir.exists() {
        println!("cargo:warning=Hyperscan not found, attempting to build from source");
        println!("cargo:warning=This may take a while and requires CMake and a C++ compiler");

        // Note: In a real implementation, you would clone and build Hyperscan here
        // For now, we'll just warn the user
        println!("cargo:warning=Please install Hyperscan via package manager or build from source manually");
        println!("cargo:warning=Ubuntu/Debian: sudo apt-get install libhyperscan-dev");
        println!("cargo:warning=CentOS/RHEL: sudo yum install hyperscan-devel");
        println!("cargo:warning=macOS: brew install hyperscan");

        // Exit with error to prevent compilation
        std::process::exit(1);
    }
}
