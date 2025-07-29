#![no_main]

use libfuzzer_sys::fuzz_target;
use sidecar_watcher::JsonProcessor;

fuzz_target!(|data: &[u8]| {
    // Convert bytes to string, ignore invalid UTF-8
    if let Ok(input) = std::str::from_utf8(data) {
        // Create processor with default limits
        let mut processor = JsonProcessor::new(300.0, 0.07);
        
        // Process the input - should not panic
        let _ = processor.process_json_line(input);
    }
});