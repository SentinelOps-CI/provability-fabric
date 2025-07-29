# TRUST-FIRE Debugging Guide

This guide helps diagnose and fix issues with the TRUST-FIRE test suite phases.

## Issues Identified and Fixed

### Phase 2: Privacy Burn-Down Test

**Problem**: `redis.exceptions.ConnectionError: Error 10061 connecting to localhost:6379`

**Root Cause**: Redis server not running on Windows

**Solutions Implemented**:

- ✅ **Enhanced Redis connection logging** with detailed error messages
- ✅ **Step-by-step epsilon consumption tracking**
- ✅ **Guard trip validation logging**
- ✅ **DSAR export process logging**
- ✅ **Triple-check validation logging**
- ✅ **Comprehensive error handling** with helpful troubleshooting messages
- ✅ **Windows-compatible logging** with UTF-8 encoding
- ✅ **Removed emoji characters** for Windows console compatibility

### Phase 3: Malicious Adapter Test

**Problem**: `[WinError 193] %1 is not a valid Win32 application` and `UnicodeEncodeError`

**Root Cause**:

1. Trying to execute Unix shell script on Windows
2. Windows console encoding issues with Unicode emojis

**Solutions Implemented**:

- ✅ **Platform-specific build scripts** (`.bat` for Windows, `.sh` for Unix)
- ✅ **Windows-compatible subprocess execution** with explicit `cmd.exe` usage
- ✅ **UTF-8 encoding handling** with error replacement
- ✅ **Enhanced error handling** for missing interpreters
- ✅ **Detailed build process logging**
- ✅ **File system operations tracking**
- ✅ **Removed emoji characters** for Windows compatibility
- ✅ **Absolute path usage** for better Windows compatibility

## How to Run the Diagnostic

### Quick Test

```bash
python test_broken_phases.py
```

### Individual Phase Testing

#### Phase 2 (requires Redis)

```bash
# Start Redis first
redis-server

# Then run the test
python tests/privacy/privacy_burn_down.py --tenant-id acme-beta
```

#### Phase 3 (Windows compatible)

```bash
python tests/security/malicious_adapter_test.py --registry-path registry --wasm-sandbox-path runtime/wasm-sandbox
```

## Enhanced Logging Features

### Phase 2 Logging:

- Redis connection attempts and failures
- Epsilon consumption simulation details
- Guard trip creation and validation
- DSAR export file creation
- Triple-check validation processes
- Windows-compatible UTF-8 encoding

### Phase 3 Logging:

- Platform detection and compatibility
- Build script creation (Windows vs Unix)
- Subprocess execution details with explicit cmd.exe usage
- File system operations
- WASM file validation
- Unicode encoding error handling

## Expected Results

The enhanced logging will now provide detailed information about:

- **Redis connection status** and troubleshooting steps
- **Build process details** with platform-specific handling
- **File creation and validation** steps
- **Error conditions** with specific solutions
- **Success/failure points** with clear indicators

## Log Files Created

- `privacy_burn_down.log` - Detailed Redis and epsilon operations
- `malicious_adapter_test.log` - Build process and platform operations
- `test_broken_phases.log` - Diagnostic script output

## Windows-Specific Solutions

### Redis Installation

1. **Download Redis for Windows**:

   - https://github.com/microsoftarchive/redis/releases
   - Or use Chocolatey: `choco install redis-64`

2. **Start Redis Server**:

   ```bash
   redis-server
   ```

3. **Or use Docker**:
   ```bash
   docker run -d -p 6379:6379 redis:alpine
   ```

### Build Script Issues

- ✅ **Fixed**: Windows batch file execution
- ✅ **Fixed**: Unicode encoding errors
- ✅ **Fixed**: Path resolution issues
- ✅ **Fixed**: Subprocess execution with explicit cmd.exe

## Troubleshooting Steps

1. **Run the diagnostic script**:

   ```bash
   python test_broken_phases.py
   ```

2. **Check log files** for detailed error information

3. **Verify Redis is running**:

   ```bash
   redis-cli ping
   ```

4. **Test individual phases** with the commands above

5. **Check Windows compatibility** - all emojis removed, UTF-8 encoding added

## Success Criteria

Both phases should now:

- ✅ Run without Unicode encoding errors
- ✅ Handle Windows-specific path and execution issues
- ✅ Provide detailed logging for troubleshooting
- ✅ Work with proper Redis setup (Phase 2)
- ✅ Execute build scripts correctly (Phase 3)

## Next Steps

After fixing the issues:

1. Run the complete TRUST-FIRE suite:

   ```bash
   python tests/trust_fire_orchestrator.py
   ```

2. Or run individual phases as shown above

3. Check the GitHub Actions workflow:
   ```bash
   # The workflow will run all phases automatically
   # Check .github/workflows/trust-fire-ga-test.yaml
   ```
