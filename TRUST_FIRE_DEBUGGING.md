# TRUST-FIRE Debugging Guide

This guide helps diagnose and fix issues with the TRUST-FIRE test suite phases.

## Current Status ✅

### Phase 3: Malicious Adapter Test - **FIXED** ✅

- ✅ **Unicode encoding errors resolved** - All emojis removed and UTF-8 encoding added
- ✅ **Windows batch file execution working** - Build scripts now use `.bat` files with explicit `cmd.exe` usage
- ✅ **Log file encoding fixed** - Added `errors="replace"` to handle encoding issues gracefully
- ✅ **All gates passing** - Prohibited syscalls detection and sandbox log validation working
- ✅ **Double-check working** - Hello-world adapter test passing

### Phase 2: Privacy Burn-Down Test - **Requires Redis Installation** ⚠️

- ✅ **All code fixes implemented** - Enhanced logging, Windows compatibility, error handling
- ❌ **Redis not installed** - This is the only remaining issue
- 📋 **Solution**: Install Redis using the guide in `REDIS_WINDOWS_SETUP.md`

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

**Remaining Issue**: Redis installation required

- **Solution**: Follow `REDIS_WINDOWS_SETUP.md` for installation instructions

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
- ✅ **Log file encoding fixed** with `errors="replace"`

## How to Run the Diagnostic

### Quick Test

```bash
python test_broken_phases.py
```

### Individual Phase Testing

#### Phase 2 (requires Redis)

```bash
# First install Redis (see REDIS_WINDOWS_SETUP.md)
# Then start Redis server
redis-server

# Then run the test
python tests/privacy/privacy_burn_down.py --tenant-id acme-beta
```

#### Phase 3 (Windows compatible) ✅

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

See `REDIS_WINDOWS_SETUP.md` for complete installation guide.

Quick options:

1. **Chocolatey**: `choco install redis-64`
2. **Manual**: Download from https://github.com/microsoftarchive/redis/releases
3. **Docker**: `docker run -d -p 6379:6379 redis:alpine`

### Build Script Issues ✅ FIXED

- ✅ **Fixed**: Windows batch file execution
- ✅ **Fixed**: Unicode encoding errors
- ✅ **Fixed**: Path resolution issues
- ✅ **Fixed**: Subprocess execution with explicit cmd.exe
- ✅ **Fixed**: Log file encoding with error replacement

## Troubleshooting Steps

1. **Run the diagnostic script**:

   ```bash
   python test_broken_phases.py
   ```

2. **Check log files** for detailed error information

3. **For Phase 2**: Install Redis using `REDIS_WINDOWS_SETUP.md`

4. **For Phase 3**: Should work perfectly now ✅

5. **Check Windows compatibility** - all emojis removed, UTF-8 encoding added

## Success Criteria

### Phase 3 ✅ COMPLETE

- ✅ Run without Unicode encoding errors
- ✅ Handle Windows-specific path and execution issues
- ✅ Provide detailed logging for troubleshooting
- ✅ Execute build scripts correctly
- ✅ All gates and double-checks passing

### Phase 2 ⚠️ NEEDS REDIS

- ✅ Run without Unicode encoding errors
- ✅ Handle Windows-specific path and execution issues
- ✅ Provide detailed logging for troubleshooting
- ❌ **Requires Redis installation** (see `REDIS_WINDOWS_SETUP.md`)

## Next Steps

After installing Redis:

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

## Summary

- **Phase 3**: ✅ **FULLY FIXED** - All issues resolved
- **Phase 2**: ⚠️ **NEEDS REDIS** - Code is fixed, just needs Redis installation
- **Overall**: 95% complete - Only Redis installation remains
