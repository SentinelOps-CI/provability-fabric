# Redis/Memurai Setup for Windows - TRUST-FIRE Test Suite

This guide helps you install and configure Redis or Memurai on Windows for running the TRUST-FIRE Phase 2 (Privacy Burn-Down) test.

## Option 1: Using Memurai (Recommended for Windows)

[Memurai](https://docs.memurai.com/) is a Redis-compatible server specifically designed for Windows.

### Installation

1. **Download Memurai**:

   - Visit: https://www.memurai.com/
   - Download the latest version for Windows

2. **Install Memurai**:

   - Run the downloaded installer
   - Follow the installation wizard
   - Memurai will be installed to `C:\Program Files\Memurai`

3. **Start Memurai Server**:

   ```cmd
   "C:\Program Files\Memurai\memurai.exe"
   ```

   Or if installed as a Windows service:

   ```cmd
   net start Memurai
   ```

### Configuration

Memurai uses the same configuration format as Redis. You can create a custom configuration file:

```cmd
# Create a config file
echo port 6379 > memurai.conf
echo bind 127.0.0.1 >> memurai.conf

# Start with custom config
"C:\Program Files\Memurai\memurai.exe" memurai.conf
```

### Verify Installation

After installing Memurai, verify it's working:

```bash
memurai-cli ping
```

You should see: `PONG`

## Option 2: Using Chocolatey (Redis)

1. **Install Chocolatey** (if not already installed):

   ```powershell
   Set-ExecutionPolicy Bypass -Scope Process -Force; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))
   ```

2. **Install Redis**:

   ```powershell
   choco install redis-64
   ```

3. **Start Redis Server**:
   ```powershell
   redis-server
   ```

## Option 3: Manual Redis Installation

1. **Download Redis for Windows**:

   - Visit: https://github.com/microsoftarchive/redis/releases
   - Download the latest release (e.g., `Redis-x64-3.0.504.msi`)

2. **Install Redis**:

   - Run the downloaded MSI file
   - Follow the installation wizard
   - Redis will be installed to `C:\Program Files\Redis`

3. **Start Redis Server**:
   ```cmd
   "C:\Program Files\Redis\redis-server.exe"
   ```

## Option 4: Using Docker (Alternative)

If you have Docker installed:

```bash
docker run -d -p 6379:6379 redis:alpine
```

## Verify Installation

After installing Redis or Memurai, verify it's working:

```bash
# For Redis
redis-cli ping

# For Memurai
memurai-cli ping
```

You should see: `PONG`

## Running Phase 2 Test

Once Redis/Memurai is running, you can run the TRUST-FIRE Phase 2 test:

```bash
python tests/privacy/privacy_burn_down.py --tenant-id acme-beta
```

## Troubleshooting

### Redis/Memurai CLI not found

- Ensure Redis or Memurai is installed and in your PATH
- Try running: `redis-server --version` or `memurai.exe --version`

### Connection refused

- Make sure Redis/Memurai server is running
- Check if port 6379 is available
- Try: `netstat -an | findstr 6379`

### Permission denied

- Run Command Prompt as Administrator
- Check Windows Firewall settings
- For Memurai: Ensure the service has proper permissions

### Memurai-specific issues

- **Service not starting**: Check Windows Event Log for Memurai service errors
- **Port conflicts**: Memurai defaults to port 6379, same as Redis
- **Configuration**: Memurai uses Redis-compatible configuration files

## Quick Test

Run the diagnostic script to check if Redis/Memurai is working:

```bash
python test_broken_phases.py
```

If Redis/Memurai is properly installed and running, Phase 2 should pass.

## Notes

- Redis/Memurai server needs to be running before executing Phase 2 tests
- The test uses Redis/Memurai to simulate epsilon budget tracking
- Redis/Memurai data is temporary and will be cleared when the server stops
- For production use, consider using a persistent Redis/Memurai configuration
- Memurai is specifically optimized for Windows environments
