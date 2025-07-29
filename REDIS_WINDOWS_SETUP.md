# Redis Setup for Windows - TRUST-FIRE Test Suite

This guide helps you install and configure Redis on Windows for running the TRUST-FIRE Phase 2 (Privacy Burn-Down) test.

## Option 1: Using Chocolatey (Recommended)

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

## Option 2: Manual Installation

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

## Option 3: Using Docker (Alternative)

If you have Docker installed:

```bash
docker run -d -p 6379:6379 redis:alpine
```

## Verify Installation

After installing Redis, verify it's working:

```bash
redis-cli ping
```

You should see: `PONG`

## Running Phase 2 Test

Once Redis is running, you can run the TRUST-FIRE Phase 2 test:

```bash
python tests/privacy/privacy_burn_down.py --tenant-id acme-beta
```

## Troubleshooting

### Redis CLI not found

- Ensure Redis is installed and in your PATH
- Try running: `redis-server --version`

### Connection refused

- Make sure Redis server is running
- Check if port 6379 is available
- Try: `netstat -an | findstr 6379`

### Permission denied

- Run Command Prompt as Administrator
- Check Windows Firewall settings

## Quick Test

Run the diagnostic script to check if Redis is working:

```bash
python test_broken_phases.py
```

If Redis is properly installed and running, Phase 2 should pass.

## Notes

- Redis server needs to be running before executing Phase 2 tests
- The test uses Redis to simulate epsilon budget tracking
- Redis data is temporary and will be cleared when the server stops
- For production use, consider using a persistent Redis configuration
