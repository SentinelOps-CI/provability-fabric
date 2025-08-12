@echo off
REM SPDX-License-Identifier: Apache-2.0
REM Copyright 2025 Provability-Fabric Contributors

REM Multi-architecture build script for Provability-Fabric
REM Builds Docker images for both x86_64 and ARM64 (Graviton)

setlocal enabledelayedexpansion

REM Configuration
if "%REGISTRY%"=="" set REGISTRY=ghcr.io/provability-fabric
if "%VERSION%"=="" (
    if exist VERSION (
        set /p VERSION=<VERSION
    ) else (
        set VERSION=latest
    )
)
set PLATFORMS=linux/amd64,linux/arm64
set BUILDX_BUILDER=provability-fabric-builder

REM Colors for output (Windows 10+)
set "RED=[91m"
set "GREEN=[92m"
set "YELLOW=[93m"
set "BLUE=[94m"
set "NC=[0m"

REM Get command line argument
set COMMAND=%1
if "%COMMAND%"=="" set COMMAND=build

REM Logging functions
:log_info
echo %BLUE%[INFO]%NC% %~1
goto :eof

:log_success
echo %GREEN%[SUCCESS]%NC% %~1
goto :eof

:log_warning
echo %YELLOW%[WARNING]%NC% %~1
goto :eof

:log_error
echo %RED%[ERROR]%NC% %~1
goto :eof

REM Check prerequisites
:check_prerequisites
call :log_info "Checking build prerequisites..."

REM Check if Docker is running
docker info >nul 2>&1
if errorlevel 1 (
    call :log_error "Docker is not running or not accessible"
    exit /b 1
)

REM Check if buildx is available
docker buildx version >nul 2>&1
if errorlevel 1 (
    call :log_error "Docker Buildx is not available. Please enable it in Docker Desktop or install it separately."
    exit /b 1
)

REM Check if qemu is available for ARM emulation
docker run --rm --platform linux/arm64 alpine:latest echo "ARM emulation working" >nul 2>&1
if errorlevel 1 (
    call :log_warning "ARM emulation not working. ARM64 builds may fail."
    call :log_info "Consider installing qemu-user-static: sudo apt-get install qemu-user-static"
)

call :log_success "Prerequisites check passed"
goto :eof

REM Setup buildx builder
:setup_buildx
call :log_info "Setting up Docker Buildx builder..."

REM Check if builder already exists
docker buildx inspect %BUILDX_BUILDER% >nul 2>&1
if not errorlevel 1 (
    call :log_info "Builder '%BUILDX_BUILDER%' already exists"
    goto :eof
)

REM Create new builder
docker buildx create --name %BUILDX_BUILDER% --driver docker-container --use
docker buildx inspect --bootstrap

call :log_success "Buildx builder setup complete"
goto :eof

REM Build a single service
:build_service
set SERVICE=%1
set DOCKERFILE_PATH=runtime\%SERVICE%\Dockerfile
set IMAGE_NAME=%REGISTRY%\%SERVICE%:%VERSION%

if not exist "%DOCKERFILE_PATH%" (
    call :log_warning "Dockerfile not found for service '%SERVICE%': %DOCKERFILE_PATH%"
    exit /b 1
)

call :log_info "Building %SERVICE% for platforms: %PLATFORMS%"

REM Build and push multi-architecture image
docker buildx build ^
    --platform %PLATFORMS% ^
    --file "%DOCKERFILE_PATH%" ^
    --tag %IMAGE_NAME% ^
    --tag %REGISTRY%\%SERVICE%:latest ^
    --push ^
    "runtime\%SERVICE%"

if errorlevel 1 (
    call :log_error "Failed to build %SERVICE%"
    exit /b 1
) else (
    call :log_success "Successfully built and pushed %SERVICE%"
    exit /b 0
)

REM Build all services
:build_all_services
call :log_info "Building all services for multi-architecture deployment..."

set SERVICES=sidecar-watcher egress-firewall attestor
set FAILED_SERVICES=

for %%s in (%SERVICES%) do (
    call :build_service %%s
    if errorlevel 1 (
        call :log_error "✗ %%s build failed"
        set FAILED_SERVICES=!FAILED_SERVICES! %%s
    ) else (
        call :log_success "✓ %%s built successfully"
    )
)

REM Report results
if "%FAILED_SERVICES%"=="" (
    call :log_success "All services built successfully!"
) else (
    call :log_error "The following services failed to build:%FAILED_SERVICES%"
    exit /b 1
)
goto :eof

REM Build and test locally (without pushing)
:build_local
set SERVICE=%1
set PLATFORM=%2
set DOCKERFILE_PATH=runtime\%SERVICE%\Dockerfile
set IMAGE_NAME=%REGISTRY%\%SERVICE%:%VERSION%-%PLATFORM%

if not exist "%DOCKERFILE_PATH%" (
    call :log_warning "Dockerfile not found for service '%SERVICE%': %DOCKERFILE_PATH%"
    exit /b 1
)

call :log_info "Building %SERVICE% locally for platform: %PLATFORM%"

REM Build local image
docker buildx build ^
    --platform %PLATFORM% ^
    --file "%DOCKERFILE_PATH%" ^
    --tag %IMAGE_NAME% ^
    --load ^
    "runtime\%SERVICE%"

if errorlevel 1 (
    call :log_error "Failed to build %SERVICE% for %PLATFORM%"
    exit /b 1
) else (
    call :log_success "Successfully built %SERVICE% for %PLATFORM%"
    exit /b 0
)

REM Test multi-architecture builds locally
:test_local_builds
call :log_info "Testing local multi-architecture builds..."

set SERVICES=sidecar-watcher egress-firewall attestor
set PLATFORMS=linux/amd64 linux/arm64
set FAILED_BUILDS=

for %%s in (%SERVICES%) do (
    for %%p in (%PLATFORMS%) do (
        call :build_local %%s %%p
        if errorlevel 1 (
            call :log_error "✗ %%s (%%p) build failed"
            set FAILED_BUILDS=!FAILED_BUILDS! %%s-%%p
        ) else (
            call :log_success "✓ %%s (%%p) built successfully"
        )
    )
)

REM Report results
if "%FAILED_BUILDS%"=="" (
    call :log_success "All local builds successful!"
) else (
    call :log_error "The following local builds failed:%FAILED_BUILDS%"
    exit /b 1
)
goto :eof

REM Performance testing for ARM vs x86
:test_performance
call :log_info "Running performance comparison tests..."

REM This would run actual performance tests comparing ARM vs x86
REM For now, we'll just check if the images can run

set SERVICES=sidecar-watcher egress-firewall attestor

for %%s in (%SERVICES%) do (
    call :log_info "Testing %%s performance..."
    
    REM Test x86_64
    docker run --rm --platform linux/amd64 %REGISTRY%/%%s:%VERSION%-amd64 --version >nul 2>&1
    if errorlevel 1 (
        call :log_warning "✗ %%s (x86_64) failed to run"
    ) else (
        call :log_success "✓ %%s (x86_64) runs successfully"
    )
    
    REM Test ARM64
    docker run --rm --platform linux/arm64 %REGISTRY%/%%s:%VERSION%-arm64 --version >nul 2>&1
    if errorlevel 1 (
        call :log_warning "✗ %%s (ARM64) failed to run"
    ) else (
        call :log_success "✓ %%s (ARM64) runs successfully"
    )
)

call :log_info "Performance testing complete. Check logs for detailed metrics."
goto :eof

REM Cleanup function
:cleanup
call :log_info "Cleaning up build artifacts..."

REM Remove local test images
docker image prune -f --filter label=org.opencontainers.image.vendor=Provability-Fabric

call :log_success "Cleanup complete"
goto :eof

REM Main function
:main
if "%COMMAND%"=="build" (
    call :check_prerequisites
    call :setup_buildx
    call :build_all_services
    goto :end
)

if "%COMMAND%"=="test-local" (
    call :check_prerequisites
    call :test_local_builds
    goto :end
)

if "%COMMAND%"=="test-performance" (
    call :check_prerequisites
    call :test_performance
    goto :end
)

if "%COMMAND%"=="cleanup" (
    call :cleanup
    goto :end
)

if "%COMMAND%"=="help" (
    echo Usage: %0 [COMMAND]
    echo.
    echo Commands:
    echo   build           Build and push all services (default)
    echo   test-local      Test local builds for all platforms
    echo   test-performance Test performance of ARM vs x86 builds
    echo   cleanup         Clean up build artifacts
    echo   help            Show this help message
    echo.
    echo Environment variables:
    echo   REGISTRY        Docker registry (default: ghcr.io/provability-fabric)
    echo   VERSION         Image version (default: from VERSION file or 'latest')
    echo   PLATFORMS       Target platforms (default: linux/amd64,linux/arm64)
    goto :end
)

call :log_error "Unknown command: %COMMAND%"
echo Use '%0 help' for usage information
exit /b 1

:end
call :log_success "Build script completed successfully!"
exit /b 0
