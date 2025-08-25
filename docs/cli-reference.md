# CLI Reference

This document provides comprehensive reference information for all command-line tools in the Provability-Fabric framework.

## Overview

The Provability-Fabric CLI (`pf`) provides a unified interface for managing agents, proofs, deployments, and system operations.

## Installation

### Prerequisites

- Go 1.21+
- Kubernetes cluster access
- Docker (for building images)

### Install CLI

```bash
# Install from source
go install github.com/provability-fabric/core/cli/cmd/pf@latest

# Or download pre-built binary
curl -L https://github.com/provability-fabric/provability-fabric/releases/latest/download/pf-cli-linux-amd64 -o pf
chmod +x pf
sudo mv pf /usr/local/bin/
```

### Verify Installation

```bash
pf --version
pf --help
```

## Global Options

All commands support these global options:

```bash
--config string        # Configuration file path
--debug               # Enable debug logging
--log-level string    # Log level (debug, info, warn, error)
--namespace string    # Kubernetes namespace
--kubeconfig string   # Path to kubeconfig file
--context string      # Kubernetes context
--timeout duration    # Command timeout
--output string       # Output format (json, yaml, table)
--quiet               # Suppress output except errors
```

## Core Commands

### Agent Management

#### `pf agent create`

Create a new agent specification.

```bash
pf agent create [NAME] [FLAGS]

# Examples
pf agent create text-generator --spec spec.yaml
pf agent create image-classifier --from-template image-classification
pf agent create --interactive

# Flags
--spec string         # Path to specification file
--from-template string # Use predefined template
--interactive         # Interactive creation mode
--output string       # Output format
--dry-run            # Show what would be created
```

#### `pf agent list`

List all agents.

```bash
pf agent list [FLAGS]

# Examples
pf agent list
pf agent list --namespace agents
pf agent list --output json
pf agent list --filter status=active

# Flags
--namespace string    # Filter by namespace
--filter string       # Filter by label
--output string       # Output format
--wide               # Show additional columns
```

#### `pf agent get`

Get detailed information about an agent.

```bash
pf agent get [NAME] [FLAGS]

# Examples
pf agent get text-generator
pf agent get text-generator --output yaml
pf agent get text-generator --show-proofs

# Flags
--output string       # Output format
--show-proofs         # Include proof information
--show-deployments    # Include deployment information
--show-metrics        # Include performance metrics
```

#### `pf agent update`

Update an existing agent.

```bash
pf agent update [NAME] [FLAGS]

# Examples
pf agent update text-generator --spec new-spec.yaml
pf agent update text-generator --set version=2.0.0
pf agent update text-generator --patch '{"spec":{"replicas":5}}'

# Flags
--spec string         # Path to new specification
--set string          # Set individual fields
--patch string        # JSON patch for updates
--dry-run            # Show what would be updated
```

#### `pf agent delete`

Delete an agent and its resources.

```bash
pf agent delete [NAME] [FLAGS]

# Examples
pf agent delete text-generator
pf agent delete text-generator --force
pf agent delete text-generator --cascade

# Flags
--force              # Force deletion without confirmation
--cascade            # Delete dependent resources
--dry-run            # Show what would be deleted
```

### Proof Management

#### `pf proof create`

Create a new proof for an agent.

```bash
pf proof create [NAME] [FLAGS]

# Examples
pf proof create behavior-verification --agent text-generator --type lean
pf proof create accuracy-guarantee --agent image-classifier --type marabou
pf proof create --from-file proof.lean

# Flags
--agent string        # Agent name
--type string         # Proof type (lean, marabou, dryvr)
--from-file string    # Path to proof file
--description string  # Proof description
--tags strings        # Proof tags
```

#### `pf proof verify`

Verify a proof.

```bash
pf proof verify [NAME] [FLAGS]

# Examples
pf proof verify behavior-verification
pf proof verify behavior-verification --timeout 300s
pf proof verify --all --agent text-generator

# Flags
--agent string        # Agent name
--all                # Verify all proofs for agent
--timeout duration   # Verification timeout
--output string      # Output format
--verbose            # Show detailed output
```

#### `pf proof list`

List all proofs.

```bash
pf proof list [FLAGS]

# Examples
pf proof list
pf proof list --agent text-generator
pf proof list --type lean
pf proof list --status verified

# Flags
--agent string        # Filter by agent
--type string         # Filter by type
--status string       # Filter by status
--output string       # Output format
```

### Deployment Management

#### `pf deploy`

Deploy an agent to a cluster.

```bash
pf deploy [AGENT] [FLAGS]

# Examples
pf deploy text-generator
pf deploy text-generator --environment production
pf deploy text-generator --replicas 5
pf deploy text-generator --dry-run

# Flags
--environment string  # Deployment environment
--replicas int       # Number of replicas
--namespace string   # Target namespace
--dry-run            # Show what would be deployed
--wait               # Wait for deployment to complete
```

#### `pf deployment list`

List all deployments.

```bash
pf deployment list [FLAGS]

# Examples
pf deployment list
pf deployment list --agent text-generator
pf deployment list --environment production
pf deployment list --output json

# Flags
--agent string        # Filter by agent
--environment string  # Filter by environment
--output string       # Output format
--wide               # Show additional columns
```

#### `pf deployment get`

Get deployment details.

```bash
pf deployment get [NAME] [FLAGS]

# Examples
pf deployment get text-generator-prod
pf deployment get text-generator-prod --show-pods
pf deployment get text-generator-prod --show-logs

# Flags
--show-pods          # Show pod information
--show-logs          # Show recent logs
--output string      # Output format
```

#### `pf deployment scale`

Scale a deployment.

```bash
pf deployment scale [NAME] [REPLICAS] [FLAGS]

# Examples
pf deployment scale text-generator-prod 5
pf deployment scale text-generator-prod 0 --suspend

# Flags
--suspend            # Suspend deployment
--resume             # Resume suspended deployment
--dry-run            # Show what would be scaled
```

#### `pf deployment rollback`

Rollback a deployment.

```bash
pf deployment rollback [NAME] [FLAGS]

# Examples
pf deployment rollback text-generator-prod
pf deployment rollback text-generator-prod --to-revision 2

# Flags
--to-revision int    # Rollback to specific revision
--dry-run            # Show what would be rolled back
```

### Verification Commands

#### `pf verify`

Verify agent specifications and proofs.

```bash
pf verify [TARGET] [FLAGS]

# Examples
pf verify text-generator
pf verify --all
pf verify --spec spec.yaml
pf verify --proofs-only

# Flags
--all                # Verify all agents
--spec string        # Verify specification file
--proofs-only        # Only verify proofs
--timeout duration   # Verification timeout
--output string      # Output format
```

#### `pf validate`

Validate configuration and specifications.

```bash
pf validate [TARGET] [FLAGS]

# Examples
pf validate spec.yaml
pf validate --all-specs
pf validate --config config.yaml

# Flags
--all-specs          # Validate all specifications
--config string      # Configuration file to validate
--output string      # Output format
--strict             # Strict validation mode
```

### Monitoring Commands

#### `pf monitor`

Monitor agent and system status.

```bash
pf monitor [TARGET] [FLAGS]

# Examples
pf monitor text-generator
pf monitor --all
pf monitor --watch
pf monitor --metrics

# Flags
--all                # Monitor all agents
--watch              # Watch for changes
--metrics            # Show performance metrics
--output string      # Output format
--interval duration  # Update interval
```

#### `pf logs`

View agent and system logs.

```bash
pf logs [TARGET] [FLAGS]

# Examples
pf logs text-generator
pf logs text-generator --follow
pf logs text-generator --since 1h
pf logs text-generator --tail 100

# Flags
--follow             # Follow log output
--since string       # Show logs since time
--tail int           # Number of lines to show
--container string   # Container name
--previous           # Show previous container logs
```

#### `pf metrics`

View performance metrics.

```bash
pf metrics [TARGET] [FLAGS]

# Examples
pf metrics text-generator
pf metrics --all
pf metrics --time-range 1h
pf metrics --export prometheus

# Flags
--all                # Show all metrics
--time-range string  # Time range for metrics
--export string      # Export format
--output string      # Output format
```

### System Commands

#### `pf init`

Initialize a new Provability-Fabric project.

```bash
pf init [NAME] [FLAGS]

# Examples
pf init my-agent
pf init my-agent --template basic
pf init my-agent --interactive

# Flags
--template string     # Project template
--interactive         # Interactive mode
--output-dir string   # Output directory
--force              # Overwrite existing directory
```

#### `pf status`

Show system status.

```bash
pf status [FLAGS]

# Examples
pf status
pf status --detailed
pf status --output json

# Flags
--detailed           # Show detailed status
--output string      # Output format
--namespace string   # Specific namespace
```

#### `pf health`

Check system health.

```bash
pf health [FLAGS]

# Examples
pf health
pf health --agent text-generator
pf health --detailed

# Flags
--agent string        # Check specific agent
--detailed           # Show detailed health info
--output string      # Output format
```

#### `pf config`

Manage configuration.

```bash
pf config [COMMAND] [FLAGS]

# Subcommands
pf config get         # Get configuration value
pf config set         # Set configuration value
pf config list        # List configuration
pf config validate    # Validate configuration
pf config export      # Export configuration
pf config import      # Import configuration

# Examples
pf config get api.endpoint
pf config set api.endpoint https://api.example.com
pf config list
pf config export config.yaml
```

### Utility Commands

#### `pf completion`

Generate shell completion scripts.

```bash
pf completion [SHELL] [FLAGS]

# Examples
pf completion bash
pf completion zsh
pf completion fish

# Install bash completion
pf completion bash > ~/.local/share/bash-completion/completions/pf
source ~/.local/share/bash-completion/completions/pf
```

#### `pf version`

Show version information.

```bash
pf version [FLAGS]

# Examples
pf version
pf version --short
pf version --json

# Flags
--short              # Show short version
--json               # JSON output format
```

#### `pf help`

Show help information.

```bash
pf help [COMMAND]

# Examples
pf help
pf help agent create
pf help --all
```

## Configuration

### Configuration File

The CLI uses a configuration file for persistent settings:

```yaml
# ~/.config/provability-fabric/config.yaml
api:
  endpoint: "https://api.provability-fabric.org"
  timeout: "30s"
  retries: 3

kubernetes:
  context: "default"
  namespace: "provability-fabric"
  kubeconfig: "~/.kube/config"

logging:
  level: "info"
  format: "text"
  output: "stderr"

verification:
  lean_timeout: "300s"
  marabou_timeout: "600s"
  dryvr_timeout: "900s"

templates:
  default: "basic"
  directory: "~/.config/provability-fabric/templates"
```

### Environment Variables

The CLI also supports environment variables:

```bash
export PF_API_ENDPOINT="https://api.example.com"
export PF_KUBECONFIG="~/.kube/config"
export PF_LOG_LEVEL="debug"
export PF_NAMESPACE="my-namespace"
```

## Templates

### Available Templates

The CLI provides several project templates:

```bash
# List available templates
pf init --list-templates

# Available templates
basic              # Basic agent template
text-generation    # Text generation agent
image-classification # Image classification agent
multi-modal        # Multi-modal agent
financial          # Financial trading agent
```

### Custom Templates

Create custom templates:

```bash
# Create template directory
mkdir -p ~/.config/provability-fabric/templates/my-template

# Add template files
touch ~/.config/provability-fabric/templates/my-template/spec.yaml
touch ~/.config/provability-fabric/templates/my-template/README.md

# Use custom template
pf init my-agent --template my-template
```

## Output Formats

### JSON Output

```bash
pf agent list --output json
```

```json
{
  "agents": [
    {
      "name": "text-generator",
      "version": "1.0.0",
      "status": "active",
      "created_at": "2024-01-01T00:00:00Z"
    }
  ]
}
```

### YAML Output

```bash
pf agent get text-generator --output yaml
```

```yaml
name: text-generator
version: "1.0.0"
status: active
specification:
  capabilities:
    - name: text_generation
      constraints:
        max_length: 1000
created_at: "2024-01-01T00:00:00Z"
```

### Table Output

```bash
pf agent list --output table
```

```
NAME            VERSION    STATUS    CREATED
text-generator  1.0.0      active    2024-01-01
image-classifier 1.0.0     pending   2024-01-01
```

## Error Handling

### Common Errors

```bash
# Agent not found
Error: agent "unknown-agent" not found

# Invalid specification
Error: invalid specification: missing required field "name"

# Verification failed
Error: proof verification failed: timeout exceeded

# Permission denied
Error: permission denied: insufficient privileges
```

### Debug Mode

Enable debug mode for detailed error information:

```bash
pf --debug agent create test-agent --spec spec.yaml
```

### Error Codes

The CLI uses standard exit codes:

- `0` - Success
- `1` - General error
- `2` - Configuration error
- `3` - Validation error
- `4` - Verification error
- `5` - Permission error

## Scripting

### Shell Scripts

```bash
#!/bin/bash
# deploy-agent.sh

AGENT_NAME=$1
ENVIRONMENT=$2

if [ -z "$AGENT_NAME" ] || [ -z "$ENVIRONMENT" ]; then
    echo "Usage: $0 <agent-name> <environment>"
    exit 1
fi

# Deploy agent
pf deploy "$AGENT_NAME" --environment "$ENVIRONMENT" --wait

# Verify deployment
pf deployment get "$AGENT_NAME-$ENVIRONMENT" --show-pods

# Monitor health
pf health --agent "$AGENT_NAME"
```

### Python Integration

```python
import subprocess
import json

def run_pf_command(command):
    """Run a pf command and return JSON output"""
    result = subprocess.run(
        ['pf'] + command + ['--output', 'json'],
        capture_output=True,
        text=True
    )
    
    if result.returncode != 0:
        raise RuntimeError(f"Command failed: {result.stderr}")
    
    return json.loads(result.stdout)

# Example usage
agents = run_pf_command(['agent', 'list'])
for agent in agents['agents']:
    print(f"Agent: {agent['name']}, Status: {agent['status']}")
```

## Best Practices

### Command Organization

1. **Use consistent naming** - Follow established patterns
2. **Group related commands** - Use subcommands for organization
3. **Provide clear help** - Include examples and descriptions
4. **Support multiple outputs** - JSON, YAML, and table formats

### Error Handling

1. **Clear error messages** - Explain what went wrong
2. **Actionable advice** - Suggest how to fix issues
3. **Consistent exit codes** - Use standard exit codes
4. **Debug information** - Provide details in debug mode

### Performance

1. **Efficient queries** - Minimize API calls
2. **Caching** - Cache frequently accessed data
3. **Parallel operations** - Use goroutines for concurrent tasks
4. **Resource limits** - Respect system constraints

## Conclusion

The Provability-Fabric CLI provides a comprehensive interface for managing all aspects of the framework. Key features include:

- **Unified interface** - Single tool for all operations
- **Multiple output formats** - JSON, YAML, and table
- **Template system** - Pre-built project templates
- **Comprehensive help** - Built-in documentation
- **Scripting support** - Easy integration with automation

For more information about specific commands, use `pf help [COMMAND]` or refer to the relevant documentation sections.
