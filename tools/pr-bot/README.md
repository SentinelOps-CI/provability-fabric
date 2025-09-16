# PR Bot

Automated GitHub PR bot that posts comprehensive analysis comments including proof compilation, automata information, epoch status, and sample replay statistics.

## Features

- **Proof Analysis**: Compiles policies and reports compilation status, timing, and hashes
- **Automata Information**: Analyzes DFA states, transitions, and event sets
- **Epoch Management**: Reports current epoch status and rotation information
- **Replay Statistics**: Runs sample replays and reports match percentages and drift detection
- **Rich Comments**: Generates detailed, formatted GitHub comments with emojis and structured data

## Usage

### Basic Usage

```bash
# Set GitHub token
export GITHUB_TOKEN=your_github_token

# Run PR bot
go run main.go owner repo pr-number
```

### Examples

```bash
# Analyze PR #123 in provability-fabric/provability-fabric
go run main.go provability-fabric provability-fabric 123

# With explicit token
go run main.go provability-fabric provability-fabric 123 ghp_xxxxxxxxxxxx
```

### CI Integration

Add to your GitHub Actions workflow:

```yaml
name: PR Analysis
on:
  pull_request:
    types: [opened, synchronize]

jobs:
  analyze:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Setup Go
        uses: actions/setup-go@v3
        with:
          go-version: 1.21
          
      - name: Install PR Bot
        run: go install github.com/provability-fabric/tools/pr-bot@latest
        
      - name: Run PR Analysis
        run: pr-bot ${{ github.repository_owner }} ${{ github.event.repository.name }} ${{ github.event.pull_request.number }}
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

## Generated Comment Format

The bot generates comprehensive comments with the following sections:

### 📊 Proof Compilation
- Compilation status (success/failed)
- Compile time in milliseconds
- Policy hash
- Automata hash

### 🤖 Automata Analysis
- Number of DFA states
- Number of transitions
- Number of accepting states
- Event types supported

### ⏰ Epoch Management
- Current epoch number
- Last rotation timestamp
- Rotation reason
- Number of active policies

### 🔄 Sample Replay Statistics
- Total replay runs attempted
- Number of successful runs
- Average match percentage
- Total execution time
- Drift detection status

## Configuration

The bot automatically discovers files in the repository:

### Policy Files
- `policy.md`
- `policies/*.md`
- `**/*.pfdsl`
- `**/*.dsl`

### DFA Files
- `artifact/dfa/*.json`
- `build/*/dfa.json`
- `**/dfa.json`

### Replay Files
- `*.replay.json`
- `replays/*.json`
- `**/*.replay.json`

## Dependencies

The bot requires the `so` CLI tool to be available in the PATH for running:
- `so policy compile`
- `so epoch status`
- `so replay run`

## Error Handling

The bot gracefully handles missing files and failed operations:
- Missing policy files result in "no_policy_found" status
- Failed proof compilation shows error status
- Missing replay files skip replay analysis
- API failures return default values where possible

## Security

- Uses GitHub's official API with OAuth2 authentication
- Requires appropriate repository permissions
- Respects GitHub rate limits
- No sensitive data is logged or exposed
