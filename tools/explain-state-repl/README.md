# Explain State REPL

Interactive tool for analyzing DFA states and transitions in real-time. This REPL allows developers to paste events and see how they affect the DFA state, including whether MonNI remains in the accept state.

## Features

- **Interactive Event Analysis**: Paste events and see immediate state transitions
- **MonNI Status Checking**: Verify if MonNI remains in accept state after events
- **Transition History**: Track all state changes with timestamps
- **DFA Visualization**: View all states and available transitions
- **JSON Export**: Export analysis results for CI integration

## Usage

### Starting the REPL

```bash
go run main.go
```

### Loading a DFA

```bash
explain-state> load artifact/dfa/example-dfa.json
✅ Loaded DFA with 5 states (initial: 0)
```

### Analyzing Events

```bash
explain-state> paste call api
📊 Event Analysis: 'call api'
   Current State: 0
   Next State: 1
   Is Accepting: true
   Actions: allow
   MonNI Status: ✅ MonNI remains in accept state
   ✅ State is accepting

explain-state> paste access sensitive_data
📊 Event Analysis: 'access sensitive_data'
   Current State: 1
   Next State: 2
   Is Accepting: false
   MonNI Status: ❌ MonNI is not in accept state
   ⚠️  State is not accepting
```

### Available Commands

- `help` - Show available commands
- `load <file>` - Load DFA from JSON file
- `paste <event>` - Analyze an event
- `reset` - Reset to initial state
- `status` - Show current state information
- `history` - Show transition history
- `states` - List all DFA states
- `transitions` - Show possible transitions from current state
- `monni` - Check MonNI acceptance status
- `json` - Export analysis as JSON
- `quit` - Exit the REPL

### Example Session

```
explain-state> load policies/security-dfa.json
✅ Loaded DFA with 8 states (initial: 0)

explain-state> status
📍 Current State: 0
   Type: intermediate
   Accepting: false
   Available transitions: 3

explain-state> paste user_login
📊 Event Analysis: 'user_login'
   Current State: 0
   Next State: 1
   Is Accepting: true
   Actions: authenticate
   MonNI Status: ✅ MonNI remains in accept state
   ✅ State is accepting

explain-state> paste access_database
📊 Event Analysis: 'access_database'
   Current State: 1
   Next State: 2
   Is Accepting: true
   Actions: allow, log
   MonNI Status: ✅ MonNI remains in accept state
   ✅ State is accepting

explain-state> paste admin_override
📊 Event Analysis: 'admin_override'
   Current State: 2
   Next State: 3
   Is Accepting: false
   MonNI Status: ❌ MonNI is not in accept state
   ⚠️  State is not accepting

explain-state> history
📜 Transition History:
  1. 'user_login': 0 → 1 ✅ (14:23:15)
  2. 'access_database': 1 → 2 ✅ (14:23:18)
  3. 'admin_override': 2 → 3 (14:23:22)

explain-state> monni
🔍 MonNI Status for current state 3: ❌ MonNI is not in accept state
```

## Integration with CI

The REPL can export analysis results in JSON format for CI integration:

```bash
explain-state> json
📄 JSON Export:
{
  "current_state": 3,
  "events": ["user_login", "access_database", "admin_override"],
  "history": [
    {
      "event": "user_login",
      "from_state": 0,
      "to_state": 1,
      "is_accepting": true,
      "timestamp": "2025-01-27T14:23:15Z"
    }
  ],
  "monni_status": "❌ MonNI is not in accept state",
  "exported_at": "2025-01-27T14:23:22Z"
}
```

## DFA File Format

The REPL expects DFA files in the following JSON format:

```json
{
  "states": {
    "0": {
      "id": 0,
      "is_accepting": false,
      "transitions": {
        "user_login": 1,
        "admin_login": 2
      },
      "metadata": {}
    },
    "1": {
      "id": 1,
      "is_accepting": true,
      "transitions": {
        "access_database": 3,
        "logout": 0
      },
      "metadata": {
        "actions": ["authenticate"]
      }
    }
  },
  "initial_state": 0,
  "event_set": {
    "user_login": true,
    "admin_login": true,
    "access_database": true,
    "logout": true
  },
  "compiled_at": "2025-01-27T14:00:00Z",
  "version": "1.0.0"
}
```

## Repository

Part of **[SentinelOps-CI/provability-fabric](https://github.com/SentinelOps-CI/provability-fabric)** (`tools/explain-state-repl/`). Clone: `git clone https://github.com/SentinelOps-CI/provability-fabric.git`.
