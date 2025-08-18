# ActionDSL → DFA Export

This directory contains the compiled DFA tables exported from ActionDSL safety fragments.

## Files

- `dfa.json` - Canonical JSON export of the DFA table (RFC 8785 compliant)
- `dfa.sha256.txt` - SHA-256 hash of the canonical JSON for integrity verification
- `README.md` - This documentation file

## DFA Structure

The exported DFA follows the structure defined in `core/lean-libs/ActionDSL/Safety.lean`:

### States
Each state has:
- `id`: Unique state identifier
- `accepting`: Whether the state accepts traces

### Transitions
Each transition has:
- `from`: Source state ID
- `event`: Event string (e.g., "call(http_get,hash1)")
- `to`: Target state ID

### Rate Limiters
Each rate limiter has:
- `key`: Rate limiter identifier (tool name or egress path)
- `window`: Time window size in milliseconds
- `bound`: Maximum allowed count/bytes within the window
- `tolerance`: Clock tolerance (ε) for the window

## Usage

### CLI Export
```bash
cd core/lean-libs
lake exe ExportDFA --bundle bundles/my-agent --out artifact/dfa/dfa.json
```

### Verification
```bash
# Verify hash consistency
cd artifact/dfa
expected_hash=$(cat dfa.sha256.txt)
actual_hash=$(sha256sum dfa.json | cut -d' ' -f1)
if [ "$expected_hash" != "sha256:$actual_hash" ]; then
    echo "Hash mismatch!"
    exit 1
fi
```

## Properties

- **Prefix-closed**: DFA acceptance is prefix-closed
- **Deny-wins**: Any policy violation results in denial
- **ε-tolerance**: Rate limiting includes clock tolerance for robustness
- **Canonical**: JSON export follows RFC 8785 canonicalization

## CI Integration

The `.github/workflows/dfa.yaml` workflow ensures:
- DFA export changes only occur with Lean source changes
- SHA-256 hash verification passes
- Compilation completes within 180s time budget
- JSON schema validation passes

## Break Tests

To test the CI gates:
1. Modify a clause in `core/lean-libs/ActionDSL/Safety.lean`
2. Verify DFA export changes
3. CI should pass only when Lean source changes

## Regeneration Consistency

The export tool generates byte-identical results across multiple runs:
```bash
lake exe ExportDFA --bundle bundles/my-agent --out artifact/dfa/dfa1.json
lake exe ExportDFA --bundle bundles/my-agent --out artifact/dfa/dfa2.json
diff artifact/dfa/dfa1.json artifact/dfa/dfa2.json  # Should be identical
```
