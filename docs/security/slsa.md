# SLSA v1 Build Provenance

Provability-Fabric generates SLSA v1 build provenance for all OCI images to ensure supply chain security and verifiable builds.

## Overview

SLSA (Supply chain Levels for Software Artifacts) is a security framework that provides a way to secure the software supply chain. Provability-Fabric implements SLSA v1 provenance to ensure that all artifacts are built from verified source code in a secure, reproducible manner.

## Generated Artifacts

Each release includes the following SLSA v1 provenance files:

- `sidecar-watcher_provenance.intoto.jsonl` - Sidecar watcher image provenance
- `admission-controller_provenance.intoto.jsonl` - Admission controller image provenance
- `ledger_provenance.intoto.jsonl` - Ledger service image provenance
- `attestor_provenance.intoto.jsonl` - Attestor service image provenance

## Verification Commands

### Prerequisites

Install the required tools:

```bash
# Install cosign
curl -O -L "https://github.com/sigstore/cosign/releases/latest/download/cosign-linux-amd64"
chmod +x cosign-linux-amd64
sudo mv cosign-linux-amd64 /usr/local/bin/cosign

# Install gitsign (for key generation)
curl -O -L "https://github.com/sigstore/gitsign/releases/latest/download/gitsign-linux-amd64"
chmod +x gitsign-linux-amd64
sudo mv gitsign-linux-amd64 /usr/local/bin/gitsign
```

### Verify Provenance Files

Download the provenance files from the GitHub release and verify them:

```bash
# Download provenance files
wget https://github.com/provability-fabric/provability-fabric/releases/latest/download/slsa-provenance.intoto.jsonl

# Verify each provenance file
cosign verify-attestation --type slsaprovenance sidecar-watcher_provenance.intoto.jsonl
cosign verify-attestation --type slsaprovenance admission-controller_provenance.intoto.jsonl
cosign verify-attestation --type slsaprovenance ledger_provenance.intoto.jsonl
cosign verify-attestation --type slsaprovenance attestor_provenance.intoto.jsonl
```

### Verify Images with Provenance

Verify that the OCI images match their provenance:

```bash
# Pull the images
docker pull provability-fabric/sidecar-watcher:latest
docker pull provability-fabric/admission-controller:latest
docker pull provability-fabric/ledger:latest
docker pull provability-fabric/attestor:latest

# Verify images against provenance
cosign verify-attestation --type slsaprovenance provability-fabric/sidecar-watcher:latest
cosign verify-attestation --type slsaprovenance provability-fabric/admission-controller:latest
cosign verify-attestation --type slsaprovenance provability-fabric/ledger:latest
cosign verify-attestation --type slsaprovenance provability-fabric/attestor:latest
```

### Verify from Rekor Log

All provenance is automatically uploaded to the Rekor transparency log. Verify against the log:

```bash
# Verify provenance from Rekor
cosign verify-attestation --type slsaprovenance --rekor-url https://rekor.sigstore.dev sidecar-watcher_provenance.intoto.jsonl
```

## Provenance Structure

Each provenance file contains:

```json
{
  "_type": "https://in-toto.io/Statement/v1",
  "predicateType": "https://slsa.dev/provenance/v1",
  "predicate": {
    "buildDefinition": {
      "buildType": "https://github.com/provability-fabric/provability-fabric/actions/runs/{run_id}",
      "externalParameters": {
        "repository": "github.com/provability-fabric/provability-fabric",
        "ref": "refs/tags/v1.0.0",
        "sha1": "commit_hash"
      },
      "internalParameters": {
        "github_actor": "github_username",
        "github_event_name": "push"
      },
      "resolvedDependencies": [
        {
          "uri": "git+https://github.com/provability-fabric/provability-fabric",
          "digest": {
            "sha1": "commit_hash"
          }
        }
      ]
    },
    "runDetails": {
      "builder": {
        "id": "github.com/provability-fabric/provability-fabric/actions/runs/{run_id}"
      },
      "metadata": {
        "invocationId": "run_id",
        "startedOn": "2024-01-01T00:00:00Z",
        "finishedOn": "2024-01-01T00:05:00Z"
      }
    },
    "buildConfig": {
      "steps": [
        {
          "command": ["docker", "build"],
          "args": ["-t", "provability-fabric/sidecar-watcher:latest"]
        }
      ]
    }
  }
}
```

## Security Benefits

1. **Verifiable Builds**: All images are built from verified source code
2. **Reproducible**: Build process is documented and can be reproduced
3. **Tamper Evidence**: Any modification to the build process is detectable
4. **Transparency**: All provenance is logged in Rekor for public verification

## Integration with CI/CD

The SLSA provenance generation is integrated into the release workflow:

1. **Build Phase**: Images are built in a secure environment
2. **Provenance Generation**: SLSA v1 provenance is generated for each image
3. **Verification**: Provenance is verified against Rekor log
4. **Release**: Provenance files are uploaded to GitHub release

## Troubleshooting

### Common Issues

1. **Verification Fails**: Ensure you're using the correct cosign version
2. **Missing Files**: Check that provenance files were uploaded to the release
3. **Rekor Unavailable**: Use `--rekor-url` to specify alternative Rekor instance

### Debug Commands

```bash
# Inspect provenance content
cat sidecar-watcher_provenance.intoto.jsonl | jq '.'

# Check image digest
docker images --digests provability-fabric/sidecar-watcher

# Verify specific attestation
cosign verify-attestation --type slsaprovenance --key <(gitsign generate-key-pair --output-key-file /dev/stdout) provability-fabric/sidecar-watcher:latest
```

## Compliance

This SLSA implementation satisfies:

- **SLSA Level 2**: Provenance generation and verification
- **SLSA Level 3**: Reproducible builds and tamper evidence
- **EU AI Act**: Supply chain transparency requirements
- **NIST SSDF**: Software supply chain security practices

For more information, see the [SLSA specification](https://slsa.dev/spec/v1.0/provenance).
