# PF CI Reusable Workflow

This document describes the reusable PF CI workflow that runs TRUST-FIRE GA phases, builds runtime images, and validates results.

## Location

- Local reusable workflow: `.github/workflows/pf-ci.yaml`

## What it does

- Installs toolchains (Python, Go, Rust)
- Installs Kind, kubectl, and Helm
- Builds and loads images for:
  - `runtime/sidecar-watcher`
  - `runtime/admission-controller`
  - `runtime/ledger`
  - `runtime/attestor`
- Runs TRUST-FIRE GA subset (phases 2, 3, and 6 by default)
- Fails the job unless `trust-fire-report.json` contains `overall_status: PASS`

## Inputs

- `pr_number` (string, optional): PR number (for callers that need it)
- `run_phases` (string, optional, default `"2,3,6"`): Comma-separated phases to run
- `kind_cluster_name` (string, optional, default `"pf-ci"`): Kind cluster name

## Secrets

- `GITHUB_TOKEN` (optional): Used by some TRUST-FIRE steps
- `CI_PAT` (optional): PAT for cross-repo checkout, if needed

## Example usage (local)

```yaml
name: PF Reusable CI Caller
on:
  pull_request:
  schedule:
    - cron: "0 3 * * *"
jobs:
  call-pf-ci:
    uses: ./.github/workflows/pf-ci.yaml
    with:
      pr_number: ${{ github.event.pull_request.number || '' }}
      run_phases: "2,3,6"
    secrets:
      GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

## Cross-repo usage

Publish the reusable workflow to a central repository (e.g., `org/ci-workflows`) under `.github/workflows/pf-ci.yaml` and tag a version (e.g., `v1`). Then call it:

```yaml
name: Cross-Repo PF CI Consumer
on:
  pull_request:
  schedule:
    - cron: "0 3 * * *"
jobs:
  pf-ci:
    uses: org/ci-workflows/.github/workflows/pf-ci.yaml@v1
    with:
      pr_number: ${{ github.event.pull_request.number || '' }}
      run_phases: "2,3,6"
    secrets:
      GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

---

# Helm Chart: pf-enforce

**Path**: `charts/pf-enforce`

## Components
- MutatingWebhookConfiguration: Injects `sidecar-watcher` into pods labeled `pf/enforce=true`
- ValidatingWebhookConfiguration: Blocks pods lacking a valid PAB signature
- Admission controller Deployment + Service (HTTPS 8443)
- RBAC & ServiceAccount
- Sidecar ConfigMap (default sidecar JSON)

## Values

```yaml
image:
  sidecarWatcher:
    repository: provability-fabric/sidecar-watcher
    tag: latest
    pullPolicy: IfNotPresent
  admissionController:
    repository: provability-fabric/admission-controller
    tag: latest
    pullPolicy: IfNotPresent

webhooks:
  namespaceSelector: {}
  objectSelector:
    matchExpressions:
      - key: pf/enforce
        operator: In
        values: ["true"]
  timeouts:
    mutating: 10
    validating: 10
  failurePolicy: Fail

caBundle: ""

admission:
  replicaCount: 1
  service:
    type: ClusterIP
    port: 443
  tls:
    secretName: pf-enforce-certs
```

## Install

```bash
helm install pf-enforce charts/pf-enforce \
  --set caBundle=$(kubectl get cm -n kube-system extension-apiserver-authentication -o jsonpath='{.data.client-ca-file}' | base64 -w0)
```

Adjust `caBundle` to match your cluster’s CA.

---

# Makefile: PAB Signing Targets

Targets added:

- `pf-sign`: cosign keyless sign `bundles/<SERVICE_NAME>/bundle.json` and record `sigstore_digest`

```bash
make pf-sign SERVICE_NAME=my-service
```

- `pf-verify`: verify signature and run `pf verify`

```bash
make pf-verify SERVICE_NAME=my-service
```

---

# Service Bootstrap Template

**Path**: `templates/pf-bootstrap/pf.yaml`

Example:

```yaml
service: <service-name>
attestor:
  endpoint: http://attestor-service:8080
ledger:
  endpoint: http://ledger-service:4000
redis:
  url: redis://redis-master:6379

tools:
  http_fetch:
    allowlist:
      - https://api.example.com
      - https://*.trusted.com
```

Use as a starting point for new service repos.

