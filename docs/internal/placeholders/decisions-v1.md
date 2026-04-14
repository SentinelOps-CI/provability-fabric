# Decisions: Placeholder/Stub Scope for v1

These answers are intended to create clear instructions for working on the items in [inventory.md](inventory.md). Each question is answered with a recommended decision and short rationale based on the current repo.

---

## 1. KMS/Vault scope

**Recommended for v1:** File backend + documented plugin interface + one real provider (e.g. file only in-repo; KMS/Vault as documented integration points).

**Rationale:** The signing rotation doc already describes a pluggable signer (`CERT_SIGNER_BACKEND=file|kms|vault`) and the evidence-service has a real file (Ed25519 PEM) implementation. Shipping real AWS KMS and Vault Transit in-repo would pull in provider SDKs, credentials handling, and env/region wiring for all users. Defining a clear Signer interface and documenting how to implement it for KMS/Vault (and optionally shipping one reference provider, e.g. file) keeps the core simple and lets operators plug their own KMS/Vault. So: **v1 = file backend + documented plugin interface; no requirement for in-repo KMS/Vault implementations.**

---

## 2. Canonical bundle format (bundle hash)

**Recommended:** Bundle hash = **hash(bundle file bytes)** (e.g. hash of the tar.gz as a single blob). Optionally document or add a second identifier (e.g. manifest-of-digests) later if needed for streaming/partial updates.

**Rationale:** Today `calculateBundleHash` in `core/cli/pf/main.go` hashes the bundle file directly: it opens the path and does `io.Copy` into SHA256. So the canonical behavior is already “hash of the serialized bundle file.” A manifest-of-digests would enable different tradeoffs (e.g. streaming, partial updates) but is a separate format; for v1, **define bundle hash as hash(bundle file bytes)** and fix the one remaining “placeholder-hash” in fixture recording to use this same function (or equivalent) so it’s consistent.

---

## 3. DSSE everywhere?

**Recommended:** **Receipts and CERT-style signatures: DSSE.** Revocations and policy packs: **not required to be DSSE for v1**; document current format and add DSSE later if we want a single envelope story.

**Rationale:** Retrieval-gateway receipts and sidecar CERT/signature handling already use or expect DSSE (e.g. `validate_dsse_signature`, payloadType binding). Using DSSE for receipts and CERTs gives a clear “payloadType + signatures” story. Revocations and policy packs are not uniformly DSSE today; making them DSSE would be an intentional format choice with extra overhead. So: **v1 = DSSE for receipts and CERT/signing; revocations and policy packs keep current format unless we explicitly decide to standardize them on DSSE** (then do it in a follow-up).

---

## 4. SWE-bench runner when OpenHands isn’t installed

**Recommended:** **(b) Run evidence pipeline only, with explicit “solver disabled” mode (no patch).** Do not hard-fail when OpenHands is missing.

**Rationale:** The runner already behaves like (b): if the openhands engine isn’t available or workspace/task are missing, it emits a stub patch and still runs the rest of the pipeline (evidence, replay bundle, policy hash, proof hook, cost report, PF metadata sidecar). That supports environments where OpenHands isn’t installed (e.g. Windows, CI without solver). For v1, **formalize this as “solver disabled” mode**: when the solver is unavailable or not configured, log clearly that the solver is disabled, emit no-patch or stub patch, and still run and emit all evidence artifacts. Optionally add a flag (e.g. `--solver-required`) for flows that want to hard-fail when no solver is present.

---

## 5. Lean expectation (sorry / by admit)

**Recommended:** **Zero sorry in CI-enforced Lean targets only.** Allow research or experimental proofs in other dirs if they are excluded from the required build and from the sorry check.

**Rationale:** Current CI (lean-style.yaml, lean-offline.yaml) runs `find . -name "*.lean"` and fails on any `sorry` or `by admit`, so today it’s effectively “zero sorry anywhere in the repo.” The same workflows only build a fixed set of projects (e.g. core/lean-libs, spec-templates, my-agent, test-new-user-agent). For v1, **define “CI-enforced Lean targets”** (the list of dirs/projects that must build and must not contain sorry) and restrict the sorry check to those paths (e.g. only under `core/lean-libs`, `spec-templates/`, `bundles/*/proofs`). Research or one-off proofs can live in other directories (e.g. `proofs/`, `experiments/`) and be excluded from the required check so long as they are not part of the CI-built set.

---

## 6. Docs/scripts placeholders (Slack webhook, tokens, etc.)

**Recommended:** **Keep sanitized examples in docs/scripts, but make them clearly variable-based.** Do not require “no placeholders anywhere”; require that examples use obvious placeholders (e.g. `SLACK_WEBHOOK_URL`, `ghp_xxx`) plus a one-line explanation that they must be replaced with real values or env vars.

**Rationale:** Sanitized examples (e.g. `https://hooks.slack.com/services/xxx/yyy/zzz`, `ghp_xxxxxxxxxxxx`) are useful for copy-paste and showing shape. Removing them entirely would make some docs harder to follow. So: **allow dummy tokens in examples**, but (a) use a consistent style (e.g. `xxx`, `your-token-here`), and (b) add a short note that these are placeholders and must be replaced with real values or environment variables. No need to remove every example placeholder; avoid real-looking secrets and document the substitution clearly.

---

## 7. DSSE trust root distribution (receipts / CERT)

**Recommended for v1:** **(a) Static public key file** as the default: deployment ships with a public key (or path to it) and verifiers use it for DSSE. **(b) JWKS over HTTP** is optional: verifiers may be configured with a JWKS URL (e.g. from evidence-service, jwks-manager, or an IdP) and fetch keys for verification. **(c) Bundle includes public key / key-id mapping** is deferred.

**Rationale:** Evidence-service verify API already accepts either PEM (`pem_pub`) or JWKS URL (`jwks_url`) per request; the *caller* supplies the trust root. JWKS-validate CI uses `--jwks "$JWKS_URL"`. So verifiers (CLI, console, sidecar, middlewares) today get the root via config: static key file or JWKS URL. For v1: **default = (a)** so that deployments and offline CI can verify without a live HTTP endpoint; **(b)** remains supported when operators configure a JWKS URL (evidence-service does not have to *serve* JWKS; jwks-manager or an external IdP can). **(c)** (bundle carries key) is a later option for self-contained bundles once bundle format and distribution are fixed.

---

## 8. Authoritative source of expected digests (policy / automata / labeler) in sidecar-watcher

**Recommended for v1:** **(a) Bundle manifest produced by CLI.** The CLI (or bundle build step) emits a manifest that contains the expected policy_hash, automata_hash, and labeler_hash for that bundle. Sidecar-watcher loads expected digests from this manifest when running with that bundle. **(b) Policy pack metadata in repo** is not the v1 authority for the sidecar; **(c) Fetched from ledger** is out of scope for v1 (offline CI cannot depend on ledger).

**Rationale:** Sidecar currently reads POLICY_HASH, AUTOMATA_HASH, LABELER_HASH from env (permit_enforcement), i.e. deployment config. To support offline CI and a single source of truth: the **bundle** should carry the expected digests so that the same artifact built in CI is what the sidecar validates against. So v1: **CLI (or bundle pipeline) produces a manifest** (e.g. alongside or inside the bundle) with expected policy/automata/labeler digests; sidecar-watcher uses that manifest as the authoritative expected digests. Policy pack in repo can still be the input to *compute* those hashes when building the bundle; the sidecar's authority is the bundle manifest.

---

## 9. Plan signature verification in sidecar-watcher (strict vs dev mode)

**Recommended for v1:** **Enforce strict signature verification on plans by default (hard deny if missing or invalid).** Allow an explicit dev mode (e.g. `--insecure-dev` or env `SIDECAR_INSECURE_PLAN_SIG=1`) for local development only; **CI must never enable this mode** (CI runs without the flag so plan signatures are always required).

**Rationale:** Plan verification in `plan.rs` currently has a TODO for actual signature verification and only does structural checks. For v1: **default = strict**: if a plan is presented without a valid signature (once verification is implemented), the sidecar denies it. To unblock local dev without a full signing setup, support an explicit **insecure-dev** mode that (a) is clearly named and documented as "local dev only," (b) is disabled by default, and (c) is forbidden in CI (e.g. CI job fails if the flag or env is set, or sidecar refuses to start with the flag in production-like env). That keeps production and CI secure while allowing dev workflows.

---

## Summary table

| Topic | Decision for v1 |
|-------|-----------------|
| KMS/Vault | File backend + documented plugin interface; no in-repo KMS/Vault implementations required. |
| Bundle hash | Hash(bundle file bytes). Fix fixture “placeholder-hash” to use same definition. |
| DSSE | Receipts and CERT/signing: DSSE. Revocations and policy packs: current format; DSSE optional later. |
| SWE-bench no solver | Solver-disabled mode: run evidence pipeline, no real patch; optional `--solver-required` to hard-fail. |
| Lean sorry | Zero sorry only in CI-enforced Lean targets; exclude research/experimental proof dirs from check. |
| Docs/scripts placeholders | Keep sanitized examples; use variable-style placeholders + one-line “replace with real value” note. |
| **DSSE trust root** | Default: static public key file in deployment. Optional: verifiers configured with JWKS URL. Bundle-included key deferred. |
| **Expected digests (sidecar)** | Bundle manifest produced by CLI is authoritative (policy/automata/labeler hashes). Not ledger; policy pack in repo feeds manifest at build time. |
| **Plan signature (sidecar)** | Strict by default (hard deny if missing/invalid). Explicit `--insecure-dev` (or env) for local dev only; CI must not enable it. |
