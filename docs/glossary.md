# Glossary

This glossary defines key terms and concepts used throughout the Provability-Fabric framework and documentation.

## A

### Admission Controller
A Kubernetes component that intercepts requests to the API server before persistence, used to validate deployments and enforce policies.

### Agent
An AI system or service that performs specific tasks, bound to formal proofs that guarantee behavioral properties.

### Attestation
Cryptographic proof that a system or component is running in a trusted state, often involving hardware-level verification.

## B

### Bundle
A packaged collection containing agent specifications, proofs, and metadata, used for deployment and verification.

### Behavioral Guarantee
A formal mathematical guarantee that an agent will behave in a specified way under given conditions.

## C

### Capability
A specific function or operation that an agent can perform, defined with constraints and verification requirements.

### Constraint
A rule or limitation that restricts agent behavior, such as maximum response length or content filtering requirements.

### Container
A lightweight, isolated execution environment that packages an application and its dependencies.

## D

### Deployment
The process of installing and running an agent in a production environment with runtime monitoring.

### DryVR
A verification engine for hybrid systems that combines discrete and continuous dynamics.

## E

### Enclave
A secure, isolated execution environment that protects code and data from external access.

### Enforcement
The runtime mechanism that ensures agents adhere to their specified constraints and behavioral guarantees.

## F

### Formal Verification
Mathematical proof that a system satisfies specified properties, using formal methods and logic.

### Framework
The complete Provability-Fabric system that provides tools, libraries, and runtime components for creating verifiable AI agents.

## G

### GraphQL
A query language and runtime for APIs that provides a flexible way to request and manipulate data.

### Guarantee
A formal assurance that certain properties will hold, backed by mathematical proof.

## H

### Hybrid System
A system that combines discrete and continuous dynamics, requiring specialized verification approaches.

### HTTP
The Hypertext Transfer Protocol used for communication between web services and clients.

## I

### Integration
The process of connecting Provability-Fabric components with existing systems and infrastructure.

### Isolation
The separation of processes and resources to prevent interference and ensure security.

## J

### JWT
JSON Web Token, a compact, URL-safe means of representing claims between parties.

### Justification
Mathematical proof that demonstrates why a particular property or constraint holds.

## K

### Kubernetes
An open-source container orchestration platform for automating deployment, scaling, and management of containerized applications.

### Key Management
The secure generation, storage, distribution, and rotation of cryptographic keys.

## L

### Lean
A functional programming language and theorem prover used for formal verification and proof development.

### Ledger
An immutable record of all agent specifications, proofs, and verification status.

### Latency
The time delay between a request and response, measured in milliseconds or seconds.

## M

### Marabou
A verification engine for neural networks that can prove properties about their behavior.

### Metrics
Quantitative measurements of system performance, behavior, and health.

### Monitoring
Continuous observation of system behavior to detect issues and ensure compliance with specifications.

## N

### Neural Network
A machine learning model composed of interconnected nodes that can learn patterns from data.

### Non-interference
A security property ensuring that high-security operations cannot be influenced by low-security operations.

## O

### Observability
The ability to understand the internal state of a system based on its external outputs.

### Operator
A Kubernetes pattern for managing complex applications and their lifecycles.

## P

### Policy
A set of rules that govern agent behavior and enforce constraints at runtime.

### Proof
A mathematical demonstration that a particular property or constraint holds for an agent.

### Proof-of-Behaviour
A formal mathematical proof that demonstrates an agent's behavioral guarantees.

### Proof-Carrying Science (PCS)
A workflow for attaching verification evidence to scientific claims: certified bundles, release handoffs, artifact registries, and signed outputs suitable for downstream systems. See [PCS documentation](pcs/README.md) and the [PCS glossary](pcs/glossary.md).

### Provenance
The complete history and origin of data, code, and components in a system.

## Q

### Quality Gate
A checkpoint in the development process that ensures certain quality standards are met before proceeding.

### Quantification
The process of measuring and quantifying system properties and performance characteristics.

## R

### Rate Limiting
A mechanism that restricts the number of requests a client can make within a given time period.

### Resource
A system component such as CPU, memory, or storage that agents consume during operation.

### Runtime
The execution environment where agents run and are monitored for compliance with specifications.

### Rollback
The process of reverting a deployment to a previous version due to issues or failures.

## S

### SDK
Software Development Kit, a collection of tools and libraries for building applications.

### Security
Protection against unauthorized access, modification, or destruction of system resources and data.

### Sidecar
A container that runs alongside the main application container to provide additional functionality such as monitoring or logging.

### Specification
A formal description of an agent's behavior, capabilities, and constraints.

### Supply Chain
The complete path from source code to deployed application, including all dependencies and build processes.

## T

### Testing
The process of verifying that a system behaves correctly under various conditions and inputs.

### Throughput
The rate at which a system can process requests or operations, typically measured in operations per second.

### Transparency
The ability to inspect and verify all aspects of system behavior and decision-making.

### Trust
Confidence in a system's behavior based on formal verification and runtime enforcement.

## U

### Update
A new version of an agent or component that includes improvements, bug fixes, or new features.

### User
An individual or system that interacts with Provability-Fabric agents and services.

## V

### Verification
The process of checking that proofs are valid and that agents meet their specifications.

### Version
A specific release or iteration of software, identified by a version number.

### Vulnerability
A weakness in a system that could be exploited to cause harm or unauthorized access.

## W

### WASM
WebAssembly, a binary instruction format for web browsers and other environments.

### Webhook
A mechanism for real-time communication between systems using HTTP callbacks.

### Worker Pool
A collection of worker processes that can handle multiple tasks concurrently.

## X

### XML
Extensible Markup Language, a markup language used for data exchange and configuration.

## Y

### YAML
YAML Ain't Markup Language, a human-readable data serialization format used for configuration files.

## Z

### Zero Trust
A security model that assumes no implicit trust and requires verification for every access request.

## Technical Terms

### API
Application Programming Interface, a set of rules and protocols for building software applications.

### Authentication
The process of verifying the identity of a user or system.

### Authorization
The process of determining what actions a user or system is allowed to perform.

### Cache
A high-speed storage area that stores frequently accessed data for quick retrieval.

### Database
A structured collection of data that can be accessed, managed, and updated.

### Encryption
The process of encoding information to prevent unauthorized access.

### Firewall
A network security device that monitors and controls incoming and outgoing network traffic.

### Load Balancer
A device that distributes network traffic across multiple servers to ensure reliability and performance.

### Microservice
An architectural style where an application is built as a collection of small, independent services.

### Namespace
A way to organize and isolate resources in Kubernetes and other systems.

### Pod
The smallest deployable unit in Kubernetes, containing one or more containers.

### Replica
A copy of a pod that runs the same application for redundancy and scalability.

### Service
A Kubernetes resource that provides a stable endpoint for accessing a set of pods.

### Volume
A persistent storage location that can be attached to pods in Kubernetes.

## Mathematical Terms

### Theorem
A mathematical statement that has been proven to be true.

### Proof
A logical argument that demonstrates the truth of a theorem.

### Lemma
A smaller theorem used in the proof of a larger theorem.

### Corollary
A statement that follows directly from a theorem.

### Axiom
A statement that is accepted as true without proof.

### Predicate
A function that returns true or false based on its inputs.

### Quantifier
A logical operator that specifies the scope of a variable.

### Implication
A logical statement of the form "if P then Q".

### Conjunction
A logical AND operation between two statements.

### Disjunction
A logical OR operation between two statements.

### Negation
A logical NOT operation that inverts the truth value of a statement.

## Security Terms

### Confidentiality
The property that information is not disclosed to unauthorized individuals or systems.

### Integrity
The property that information has not been altered in an unauthorized manner.

### Availability
The property that information and systems are accessible when needed.

### Non-repudiation
The property that the origin of information cannot be denied by the sender.

### Audit Trail
A chronological record of system activities for security and compliance purposes.

### Threat Model
A structured approach to identifying and analyzing potential security threats to a system.

### Attack Vector
A path or means by which an attacker can gain access to a system.

### Vulnerability Assessment
The process of identifying and evaluating security vulnerabilities in a system.

### Penetration Testing
The practice of testing a system's security by simulating attacks.

### Security Policy
A set of rules and procedures that define how security is implemented in an organization.

## Performance Terms

### Benchmark
A standard test used to measure and compare system performance.

### Bottleneck
A component that limits the overall performance of a system.

### Cache Hit
A successful retrieval of data from cache memory.

### Cache Miss
An unsuccessful attempt to retrieve data from cache memory.

### Latency
The time delay between a request and response.

### Throughput
The rate at which a system can process requests or operations.

### Scalability
The ability of a system to handle increased load by adding resources.

### Reliability
The ability of a system to perform its functions correctly over time.

### Availability
The percentage of time a system is operational and accessible.

### Performance
The efficiency and speed with which a system performs its functions.

## Conclusion

This glossary provides definitions for the key terms and concepts used throughout the Provability-Fabric framework. For more detailed explanations, refer to the relevant documentation sections.

Terms are organized alphabetically and by category to help you quickly find the information you need. The glossary is regularly updated to reflect new concepts and terminology as the framework evolves.

---

## Bench / SWE-bench pipeline terms

### Baseline run
A SWE-bench agent run executed without any PF policy guard. Used as the reference solve rate against which a PF-guarded run is compared.

### Budget drift
A mismatch between the `timeout_sec`, `max_steps`, `max_tool_calls`, model, or model parameters recorded in the baseline and PF run manifests. Detected by `compare_runs.py` when `--require-harness` is set; a drifted comparison is invalid.

### CERT-V1
The community standard schema for verifiable AI certificates. Published at `github.com/verifiable-ai-ci/CERT-V1`; used by PF to structure per-run evidence.

### harness_eval

Block in **compare.json** produced by **compare_runs.py**. Parses **`eval/logs/run_evaluation/<run_id>/<model>/<instance_id>/run_instance.log`** for the line **`Test runtime: N seconds`** (newest run batch wins per instance). Exposes **harness_seconds_per_instance** and a **summary** (median, p90, p95). This is harness test-phase duration, not OpenHands agent wall-clock.

### metrics_full.json

Optional run card next to **compare.json**: solve rates, **harness_eval**, agent latency summaries, **estimated_cost_usd**, and observed version fields. Schema version **metrics_full/1.0**.

### compare.json
The machine-readable output of `compare_runs.py`. Contains baseline and PF solve rates, delta, cost per solved instance, policy violation rates, patch-apply aggregation, empty-patch reason counts, replay success rate, and env-drift fields.

### compare.csv
The pivot-friendly per-instance output of `compare_runs.py`. One row per instance (baseline and PF status, patch-apply result) plus a `_summary` row with aggregate counts.

### Denial recovery
When a PF policy guard denies an agent command but the agent continues and eventually produces a valid patch, the episode is counted as "recovered after denial". Tracked in `compare.json` as `recovered_after_denial_pf_rate`.

### Empty-patch reason
A structured code recorded in `patch_apply_check.json` and `predictions.pfmeta.jsonl` explaining why an instance produced no patch. One of: `agent_no_changes`, `patch_too_large`, `diff_timeout`, `apply_check_failed`, `workspace_missing_or_failed`, `guard_denial_prevented_writes`.

### env.json
A per-run snapshot written by the bench runner at `runs/<run_id>/env.json`. Records Python version, platform, dataset, split, and (when available) `openhands_version`, `datasets_version`, `swebench_version`, and `pip_freeze_hash`. Used by `compare_runs.py` to detect environment drift between baseline and PF runs.

### eval_metadata.json
Written by `run_swebench_eval.py` after each harness run into the eval dir. Records the `run_id`, `predictions_sha256`, `dataset_name`, `split`, `datasets_version`, and `swebench_version`. Used by `compare_runs.py --require-harness` to bind eval results to the exact predictions that produced them.

### experiment manifest
A `manifest.json` in each experiment directory (e.g. `experiments/exp-step2-lite-smoke/manifest.json`) that pins `pf_commit`, `agent_framework`, `model`, `policy_pack`, `budgets`, `seed`, and `run_modes`. Ensures that baseline and PF runs are comparable and that solve-rate differences can be attributed to run mode rather than configuration drift.

### GOLDEN.ok
A JSON file written to `runs/<exp>/publish/GOLDEN.ok` by `update_run_ids_if_green.py` when all acceptance gates pass. Contains `baseline_run_id`, `pf_run_id`, `pf_commit`, `timestamp_utc`, and `parity_gate_passed`. The machine verifier (`verify_publish_bundle.py`) checks for this file.

### harness (SWE-bench harness)
The official SWE-bench Docker-based evaluation framework that runs the test suite for each instance against the submitted patch and reports resolved/unresolved/error/empty-patch counts. Requires Docker and runs on Linux/WSL only.

### instance_ids.txt
A stable list of SWE-bench instance IDs for an experiment (e.g. 20 for the smoke run). Generated once with `sample_lite_instance_ids.py --count N --seed 42`; must not change during an iteration loop.

### parity gate
The acceptance condition `pf.solve_rate >= baseline.solve_rate - 0.01`. If the PF-guarded run's solve rate is within 1 percentage point of baseline, the run is considered to have maintained parity. Recorded as `parity_gate_passed` in GOLDEN.ok.

### patch_apply_check.json
Per-instance evidence file recording the result of `git apply --check` on the produced patch. Fields: `applies` (bool), `stderr`, `base_commit`, `resolved_commit`, `git_version`, and optionally `patch_capped_reason` and `diff_stat_file`.

### PF-guarded run
A SWE-bench agent run where every shell command is intercepted by the PF policy guard before execution. Forbidden commands are denied and recorded as violations in `evidence/events.jsonl`; the agent may continue (recoverable denials). Evidence includes `policy_compliance_summary.json` per instance.

### policy_compliance_summary.json
Written per instance in a PF-guarded run. Contains `compliant` (bool), `violations` count, `reason_codes` list, and `chain_tail_hash`. Always written, even when there are zero tool calls.

### predictions.jsonl
The SWE-bench submission file produced by the bench runner. One JSON object per line with fields `instance_id`, `model_patch`, and `model_name_or_path`. Consumed directly by the SWE-bench harness.

### predictions.pfmeta.jsonl
A PF metadata sidecar to `predictions.jsonl`. Same line count and `instance_id` order; contains `run_id`, `policy_hash`, `trace_hash`, `replay_bundle_hash`, `empty_patch_reason`, and `cost_metrics` per instance.

### predictions.sha256
SHA-256 of the predictions file, written by the runner in the same directory. Recorded in `eval_metadata.json` so `compare_runs.py --require-harness` can verify that the harness was run on the exact same predictions file.

### replay bundle
The captured tool I/O and file snapshots that allow an agent run to be replayed deterministically. `run_replay_sample.py` uses replay bundles to verify that replaying a PF-resolved instance reproduces the same patch hash.

### replay_summary.json
Written by `run_replay_sample.py` after replaying a sample of PF-resolved instances. Contains `sample_size`, `success_rate`, `mismatch_count`, and `replay_fail_reasons_topN`. Merged into `compare.json` by `compare_runs.py`.

### run_id
A timestamped unique identifier for a bench run (e.g. `20260317-120041-1badcd73`). The directory `runs/<exp>/<mode>/<run_id>/` contains all per-instance evidence for that run.

### run_status.json
Written by the bench runner in the same directory as `predictions.jsonl`. Contains `run_id`, `status` (`complete` | `partial` | `failed`), `instances_planned`, `instances_written`, `first_error`, and `created_at`. Used by `validate_predictions.py` and `compare_runs.py --require-harness` to detect partial or failed runs.

### allow-empty-patch
Flag for `validate_predictions.py` and `update_run_ids_if_green.py`. When set, validation passes even if some instances have an empty or non-diff `model_patch` (e.g. OpenHands produced no edit). The cycle script uses it in Phase 2.2/3.2 and passes it to `update_run_ids_if_green.py` in Phase 5a so runs with some empty-patch instances can still update run-ids.md when other gates pass.

### OPENHANDS_PROVIDER
Environment variable selecting the LLM provider for OpenHands: `openai` (default), `anthropic`, or `prime_intellect` (aliases such as `prime` / `prime-intellect` normalize to `prime_intellect`). Determines which API key and base URL the PF bench uses. Resolution, fallbacks, and `runs/<run_id>/env.json` fields (`openhands_provider`, `llm_base_url_source`, `llm_base_url_effective`, `prime_team_id_set`) are implemented in **`bench/swebench/provider_env.py`** and consumed by `engines/openhands_engine.py`, `experiments/scripts/ensure_openhands_config.py`, and `bench/swebench/runner.py`. The cycle script and `resolve_cycle_llm.py` validate the matching key before runs.

### Prime Intellect (prime_intellect)
LLM provider option for `OPENHANDS_PROVIDER`. Requires **`PRIME_INTELLECT_API_KEY`**. If **`PRIME_INTELLECT_BASE_URL`** and **`OPENAI_BASE_URL`** are unset, PF defaults to Prime Inference at **`https://api.pinference.ai/api/v1`** so **`pit_*` keys are not sent to OpenAI's platform API**. Optional **`PRIME_TEAM_ID`** is forwarded as **`X-Prime-Team-ID`** when set. The OpenHands **CLI subprocess** path sets **`LLM_API_KEY`**, **`LLM_MODEL`**, **`LLM_BASE_URL`** (via a local strict-compat proxy when using Prime or other strict OpenAI-compatible endpoints), and copies **`OPENHANDS_PROVIDER`**, **`OPENHANDS_MODEL`**, and **`PRIME_TEAM_ID`** into the child environment so downstream LiteLLM/OpenHands routing matches PF. For **`prime_intellect`**, the engine **always uses the subprocess path** (not the in-process library path) so this wiring is consistent. Model IDs are normalized (e.g. `gpt-4o` to `openai/gpt-4o`) for upstream acceptance.

### scale results ledger
`experiments/scale-results-ledger.jsonl`: append-only log of one row per green run. Each row (validated against `experiments/schemas/scale_results_ledger_row.schema.json`) records solve rates, violation rate, instance counts, and experiment metadata so solve-rate trends are visible across runs over time.

### solve rate
The fraction of submitted instances that are resolved by the SWE-bench harness (i.e. the submitted patch makes the test suite pass). Reported as a float in `[0.0, 1.0]` in `compare.json`.

### swebench_safe_v1
The default PF policy pack used for SWE-bench experiments. Denies network binaries (curl, wget), external git clones over HTTPS, and writes outside the workspace; allows standard build and test commands.

### workspace manifest
`workspace_manifest.json` written per instance under `workspaces/<instance_id>/`. Records `instance_id`, `repo`, `base_commit`, resolved paths, and a SHA-256 hash of the manifest. The hash is recorded in the PF evidence log to bind the run to the exact workspace state.
