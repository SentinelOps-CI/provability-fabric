# External dependencies (optional)

This directory is used by `docker-compose.yml` for optional mounts:

- **CERT-V1** – Clone [verifiable-ai-ci/CERT-V1](https://github.com/verifiable-ai-ci/CERT-V1) into `CERT-V1/` for evidence-service schema and verifiers.
- **TRACE-REPLAY-KIT** – Clone [verifiable-ai-ci/TRACE-REPLAY-KIT](https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT) into `TRACE-REPLAY-KIT/` for the replay-service runner.

If these directories are missing, Docker Compose will create empty mount points and the platform will start; full evidence and replay features may require the real content.

Example setup:

```bash
git clone --depth 1 https://github.com/verifiable-ai-ci/CERT-V1.git CERT-V1
git clone --depth 1 https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT.git TRACE-REPLAY-KIT
```
