#!/usr/bin/env python3
"""Disposable PostgreSQL HTTP qualification; never run against a production database."""
from __future__ import annotations

import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from urllib.request import urlopen

from retrieval_auth_smoke import claims_for, sign_token, verifier_key_map, request_gateway, ISSUER

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests"))
from test_retrieval_result_commitment_v2 import compute_reference

BASE = "http://127.0.0.1:18080"
ADMIN = "postgres://postgres:testpass@127.0.0.1:5432/postgres"
APP = "postgres://pf_retrieval_ci:testpass@127.0.0.1:5432/postgres"


def sql(statement: str) -> None:
    subprocess.run(["psql", "-X", "-v", "ON_ERROR_STOP=1", ADMIN, "-c", statement],
                   check=True, timeout=15)


def openssl(*args: str) -> None:
    subprocess.run(["openssl", *args], check=True, capture_output=True, timeout=15)


def verify_receipt(reply: dict, request: dict, public: Path, directory: Path) -> None:
    receipt = reply["receipt"]
    results = reply["results"]
    assert receipt["tenant"] == request["tenant"]
    assert receipt["subject_id"] == request["subject_id"]
    assert receipt["query_hash"] == hashlib.sha256(request["query"].encode()).hexdigest()
    assert receipt["result_count"] == reply["total_count"] == len(results)
    assert receipt["result_hash"] == compute_reference(request["tenant"], results)
    assert receipt["sign_alg"] == "ed25519"
    signed = {k: receipt[k] for k in ("receipt_id", "tenant", "subject_id",
              "query_hash", "index_shard", "timestamp", "result_hash")}
    signed["signature"] = ""
    for k in ("result_count", "query_time_ms"):
        if receipt[k] != 0:
            signed[k] = receipt[k]
    # Fixtures use ASCII strings; independent sorted JSON matches wire encoding.
    with tempfile.TemporaryDirectory(dir=directory) as temp:
        message = Path(temp) / "message"
        sig = Path(temp) / "sig"
        message.write_bytes(json.dumps(signed, sort_keys=True, separators=(",", ":")).encode())
        sig.write_bytes(base64.b64decode(receipt["sig"], validate=True))
        openssl("pkeyutl", "-verify", "-pubin", "-inkey", str(public),
                "-rawin", "-in", str(message), "-sigfile", str(sig))


def main() -> None:
    if (os.environ.get("GITHUB_ACTIONS") != "true"
            or os.environ.get("PF_POSTGRES_TEST_ADMIN_URL") != ADMIN
            or os.environ.get("PF_POSTGRES_TEST_APP_URL") != APP):
        raise RuntimeError("requires exact disposable CI database configuration")
    # Existing storage qualification seeds five rows; add independent controls.
    sql("""INSERT INTO documents (id, tenant, content, labels, metadata, embedding, created_at, updated_at)
           SELECT 'a-public-two', tenant, 'second content', ARRAY['public'], metadata, embedding, 1000, 1001
             FROM documents WHERE id='a-public';
           INSERT INTO documents (id, tenant, content, labels, metadata, embedding, created_at, updated_at)
           SELECT 'a-private', tenant, 'private content', ARRAY['private'], metadata, embedding, 1000, 1001
             FROM documents WHERE id='a-public';""")
    with tempfile.TemporaryDirectory(prefix="pf-pg-http-") as tmp:
        directory = Path(tmp)
        issuer, signer, untrusted, public = [directory / name for name in
            ("issuer.pem", "receipt.pem", "untrusted.pem", "receipt-public.pem")]
        for key in (issuer, signer, untrusted):
            openssl("genpkey", "-algorithm", "Ed25519", "-out", str(key))
            key.chmod(0o600)
        openssl("pkey", "-in", str(signer), "-pubout", "-out", str(public))
        env = os.environ.copy()
        env.pop("RECEIPT_SIGNING_KEY", None)
        env.pop("PF_POSTGRES_TEST_ADMIN_URL", None)
        env.update(RETRIEVAL_POSTGRES_URL=APP, RETRIEVAL_LISTEN_ADDR="127.0.0.1:18080",
                   RETRIEVAL_JWT_VERIFY_KEYS_JSON=json.dumps(verifier_key_map(issuer)),
                   RETRIEVAL_JWT_ISSUER=ISSUER, RECEIPT_SIGNING_KEY_PATH=str(signer),
                   LEDGER_ENDPOINT="http://127.0.0.1:1")
        binary = ROOT / "target/debug/retrieval-gateway"
        cwd = ROOT / "runtime/retrieval-gateway"
        # An administrator connection must be rejected before serving.
        rejected = subprocess.run([binary], cwd=cwd, env={**env, "RETRIEVAL_POSTGRES_URL": ADMIN},
                                  capture_output=True, timeout=20)
        assert rejected.returncode != 0 and b"restricted SELECT role" in rejected.stderr
        print("PASS privileged startup denied")
        with (directory / "gateway.log").open("w+") as log:
            server = subprocess.Popen([binary], cwd=cwd, env=env, stdout=log, stderr=log)
            try:
                for _ in range(100):
                    if server.poll() is not None:
                        raise RuntimeError("gateway exited before health check")
                    try:
                        with urlopen(BASE + "/health", timeout=1) as response:
                            if response.status == 200:
                                break
                    except OSError:
                        time.sleep(0.2)
                else:
                    raise RuntimeError("gateway startup deadline exceeded")

                def payload(tenant="tenant-a", labels=None, capabilities=None, limit=10, key=issuer):
                    labels = ["public"] if labels is None else labels
                    claims = claims_for(tenant, "user_ci", int(time.time()))
                    claims["allowed_labels"] = labels
                    claims["capabilities"] = capabilities or []
                    return {"query": "integration-query", "tenant": tenant, "subject_id": "user_ci",
                            "capability_token": sign_token(key, claims), "labels_filter": labels, "limit": limit}

                def check(name, request, status, ids=None):
                    code, result = request_gateway(BASE + "/query", request)
                    assert code == status, (name, code, status)
                    if status == 200:
                        observed = [r["document_id"] for r in result["results"]]
                        assert len(observed) == len(ids) and set(observed) == set(ids), (name, observed)
                        verify_receipt(result, request, public, directory)
                    print("PASS", name, code)

                a = payload()
                b = payload("tenant-b")
                check("tenant A public", a, 200, {"a-public", "a-public-two"})
                check("tenant B public", b, 200, {"b-public"})
                check("limit one", payload(limit=1), 200, {"a-public"})
                check("private authorized", payload(labels=["private"], capabilities=["private_access"]), 200, {"a-private"})
                check("private denied", payload(labels=["private"]), 403)
                check("mixed scope denied", payload(labels=["public", "secret"]), 403)
                check("tenant substitution", {**a, "tenant": "tenant-b"}, 403)
                check("subject substitution", {**a, "subject_id": "other"}, 403)
                check("forged issuer", payload(key=untrusted), 403)
                check("legacy token", {**a, "capability_token": "legacy"}, 403)
                with ThreadPoolExecutor(max_workers=4) as pool:
                    futures = [pool.submit(check, f"parallel tenant {i}", a if i % 2 == 0 else b, 200,
                                {"a-public", "a-public-two"} if i % 2 == 0 else {"b-public"})
                               for i in range(12)]
                    for future in futures:
                        future.result()
                sql("UPDATE documents SET labels=ARRAY['secret'] WHERE id='a-public-two'")
                check("classification changed after prior response", a, 200, {"a-public"})
                sql("REVOKE SELECT ON documents FROM pf_retrieval_ci")
                try:
                    check("database permission revoked, no stale cache fallback", a, 500)
                finally:
                    sql("GRANT SELECT ON documents TO pf_retrieval_ci")
                check("database permission restored", a, 200, {"a-public"})
            finally:
                server.terminate()
                try:
                    server.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    server.kill()
                    server.wait()
                if sys.exc_info()[0] is not None:
                    log.seek(0)
                    print(log.read(), file=sys.stderr)


if __name__ == "__main__":
    main()
