#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Isolated native Vault transit integration; never run against a real deployment."""
import base64
import json
import os
from pathlib import Path
import secrets
import socket
import struct
import subprocess
import tempfile
import time
import urllib.error
import urllib.request

DOMAIN = b"provability-fabric/kms-request-authority/v1\0"
MAX_RESPONSE = 128 * 1024
SPKI_PREFIX = bytes.fromhex("302a300506032b6570032100")


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


HTTP = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())


def api(url, path, payload=None, token=None, method=None):
    headers = {"Content-Type": "application/json"}
    if token is not None:
        headers["X-Vault-Token"] = token
    body = None if payload is None else json.dumps(payload).encode()
    request = urllib.request.Request(url + path, data=body, headers=headers, method=method)
    try:
        response = HTTP.open(request, timeout=8)
    except urllib.error.HTTPError as exc:
        response = exc
    with response:
        raw = response.read(MAX_RESPONSE + 1)
        if len(raw) > MAX_RESPONSE:
            raise RuntimeError("fixture response exceeded bound")
        return response.status, json.loads(raw) if raw else {}


def require(url, path, payload=None, token=None, method=None, expected=(200, 204)):
    status, result = api(url, path, payload, token, method)
    if status not in expected:
        raise RuntimeError(f"unexpected HTTP status {status} for {path}")
    return result


def openssl(*args):
    return subprocess.run(["openssl", *map(str, args)], check=True, timeout=10,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def field(value):
    data = value.encode("utf-8")
    return struct.pack(">I", len(data)) + data


def signed_request(root, issuer, key="test-key", data="test message"):
    now = time.time_ns()
    seconds, nanos = divmod(now, 1_000_000_000)
    timestamp = time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(seconds)) + f".{nanos:09d}Z"
    token = {"token": secrets.token_hex(16), "pod_identity": "pod-a",
             "policy_hash": "policy-a", "timestamp": timestamp}
    message = DOMAIN + b"".join(map(field, ["isolated-test", token["token"], "pod-a",
                                            "policy-a", "sign", key]))
    message += struct.pack(">qI", seconds, nanos) + b"\x01" + field(data)
    (root / "issuer-input").write_bytes(message)
    sig = openssl("pkeyutl", "-sign", "-rawin", "-inkey", issuer,
                  "-in", root / "issuer-input")
    token["signature"] = base64.b64encode(sig).decode("ascii")
    return {"operation": "sign", "key_id": key, "data": data, "attestation_token": token}


def verify(root, public, data, signature):
    (root / "message").write_bytes(data)
    (root / "signature").write_bytes(signature)
    proc = subprocess.run(["openssl", "pkeyutl", "-verify", "-pubin", "-keyform", "DER",
                           "-inkey", str(public), "-rawin", "-in", str(root / "message"),
                           "-sigfile", str(root / "signature")],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    if proc.returncode not in (0, 1):
        raise RuntimeError("OpenSSL verification failed to execute")
    return proc.returncode == 0


def free_port():
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def ready(process, url, path, expected):
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        if process.poll() is not None:
            raise RuntimeError("fixture process exited before readiness")
        try:
            if api(url, path)[0] in expected:
                return
        except (OSError, urllib.error.URLError):
            pass
        time.sleep(0.2)
    raise RuntimeError("fixture readiness timed out")


def stop(process):
    if process is None or process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def main():
    if os.environ.get("GITHUB_ACTIONS") != "true" or os.environ.get("RUNNER_OS") != "Linux":
        raise RuntimeError("this fixture is restricted to the isolated Linux CI runner")
    vault_bin = Path(os.environ["PF_TEST_VAULT_BIN"]).resolve(strict=True)
    proxy_bin = Path("target/debug/kms-proxy").resolve(strict=True)
    # Fail rather than accidentally interact with an existing local service.
    with socket.socket() as check:
        check.bind(("127.0.0.1", 8082))
    with tempfile.TemporaryDirectory(prefix="pf-vault-test-") as tmp:
        root = Path(tmp)
        issuer = root / "issuer.pem"
        openssl("genpkey", "-algorithm", "ED25519", "-out", issuer)
        public = openssl("pkey", "-in", issuer, "-pubout", "-outform", "DER")
        if len(public) != len(SPKI_PREFIX) + 32 or not public.startswith(SPKI_PREFIX):
            raise RuntimeError("unexpected issuer public key format")
        root_token = secrets.token_hex(32)
        vault_url = f"http://127.0.0.1:{free_port()}"
        proxy_url = "http://127.0.0.1:8082"
        # No production credentials or ambient Vault configuration are inherited.
        env = {k: os.environ[k] for k in ("PATH", "LANG") if k in os.environ}
        env["HOME"] = str(root)
        vault = proxy = None
        with (root / "vault.log").open("wb") as vault_log, (root / "proxy.log").open("wb") as proxy_log:
            try:
                vault = subprocess.Popen([str(vault_bin), "server", "-dev", "-dev-no-store-token",
                                          f"-dev-listen-address={vault_url.removeprefix('http://')}",
                                          f"-dev-root-token-id={root_token}"],
                                         env=env, stdout=vault_log, stderr=subprocess.STDOUT)
                ready(vault, vault_url, "/v1/sys/health", (200,))
                require(vault_url, "/v1/sys/mounts/transit", {"type": "transit"}, root_token)
                keys = {}
                for name in ("test-key", "other-key"):
                    require(vault_url, f"/v1/transit/keys/{name}",
                            {"type": "ed25519", "derived": False, "exportable": False}, root_token)
                    details = require(vault_url, f"/v1/transit/keys/{name}", token=root_token)["data"]
                    if details["type"] != "ed25519" or details["latest_version"] != 1:
                        raise RuntimeError("unexpected transit key type or version")
                    key = base64.b64decode(details["keys"]["1"]["public_key"], validate=True)
                    if len(key) != 32:
                        raise RuntimeError("unexpected transit public key length")
                    path = root / (name + ".der")
                    path.write_bytes(SPKI_PREFIX + key)
                    keys[name] = path
                policy = 'path "transit/sign/test-key" { capabilities = ["update"] }'
                require(vault_url, "/v1/sys/policies/acl/pf-sign-only", {"policy": policy}, root_token)
                restricted = require(vault_url, "/v1/auth/token/create",
                                     {"policies": ["pf-sign-only"], "no_default_policy": True,
                                      "ttl": "10m"}, root_token)["auth"]["client_token"]
                # Non-vacuous provider ACL negative control.
                require(vault_url, "/v1/transit/sign/other-key",
                        {"input": base64.b64encode(b"test message").decode()}, restricted, expected=(403,))
                require(vault_url, "/v1/transit/keys/test-key", token=restricted, expected=(403,))
                proxy_env = dict(env, VAULT_URL=vault_url, VAULT_TOKEN=restricted,
                                 KMS_ATTESTATION_PUBLIC_KEY=base64.b64encode(public[len(SPKI_PREFIX):]).decode(),
                                 KMS_ATTESTATION_AUDIENCE="isolated-test",
                                 KMS_ALLOWED_POLICY_HASHES="policy-a",
                                 KMS_ALLOWED_POD_IDENTITIES="pod-a")
                proxy = subprocess.Popen([str(proxy_bin)], env=proxy_env,
                                         stdout=proxy_log, stderr=subprocess.STDOUT)
                ready(proxy, proxy_url, "/kms/sign", (404,))
                request = signed_request(root, issuer)
                response = require(proxy_url, "/kms/sign", request)
                if response["success"] is not True:
                    raise RuntimeError("authorized signing did not succeed")
                prefix, version, encoded = response["result"].split(":")
                if (prefix, version) != ("vault", "v1"):
                    raise RuntimeError("unexpected Vault signature version")
                signature = base64.b64decode(encoded, validate=True)
                if len(signature) != 64:
                    raise RuntimeError("unexpected Ed25519 signature length")
                if not verify(root, keys["test-key"], b"test message", signature):
                    raise RuntimeError("independent OpenSSL verification rejected Vault signature")
                if verify(root, keys["test-key"], b"changed message", signature):
                    raise RuntimeError("signature verified against altered message")
                if verify(root, keys["other-key"], b"test message", signature):
                    raise RuntimeError("signature verified against unrelated public key")
                # Retired operations must fail on the actual HTTP listener,
                # even when a valid signing credential is supplied.
                for operation in ("encrypt", "decrypt", "verify", "rotate-keys"):
                    retired = require(proxy_url, f"/kms/{operation}",
                                      dict(request, operation=operation), expected=(501,))
                    if retired.get("success") is not False or retired.get("result") is not None:
                        raise RuntimeError(f"retired operation {operation} returned success")
                mismatch = require(proxy_url, "/kms/sign",
                                   dict(request, operation="encrypt"), expected=(400,))
                if mismatch.get("success") is not False or mismatch.get("result") is not None:
                    raise RuntimeError("operation/endpoint mismatch returned success")
                altered = dict(request, data="changed message")
                require(proxy_url, "/kms/sign", altered, expected=(403,))
                require(proxy_url, "/kms/sign", dict(request, attestation_token=None), expected=(403,))
                denied = require(proxy_url, "/kms/sign", signed_request(root, issuer, key="other-key"),
                                 expected=(502,))
                if denied["success"] or denied["result"] is not None:
                    raise RuntimeError("provider ACL denial returned success")
                require(vault_url, "/v1/auth/token/revoke", {"token": restricted}, root_token)
                denied = require(proxy_url, "/kms/sign", signed_request(root, issuer), expected=(502,))
                if denied["success"] or denied["result"] is not None:
                    raise RuntimeError("revoked provider credential returned success")
                print("PASS: native Vault Ed25519 signature independently verified; wrong message, wrong key, "
                      "tampered request, missing authority, provider ACL denial, revoked provider token, retired operations and endpoint mismatch rejected")
            finally:
                stop(proxy)
                stop(vault)


if __name__ == "__main__":
    main()
