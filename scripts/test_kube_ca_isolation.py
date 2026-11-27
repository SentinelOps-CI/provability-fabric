#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Run the real kube client against two independently rooted TLS fixtures.

Only for an ephemeral Linux CI runner: installs one generated system root.
The second root is supplied only through the client's explicit CA config.
"""
import contextlib
import http.server
import json
import os
from pathlib import Path
import ssl
import subprocess
import tempfile
import threading

def run(*args):
    subprocess.run(args, check=True)

class ConfigMapHandler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path != "/api/v1/namespaces/default/configmaps/privacy-config":
            self.send_error(404)
            return
        config = {
            "tenant_id": "fixture-tenant",
            "epsilon_limit": 1.0,
            "delta_limit": 0.1,
            "reset_period_hours": 24,
        }
        data = json.dumps({
            "apiVersion": "v1",
            "kind": "ConfigMap",
            "metadata": {"name": "privacy-config", "namespace": "default"},
            "data": {"fixture-tenant": json.dumps(config)},
        }).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

def make_chain(directory, name):
    root_key = directory / f"{name}-ca.key"
    root = directory / f"{name}-ca.crt"
    key = directory / f"{name}.key"
    csr = directory / f"{name}.csr"
    cert = directory / f"{name}.crt"
    ext = directory / f"{name}.ext"
    ext.write_text("basicConstraints=critical,CA:FALSE\n"
                   "keyUsage=critical,digitalSignature,keyEncipherment\n"
                   "extendedKeyUsage=serverAuth\nsubjectAltName=IP:127.0.0.1\n")
    run("openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
        "-days", "2", "-subj", f"/CN=PF fixture {name} CA",
        "-addext", "basicConstraints=critical,CA:TRUE",
        "-addext", "keyUsage=critical,keyCertSign,cRLSign",
        "-keyout", str(root_key), "-out", str(root))
    run("openssl", "req", "-new", "-newkey", "rsa:2048", "-nodes",
        "-subj", "/CN=127.0.0.1", "-keyout", str(key), "-out", str(csr))
    run("openssl", "x509", "-req", "-in", str(csr), "-CA", str(root),
        "-CAkey", str(root_key), "-CAcreateserial", "-days", "2",
        "-extfile", str(ext), "-out", str(cert))
    run("openssl", "verify", "-CAfile", str(root), "-verify_ip", "127.0.0.1", str(cert))
    return root, cert, key

@contextlib.contextmanager
def endpoint(cert, key):
    with http.server.ThreadingHTTPServer(("127.0.0.1", 0), ConfigMapHandler) as server:
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(cert, key)
        server.socket = context.wrap_socket(server.socket, server_side=True)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            yield f"https://127.0.0.1:{server.server_port}"
        finally:
            server.shutdown()
            thread.join(timeout=5)
            if thread.is_alive():
                raise RuntimeError("TLS fixture did not stop")

def main():
    if os.environ.get("GITHUB_ACTIONS") != "true" or os.environ.get("RUNNER_OS") != "Linux":
        raise RuntimeError("Run only on an isolated Linux GitHub Actions runner")
    with tempfile.TemporaryDirectory(prefix="pf-kube-ca-") as name:
        directory = Path(name)
        explicit_root, explicit_cert, explicit_key = make_chain(directory, "explicit")
        system_root, system_cert, system_key = make_chain(directory, "system")
        der = directory / "explicit.der"
        run("openssl", "x509", "-in", str(explicit_root), "-outform", "DER", "-out", str(der))
        installed = f"/usr/local/share/ca-certificates/{directory.name}.crt"
        run("sudo", "install", "-m", "0644", str(system_root), installed)
        try:
            run("sudo", "update-ca-certificates")
            run("openssl", "verify", "-verify_ip", "127.0.0.1", str(system_cert))
            with endpoint(explicit_cert, explicit_key) as trusted, endpoint(system_cert, system_key) as unrelated:
                env = dict(os.environ, PF_KUBE_TEST_CA_DER=str(der),
                           PF_KUBE_TEST_TRUSTED_URL=trusted, PF_KUBE_TEST_UNRELATED_URL=unrelated)
                subprocess.run(["cargo", "test", "--locked", "-p", "sidecar-watcher",
                                "--lib", "privacy::epsilon_guard::tests::test_kubernetes_configmap_configured_ca_is_exclusive",
                                "--", "--ignored", "--exact", "--nocapture"],
                               env=env, check=True)
        finally:
            run("sudo", "rm", installed)
            run("sudo", "update-ca-certificates")

if __name__ == "__main__":
    main()
