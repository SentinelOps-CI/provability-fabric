// SPDX-License-Identifier: Apache-2.0
import assert from "node:assert/strict";
import { test } from "node:test";
import { checkWorkspace } from "../scripts/check_npm_lockfile_parity.mjs";

function fixture() {
  const ws="runtime/ledger";
  const m={dependencies:{"@scope/lib":"^1.0.0"},devDependencies:{testlib:"^2.0.0"}};
  const copy=x=>JSON.parse(JSON.stringify(x));
  const root={lockfileVersion:3,packages:{[ws]:copy(m),[ws+"/node_modules/@scope/lib"]:{version:"1.1.0",integrity:"sha512-a"},"node_modules/testlib":{version:"2.0.0"}}};
  const local={lockfileVersion:3,packages:{"":copy(m),"node_modules/@scope/lib":{version:"1.1.0",integrity:"sha512-a"},"node_modules/testlib":{version:"2.0.0"}}};
  return {ws,m,root,local};
}

test("matching nested and hoisted dependencies", () => {
  const f = fixture();
  (f=>{})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 0, errors.join("\n"));
});

test("stale manifest snapshot", () => {
  const f = fixture();
  (f=>{f.root.packages[f.ws].dependencies["@scope/lib"]="^0.9.0"})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("unexpected manifest dependency", () => {
  const f = fixture();
  (f=>{f.local.packages[""].dependencies.extra="1.0.0"})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("runtime version mismatch", () => {
  const f = fixture();
  (f=>{f.local.packages["node_modules/@scope/lib"].version="1.2.0"})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("development version mismatch", () => {
  const f = fixture();
  (f=>{f.root.packages["node_modules/testlib"].version="2.1.0"})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("missing package", () => {
  const f = fixture();
  (f=>{delete f.root.packages["node_modules/testlib"]})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("conflicting integrity", () => {
  const f = fixture();
  (f=>{f.local.packages["node_modules/@scope/lib"].integrity="sha512-b"})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("missing snapshot", () => {
  const f = fixture();
  (f=>{delete f.root.packages[f.ws]})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("unsupported lockfile version", () => {
  const f = fixture();
  (f=>{f.local.lockfileVersion=2})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 1, errors.join("\n"));
});

test("nested precedence", () => {
  const f = fixture();
  (f=>{f.root.packages["node_modules/@scope/lib"]={version:"9.0.0"}})(f);
  const errors = checkWorkspace(f.ws, f.m, f.root, f.local);
  assert.equal(errors.length, 0, errors.join("\n"));
});
