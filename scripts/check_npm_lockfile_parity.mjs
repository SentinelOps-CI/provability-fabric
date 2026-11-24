// SPDX-License-Identifier: Apache-2.0
// Read-only check for npm workspace and standalone installation paths.
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

export function checkWorkspace(workspace, manifest, rootLock, standaloneLock) {
  const errors = [];
  if (rootLock?.lockfileVersion !== 3 || standaloneLock?.lockfileVersion !== 3) return [`${workspace}: expected lockfileVersion 3`];
  const rp = rootLock.packages, lp = standaloneLock.packages;
  if (!rp?.[workspace] || !lp?.[""]) return [`${workspace}: missing manifest snapshot`];
  for (const field of ["dependencies", "devDependencies", "optionalDependencies", "peerDependencies"]) {
    const expected = manifest[field] ?? {};
    for (const [label, snapshot] of [["root", rp[workspace]], ["standalone", lp[""]]]) {
      const actual = snapshot[field] ?? {};
      for (const name of [...new Set([...Object.keys(expected), ...Object.keys(actual)])].sort()) {
        if (expected[name] !== actual[name]) errors.push(`${workspace}: ${label} ${field}.${name}: expected ${expected[name] ?? "<absent>"}, found ${actual[name] ?? "<absent>"}`);
      }
    }
  }
  // Direct runtime and development dependencies only; not full transitive parity.
  for (const name of Object.keys({...manifest.dependencies, ...manifest.devDependencies}).sort()) {
    const root = rp[`${workspace}/node_modules/${name}`] ?? rp[`node_modules/${name}`];
    const local = lp[`node_modules/${name}`];
    if (typeof root?.version !== "string" || typeof local?.version !== "string") errors.push(`${workspace}: missing direct dependency ${name}`);
    else if (root.version !== local.version) errors.push(`${workspace}: ${name}: root ${root.version}, standalone ${local.version}`);
    else if (root.integrity && local.integrity && root.integrity !== local.integrity) errors.push(`${workspace}: ${name}: conflicting integrity hashes for ${root.version}`);
  }
  return errors;
}

function main() {
  const root = fileURLToPath(new URL("../", import.meta.url));
  const read = path => JSON.parse(readFileSync(resolve(root, path), "utf8"));
  const rootLock = read("package-lock.json");
  const errors = ["runtime/ledger", "core/sdk/typescript"].flatMap(ws =>
    checkWorkspace(ws, read(ws + "/package.json"), rootLock, read(ws + "/package-lock.json"))
  );
  if (errors.length) {
    for (const error of errors) console.error(error);
    console.error("Synchronize both npm lockfiles and rerun the check.");
    process.exitCode = 1;
  } else {
    console.log("Direct dependency parity verified for Ledger and TypeScript SDK.");
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    main();
  } catch (error) {
    console.error("Unable to verify npm lockfiles:", error.message);
    process.exitCode = 1;
  }
}
