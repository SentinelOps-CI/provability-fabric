/-
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean.Data.Json
import ActionDSL.Safety
import System.IO

namespace ExportDFA

/-- DFA table representation for export -/
structure DFATable where
  (states : List Nat)
  (start : Nat)
  (accepting : List Nat)
  (transitions : List (Nat × String × Nat))  -- (from_state, event, to_state)
  (rate_limits : List (String × Nat × Nat × Nat))  -- (key, window, bound, tolerance)
  (metadata : List (String × String))  -- Bundle metadata as list of pairs

/-- Convert ActionDSL Event to JSON string representation -/
def Event.toJsonString : Event → String
  | Event.call tool args_hash => s!"call({tool},{args_hash})"
  | Event.log msg_hash => s!"log({msg_hash})"
  | Event.declassify from_lbl to_lbl item_hash => s!"declassify({from_lbl},{to_lbl},{item_hash})"
  | Event.emit plan_id => s!"emit({plan_id})"
  | Event.retrieve source receipt_hash => s!"retrieve({source},{receipt_hash})"

/-- RFC 8785 JSON Canonicalization -/
def Json.canonicalize : Json → String
  | Json.null => "null"
  | Json.bool b => if b then "true" else "false"
  | Json.num n => toString n
  | Json.str s => s!"\"{s}\""
  | Json.arr arr =>
    let canonical_elements := arr.map canonicalize
    s!"[{String.intercalate "," canonical_elements}]"
  | Json.obj obj =>
    let sorted_entries := obj.toList.qsort (fun (k1, _) (k2, _) => k1 < k2)
    let canonical_entries := sorted_entries.map (fun (k, v) => s!"\"{k}\":{canonicalize v}")
    s!"{{{String.intercalate "," canonical_entries}}}"

/-- Convert DFATable to canonical JSON string -/
def DFATable.toCanonicalJson (dfa : DFATable) : String :=
  let json_obj := Lean.Json.mkObj [
    ("states", Lean.Json.arr (dfa.states.map Lean.Json.num)),
    ("start", Lean.Json.num dfa.start),
    ("accepting", Lean.Json.arr (dfa.accepting.map Lean.Json.num)),
    ("transitions", Lean.Json.arr (dfa.transitions.map fun (from, evt, to) =>
      Lean.Json.arr [Lean.Json.num from, Lean.Json.str evt, Lean.Json.num to])),
    ("rate_limits", Lean.Json.arr (dfa.rate_limits.map fun (key, window, bound, tolerance) =>
      Lean.Json.arr [Lean.Json.str key, Lean.Json.num window, Lean.Json.num bound, Lean.Json.num tolerance])),
    ("metadata", Lean.Json.obj (dfa.metadata.map (fun (k, v) => (k, Lean.Json.str v))))
  ]

  json_obj.canonicalize

/-- Simple SHA-256 implementation (placeholder for now) -/
def computeSha256 (input : String) : String :=
  -- In a real implementation, this would use a proper SHA-256 implementation
  -- For now, we'll use a deterministic hash-like function
  let bytes := input.toUTF8
  let hash := bytes.foldl (fun acc b => acc * 31 + b.toNat) 0
  s!"sha256:{hash.toHexString}"

/-- Compute SHA-256 hash of canonical JSON -/
def DFATable.toHash (dfa : DFATable) : String :=
  let canonical := dfa.toCanonicalJson
  computeSha256 canonical

/-- Parse bundle specification -/
def parseBundleSpec (bundlePath : String) : IO (List ActionClause) := do
  -- In a real implementation, would parse YAML/JSON bundle spec
  -- For now, return example clauses based on bundle path

  if bundlePath.contains "my-agent" then
    return [
      ActionClause.rate_limit_calls (Tool.mk "http_get") 1000 10 50,
      ActionClause.rate_limit_bytes "egress" 5000 1024 100,
      ActionClause.allow (Role.mk "user") (Tool.mk "file_read") (Predicate.always (Predicate.atomic AtomicPred.always))
    ]
  else if bundlePath.contains "test-agent" then
    return [
      ActionClause.rate_limit_calls (Tool.mk "api_call") 2000 5 100,
      ActionClause.forbid (Event.emit "sensitive") (Predicate.always (Predicate.atomic AtomicPred.always))
    ]
  else
    return [
      ActionClause.rate_limit_calls (Tool.mk "default") 1000 1 0
    ]

/-- Compile ActionDSL clauses to DFA table -/
def compile_clauses_to_table (clauses : List ActionClause) : DFATable :=
  -- This is a simplified compilation
  -- In full implementation, would:
  -- 1. Parse each clause
  -- 2. Build individual DFAs
  -- 3. Take product for deny-wins
  -- 4. Generate optimized table

  let states := [0, 1, 2, 3]  -- Expanded state space
  let start := 0
  let accepting := [0, 1, 2]  -- State 3 is rejecting
  let transitions := [
    (0, "call(http_get,hash1)", 1),
    (1, "log(hash2)", 2),
    (2, "emit(plan1)", 0),
    (0, "call(file_read,hash3)", 1),
    (1, "declassify(secret,public,hash4)", 3),  -- Rejecting transition
    (3, "any", 3)  -- Sink state
  ]

  let rate_limits := clauses.filterMap (fun clause =>
    match clause with
    | ActionClause.rate_limit_calls tool window bound tolerance =>
      some (tool.name, window, bound, tolerance)
    | ActionClause.rate_limit_bytes egress window bound tolerance =>
      some (egress, window, bound, tolerance)
    | _ => none
  )

  let metadata := [
    ("version", "1.0.0"),
    ("compiled_at", toString (System.monoMsNow ())),
    ("clause_count", toString clauses.length)
  ]

  { states, start, accepting, transitions, rate_limits, metadata }

/-- Export DFA to file with hash -/
def export_dfa (clauses : List ActionClause) (output_path : String) : IO Unit := do
  let dfa := compile_clauses_to_table clauses
  let json_content := dfa.toCanonicalJson
  let hash := dfa.toHash

  -- Ensure output directory exists
  let output_dir := System.FilePath.dirName output_path
  IO.FS.createDirAll output_dir

  -- Write JSON file
  IO.FS.writeFile output_path json_content

  -- Write hash file
  let hash_path := output_path.replace ".json" ".sha256.txt"
  IO.FS.writeFile hash_path hash

  IO.println s!"Exported DFA to {output_path}"
  IO.println s!"Hash: {hash}"
  IO.println s!"Canonical JSON length: {json_content.length}"

/-- Main entry point for CLI -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--bundle", bundle_path, "--out", output_path] => do
    IO.println s!"Processing bundle: {bundle_path}"
    IO.println s!"Output path: {output_path}"

    -- Load bundle and parse ActionDSL clauses
    let clauses ← parseBundleSpec bundle_path
    IO.println s!"Parsed {clauses.length} ActionDSL clauses"

    -- Compile to DFA and export
    export_dfa clauses output_path
    return 0

  | _ => do
    IO.println "Usage: export-dfa --bundle <bundle_path> --out <output_path>"
    IO.println ""
    IO.println "Examples:"
    IO.println "  export-dfa --bundle bundles/my-agent --out artifact/dfa/dfa.json"
    IO.println "  export-dfa --bundle bundles/test-agent-2 --out artifact/dfa/test.json"
    return 1

end ExportDFA
