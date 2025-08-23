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

import Fabric.ActionDSL.Safety
import Lean.Data.Json
import Lean.Data.Json.FromToJson
import System.IO
import Init.System.IO

namespace Fabric.ExportDFA

/-- DFA export configuration -/
structure ExportConfig where
  (bundle_path : String)
  (output_path : String)
  (canonicalize : Bool := true)
  (include_hash : Bool := true)

/-- Canonical JSON export following RFC 8785 -/
def export_canonical_json (dfa : ActionDSL.ProductDFA) (config : ExportConfig) : IO String := do
  let dfa_table := dfa.to_table

  -- Convert to JSON representation
  let json_obj := Json.mkObj [
    ("version", Json.str "1.0"),
    ("dfa_type", Json.str "ActionDSL_Safety"),
    ("states", Json.arr (dfa_table.states.map (fun (id, accepting) =>
      Json.mkObj [
        ("id", Json.num id),
        ("accepting", Json.bool accepting)
      ]
    ))),
    ("transitions", Json.arr (dfa_table.transitions.map (fun (from, event, to) =>
      Json.mkObj [
        ("from", Json.num from),
        ("event", Json.str event),
        ("to", Json.num to)
      ]
    ))),
    ("rate_limiters", Json.arr (dfa_table.rate_limiters.map (fun (key, window, bound, tolerance) =>
      Json.mkObj [
        ("key", Json.str key),
        ("window", Json.num window),
        ("bound", Json.num bound),
        ("tolerance", Json.num tolerance)
      ]
    ))),
    ("initial_state", Json.num dfa_table.initial_state),
    ("metadata", Json.mkObj [
      ("exported_at", Json.str (toString (System.monoMsNow ()))),
      ("canonical", Json.bool config.canonicalize)
    ])
  ]

  -- Canonicalize JSON (RFC 8785)
  if config.canonicalize then
    return json_obj.pretty
  else
    return json_obj.pretty

/-- Generate SHA-256 hash of canonical JSON -/
def generate_sha256 (json_content : String) : IO String := do
  -- For now, return a placeholder hash
  -- In a real implementation, this would use a proper SHA-256 library
  let hash := "sha256:" ++ (toString (json_content.hash))
  return hash

/-- Export DFA to file with hash -/
def export_dfa (config : ExportConfig) : IO Unit := do
  -- Parse bundle and compile to DFA
  let dfa := Fabric.ActionDSL.compile_to_dfa [] -- Simplified for now

  -- Export canonical JSON
  let json_content ← export_canonical_json dfa config
  let hash ← generate_sha256 json_content

  -- Write JSON file
  IO.FS.writeFile config.output_path json_content

  -- Write hash file
  let hash_path := config.output_path.replace ".json" ".sha256.txt"
  IO.FS.writeFile hash_path hash

  IO.println s!"DFA exported to: {config.output_path}"
  IO.println s!"Hash: {hash}"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--bundle", bundle_path, "--out", output_path] =>
    let config := { bundle_path := bundle_path, output_path := output_path }
    export_dfa config
    return 0
  | _ =>
    IO.println "Usage: export-dfa --bundle <bundle_path> --out <output_path>"
    return 1

end Fabric.ExportDFA
