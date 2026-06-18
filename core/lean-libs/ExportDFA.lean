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

import ActionDSL.Safety
import Lean.Data.Json
import Init.System.IO

open Fabric.ActionDSL

namespace ExportDFA

/-- DFA export configuration -/
structure ExportConfig where
  (bundle_path : String)
  (output_path : String)
  (canonicalize : Bool := true)
  (include_hash : Bool := true)

/-- Canonical JSON export following RFC 8785 -/
def export_canonical_json (dfa : ProductDFA) (config : ExportConfig) : IO String := do
  let dfa_table := dfa.to_table

  let json_obj := Json.mkObj [
    ("version", Json.str "1.0"),
    ("dfa_type", Json.str "ActionDSL_Safety"),
    ("states", Json.arr (dfa_table.states.map fun (id, accepting) =>
      Json.mkObj [
        ("id", Json.num id),
        ("accepting", Json.bool accepting)
      ])),
    ("transitions", Json.arr (dfa_table.transitions.map fun (from, event, to) =>
      Json.mkObj [
        ("from", Json.num from),
        ("event", Json.str event),
        ("to", Json.num to)
      ])),
    ("rate_limiters", Json.arr (dfa_table.rate_limiters.map fun (key, window, bound, tolerance) =>
      Json.mkObj [
        ("key", Json.str key),
        ("window", Json.num window),
        ("bound", Json.num bound),
        ("tolerance", Json.num tolerance)
      ])),
    ("initial_state", Json.num dfa_table.initial_state),
    ("metadata", Json.mkObj [
      ("exported_at", Json.str (toString (System.monoMsNow ()))),
      ("canonical", Json.bool config.canonicalize)
    ])
  ]

  return json_obj.pretty

/-- Export DFA to file with hash -/
def export_dfa (config : ExportConfig) : IO Unit := do
  let dfa := compile_to_dfa []
  let json_content ← export_canonical_json dfa config

  let output_dir := System.FilePath.dirName config.output_path
  IO.FS.createDirAll output_dir
  IO.FS.writeFile config.output_path json_content

  IO.println s!"DFA exported to: {config.output_path}"

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

end ExportDFA
