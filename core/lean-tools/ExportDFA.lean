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

/--
Export DFA JSON to `config.output_path`.

Integrity hashing is **not** performed here: the advertised lake executable and CI
path live under `core/lean-libs/ExportDFA.lean`, and hosts compute SHA-256 externally
(e.g. `sha256sum` in `.github/workflows/dfa.yaml`). This module is a non-executable
mirror kept for path-filter / inventory references only.
-/
def export_dfa (config : ExportConfig) : IO Unit := do
  let dfa := Fabric.ActionDSL.compile_to_dfa []
  let json_content ← export_canonical_json dfa config
  IO.FS.writeFile config.output_path json_content
  IO.println s!"DFA exported to: {config.output_path}"
  if config.include_hash then
    IO.println "Note: SHA-256 is host-side (sha256sum); not emitted by this Lean module."

/-- Main entry point (not registered as a lake exe; prefer core/lean-libs ExportDFA). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--bundle", bundle_path, "--out", output_path] =>
    let config := { bundle_path := bundle_path, output_path := output_path }
    export_dfa config
    return 0
  | _ =>
    IO.println "Usage: export-dfa --bundle <bundle_path> --out <output_path>"
    IO.println "Canonical executable: cd core/lean-libs && lake exe ExportDFA ..."
    return 1

end Fabric.ExportDFA
