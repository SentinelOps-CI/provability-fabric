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
import Lean.Data.Json.FromToJson
import Init.System.IO

open Lean
open Fabric.ActionDSL

namespace ExportDFA

/-- DFA export configuration -/
structure ExportConfig where
  bundle_path : String
  output_path : String
  canonicalize : Bool := true
  include_hash : Bool := true

/-- Canonical JSON export following RFC 8785 -/
def export_canonical_json (dfa : ProductDFA) (config : ExportConfig) : IO String := do
  let dfa_table := dfa.to_table
  let exported_at ← IO.monoMsNow

  let json_obj := Json.mkObj [
    ("version", Json.str "1.0"),
    ("dfa_type", Json.str "ActionDSL_Safety"),
    ("states", Json.arr (dfa_table.states.map fun (id, accepting) =>
      Json.mkObj [
        ("id", (id : Json)),
        ("accepting", Json.bool accepting)
      ]).toArray),
    ("transitions", Json.arr (dfa_table.transitions.map fun (fromState, event, toState) =>
      Json.mkObj [
        ("from", (fromState : Json)),
        ("event", Json.str event),
        ("to", (toState : Json))
      ]).toArray),
    ("rate_limiters", Json.arr (dfa_table.rate_limiters.map fun (key, window, bound, tolerance) =>
      Json.mkObj [
        ("key", Json.str key),
        ("window", (window : Json)),
        ("bound", (bound : Json)),
        ("tolerance", (tolerance : Json))
      ]).toArray),
    ("initial_state", (dfa_table.initial_state : Json)),
    ("metadata", Json.mkObj [
      ("exported_at", Json.str (toString exported_at)),
      ("canonical", Json.bool config.canonicalize)
    ])
  ]

  return Json.pretty json_obj

/-- Export DFA to file -/
def export_dfa (config : ExportConfig) : IO Unit := do
  let dfa := compile_to_dfa []
  let json_content ← export_canonical_json dfa config

  let fp := System.FilePath.mk config.output_path
  match fp.parent with
  | none => pure ()
  | some dir => IO.FS.createDirAll dir
  IO.FS.writeFile config.output_path json_content

  IO.println s!"DFA exported to: {config.output_path}"

/-- CLI entry (invoked from module `main` below). -/
def exportMain (args : List String) : IO UInt32 := do
  let runExport (bundle_path output_path : String) : IO UInt32 := do
    export_dfa { bundle_path := bundle_path, output_path := output_path }
    return 0
  match args with
  | ["--bundle", bundle_path, "--out", output_path] =>
    runExport bundle_path output_path
  | [bundle_path, output_path] =>
    runExport bundle_path output_path
  | _ =>
    IO.println "Usage: export-dfa <bundle_path> <output_path>"
    IO.println "   or: export-dfa --bundle <bundle_path> --out <output_path>"
    return 1

end ExportDFA

def main (args : List String) : IO UInt32 :=
  ExportDFA.exportMain args
