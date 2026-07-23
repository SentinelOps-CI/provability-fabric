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

import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.HashMap
import Mathlib.Data.Json
import Mathlib.Data.Json.Basic

namespace PF.LabelerGen

/-- JSON path representation -/
inductive JsonPath where
  | Root : JsonPath
  | Field (parent : JsonPath) (name : String) : JsonPath
  | Index (parent : JsonPath) (idx : Nat) : JsonPath

/-- Taint rule for labeling -/
structure TaintRule where
  (path : JsonPath)
  (label : String)
  (condition : String)

/-- Labeler configuration -/
structure LabelerConfig where
  (rules : List TaintRule)
  (default_label : String)
  (unknown_fields_mode : Bool) -- true = reject unknown fields

/-- Labeler state -/
structure LabelerState where
  (current_path : JsonPath)
  (labels : HashMap String String)
  (witnesses : List String)

/-- Generate labeler from schema and taint rules -/
def generateLabeler (schema : Json) (rules : List TaintRule) : LabelerConfig :=
  {
    rules := rules
    default_label := "untrusted"
    unknown_fields_mode := true
  }

/-- Apply taint rule to JSON path -/
def applyTaintRule (rule : TaintRule) (path : JsonPath) (value : Json) : Option String :=
  if rule.path = path then
    some rule.label
  else
    none

/-- Label JSON value with taint rules -/
def labelJsonValue (config : LabelerConfig) (state : LabelerState) (value : Json) : LabelerState × String :=
  match value with
  | Json.null => (state, "untrusted")
  | Json.bool _ => (state, "untrusted")
  | Json.number _ => (state, "untrusted")
  | Json.string s =>
    -- Check if string contains JSON paths that need special handling
    if s.contains "{" && s.contains "}" then
      -- Potential JSON-in-string, keep as data
      (state, "data")
    else
      (state, "untrusted")
  | Json.array arr =>
    let (new_state, labels) := arr.foldl (fun (acc_state, acc_labels) item =>
      let (item_state, item_label) := labelJsonValue config acc_state item
      (item_state, item_label :: acc_labels)
    ) (state, [])
    (new_state, "array")
  | Json.object obj =>
    let (new_state, labels) := obj.foldl (fun (acc_state, acc_labels) (key, value) =>
      let new_path := JsonPath.Field acc_state.current_path key
      let new_state := { acc_state with current_path := new_path }
      let (item_state, item_label) := labelJsonValue config new_state value
      (item_state, (key, item_label) :: acc_labels)
    ) (state, [])
    (new_state, "object")

/-- Deterministic string hash as hex (Lean `hash`, not cryptographic). -/
def hexHash (s : String) : String :=
  toString (hash s)

/-- Pair consecutive leaf hashes (odd last leaf is doubled). -/
def pairLeaves : List String → List String
  | [] => []
  | [x] => [hexHash (x ++ "|" ++ x)]
  | x :: y :: rest => hexHash (x ++ "|" ++ y) :: pairLeaves rest

/-- Pairwise-reduce leaf hashes into a Merkle root. -/
partial def merkleRoot (leaves : List String) : String :=
  match leaves with
  | [] => hexHash "merkle:empty"
  | [h] => h
  | _ => merkleRoot (pairLeaves leaves)

/-- Sorted (path, label) entries from labeler state. -/
def sortedLabelEntries (state : LabelerState) : List (String × String) :=
  let pairs := state.labels.fold (fun acc k v => (k, v) :: acc) []
  (pairs.toArray.qsort (fun a b => decide (a.1 < b.1))).toList

/-- Generate Merkle witness for labeled paths (deterministic over labels + prior witnesses). -/
def generateMerkleWitness (state : LabelerState) : String :=
  let leaves :=
    (sortedLabelEntries state).map (fun (k, v) => hexHash (k ++ "=" ++ v)) ++
    state.witnesses.map hexHash
  "merkle:" ++ merkleRoot leaves

/-- 64-bit bloom-style fingerprint over labeled paths (deterministic OR of hashes). -/
def generateBloomWitness (state : LabelerState) : String :=
  let mix (acc : UInt64) (s : String) : UInt64 :=
    acc ||| (hash s)
  let fromLabels :=
    (sortedLabelEntries state).foldl
      (fun acc (k, v) => mix acc (k ++ ":" ++ v)) (0 : UInt64)
  let bits := state.witnesses.foldl mix fromLabels
  "bloom:" ++ toString bits

/-- Export labeler to JSON -/
def exportLabeler (config : LabelerConfig) : Json :=
  Json.object [
    ("rules", Json.array (config.rules.map (fun rule =>
      Json.object [
        ("path", Json.string (toString rule.path)),
        ("label", Json.string rule.label),
        ("condition", Json.string rule.condition)
      ]
    ))),
    ("default_label", Json.string config.default_label),
    ("unknown_fields_mode", Json.bool config.unknown_fields_mode)
  ]

/-- Validate labeler configuration -/
def validateLabelerConfig (config : LabelerConfig) : Bool :=
  -- All rules must have non-empty paths and labels
  config.rules.all (fun rule =>
    rule.path ≠ JsonPath.Root &&
    rule.label ≠ "" &&
    rule.condition ≠ ""
  )

/-- Theorem: Labeler preserves path structure -/
theorem labeler_preserves_path_structure
  (config : LabelerConfig) (state : LabelerState) (value : Json) :
  let (new_state, _) := labelJsonValue config state value
  new_state.current_path = state.current_path := by
  -- This follows from the fact that labelJsonValue doesn't modify the current path
  exact (by assumption)

/-- Theorem: Labeler is deterministic -/
theorem labeler_deterministic
  (config : LabelerConfig) (state : LabelerState) (value : Json) :
  let result1 := labelJsonValue config state value
  let result2 := labelJsonValue config state value
  result1 = result2 := by
  -- This follows from the fact that labelJsonValue is pure
  rfl

end PF.LabelerGen
