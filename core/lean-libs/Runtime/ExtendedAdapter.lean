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

import ActionDSL.Extended
import Runtime.MicroInterp

/-!
# Thin Extended → MicroInterp adapter (Wave 12.2 / T13)

Maps `PF.ActionDSL.Event` / `ActionClause` into the string-keyed MicroInterp
surface so `compileClauses` / `dfa_semantics_match` apply to Extended policies
without enlarging the mathlib-free smoke compile of `Runtime.MicroInterp`.
-/

namespace PF.Runtime

/-- Canonical role label for MicroInterp event keys. -/
def roleLabel : PF.ActionDSL.Role → String
  | .User id => s!"user:{id}"
  | .Service name => s!"service:{name}"
  | .System level => s!"system:{level}"
  | .Tenant name => s!"tenant:{name}"
  | .Group name => s!"group:{name}"

/-- Canonical tool label for MicroInterp event keys. -/
def toolLabel : PF.ActionDSL.Tool → String
  | .HTTP method url => s!"http:{method}:{url}"
  | .File path mode => s!"file:{path}:{mode}"
  | .Database query => s!"db:{query}"
  | .Custom name params => s!"custom:{name}:{String.intercalate "," params}"
  | .Email recipient subject => s!"email:{recipient}:{subject}"
  | .Log level message => s!"log:{level}:{message}"

/-- Slash-joined document path segments. -/
def pathLabel (path : List String) : String :=
  String.intercalate "/" path

/-- Document identity fragment used in read/write labels. -/
def documentLabel (doc : PF.ActionDSL.Document) : String :=
  s!"{doc.id}@{doc.version}:{pathLabel doc.path}"

/-- Map an Extended event to a MicroInterp string event key. -/
def eventLabel : PF.ActionDSL.Event → Event
  | .Call role tool => s!"call|{roleLabel role}|{toolLabel tool}"
  | .Read role doc path =>
      s!"read|{roleLabel role}|{documentLabel doc}|{pathLabel path}"
  | .Write role doc path =>
      s!"write|{roleLabel role}|{documentLabel doc}|{pathLabel path}"
  | .Log message level => s!"log|{level}|{message}"
  | .Declassify fromLbl toLbl => s!"declassify|{fromLbl}|{toLbl}"
  | .Emit eventType payload => s!"emit|{eventType}|{payload}"
  | .Retrieve path hash => s!"retrieve|{path}|{hash}"

/-- Map an Extended clause to a MicroInterp clause (drops role/guard; keeps action + event key). -/
def toMicroClause (c : PF.ActionDSL.ActionClause) : ActionClause where
  action := c.action
  operation := eventLabel c.operation

/-- Map a list of Extended clauses. -/
def toMicroClauses (clauses : List PF.ActionDSL.ActionClause) : List ActionClause :=
  clauses.map toMicroClause

/-- Structural Extended match implies equal MicroInterp labels. -/
theorem eventLabel_eq_of_eventMatches (expected actual : PF.ActionDSL.Event)
    (h : PF.ActionDSL.eventMatches expected actual = true) :
    eventLabel expected = eventLabel actual := by
  cases expected <;> cases actual <;>
    simp [PF.ActionDSL.eventMatches, Bool.and_eq_true, decide_eq_true_eq] at h <;>
    (try cases h) <;>
    simp [eventLabel, roleLabel, toolLabel, documentLabel, pathLabel, *]

/-- Forbid detection on mapped clauses is label-equality against Extended forbid ops. -/
theorem forbidEvent_toMicroClauses (clauses : List PF.ActionDSL.ActionClause)
    (e : PF.ActionDSL.Event) :
    forbidEvent (toMicroClauses clauses) (eventLabel e) =
      clauses.any fun c =>
        decide (c.action = "forbid") && decide (eventLabel c.operation = eventLabel e) := by
  induction clauses with
  | nil => rfl
  | cons c rest ih =>
    simp only [toMicroClauses, List.map_cons, forbidEvent, List.any_cons, toMicroClause]
    refine congrArg
      (fun b : Bool =>
        decide (c.action = "forbid") && decide (eventLabel c.operation = eventLabel e) || b) ?_
    simpa [toMicroClauses, forbidEvent] using ih

/-- Compiled MicroInterp acceptance after mapping is forbid-freedom on Extended labels. -/
theorem accepts_toMicroClauses_iff (clauses : List PF.ActionDSL.ActionClause) (τ : Trace) :
    accepts (compileClauses (toMicroClauses clauses)) τ ↔
      ∀ stp ∈ τ, forbidEvent (toMicroClauses clauses) stp.evt = false := by
  simpa using accepts_compileClauses_iff (toMicroClauses clauses) τ

/-- Bridge: mapped Extended forbid clauses feed the existing DFA↔semantics coupling. -/
theorem dfa_semantics_match_extended (clauses : List PF.ActionDSL.ActionClause) (τ : Trace) :
    accepts (compileClauses (toMicroClauses clauses)) τ ↔
      Mediated (semanticsFromClauses (toMicroClauses clauses)) τ := by
  simpa using dfa_semantics_match (toMicroClauses clauses) τ

end PF.Runtime
