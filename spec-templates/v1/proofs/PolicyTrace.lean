/-
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Proof template: "Given this finite trace, every event satisfies Policy P."
Decidable checker + Lean wrapper theorem; minimal and self-contained (no mathlib).
-/

namespace Spec

/-- Single event in the trace (e.g. from PF guard ledger). Policy-relevant field: allowed -/
structure Event where
  allowed : Bool
  deriving DecidableEq, Repr

/-- Policy P: an event satisfies policy iff it was allowed -/
def PolicyP (e : Event) : Prop :=
  e.allowed = true

/-- Decidable checker: true iff every event in the trace satisfies Policy P -/
def traceSatisfiesPolicy (trace : List Event) : Bool :=
  trace.foldl (fun acc e => acc && e.allowed) true

/-- All events in the list satisfy Policy P -/
def allEventsSatisfyP (trace : List Event) : Prop :=
  List.Forall PolicyP trace

/-- (a && b) = true implies a = true -/
theorem Bool.and_left_eq_true (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp at h
  try exact h
  rfl

/-- (a && b) = true implies b = true -/
theorem Bool.and_right_eq_true (a b : Bool) (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp at h
  try exact h
  rfl

/-- The checker is correct: when it returns true, every event satisfies P -/
theorem traceSatisfiesPolicy_iff_allEventsSatisfyP (trace : List Event) :
    traceSatisfiesPolicy trace = true ↔ allEventsSatisfyP trace := by
  induction trace with
  | nil => simp [traceSatisfiesPolicy, allEventsSatisfyP, PolicyP]
  | cons e rest ih =>
    simp only [traceSatisfiesPolicy, List.foldl, allEventsSatisfyP, PolicyP]
    constructor
    · intro h
      constructor
      · exact Bool.and_left_eq_true _ _ h
      · exact ih.mp (Bool.and_right_eq_true _ _ h)
    · intro ⟨hp, hrest⟩
      simp only [hp, ih.mpr hrest]

/-- Wrapper theorem: checker true implies every event satisfies Policy P -/
theorem checker_implies_policy (trace : List Event) (h : traceSatisfiesPolicy trace = true) :
    allEventsSatisfyP trace :=
  (traceSatisfiesPolicy_iff_allEventsSatisfyP trace).mp h

end Spec
