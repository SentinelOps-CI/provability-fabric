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

/-!
# Runtime micro-interpreter and ActionDSL↔DFA coupling (F33 / P4)

Lands P4.1–P4.3 generator coupling that previously blocked `dfa_semantics_match`.
Types are self-contained (string-keyed events/clauses) so this lake target builds
without depending on the unfinished `ActionDSL.Extended` surface. A later thin
adapter can map Extended clauses into `ActionClause` once that module compiles.
-/

namespace PF.Runtime

/-- Runtime event label (string-keyed; adapter target for Extended.Event). -/
abbrev Event := String

/-- Role / tool placeholders for semantics.Allowed. -/
abbrev Role := String
abbrev Tool := String

/-- Interpreter state placeholder. -/
structure State where
  label : String := ""
  deriving Repr, BEq, DecidableEq

/-- One mediated step. -/
structure Step where
  st : State
  evt : Event
  st' : State
  deriving Repr, BEq, DecidableEq

/-- Trace of steps. -/
abbrev Trace := List Step

/-- Minimal ActionDSL clause used by the DFA compiler.

`action` is `"allow"` or `"forbid"`. `operation` is the event label matched
by equality. -/
structure ActionClause where
  action : String
  operation : Event
  deriving Repr, BEq, DecidableEq

/-- Sidecar witness type for mediation (runtime-facing). -/
inductive SidecarWitness where
  | dfa_accept (ok : Bool) (event : Event) : SidecarWitness
  | rate_limit_ok (tool : String) (window : Nat) (bound : Nat) : SidecarWitness
  | declassify_rule (from_lbl : String) (to_lbl : String) : SidecarWitness
  | label_witness (path : String) (hash : String) : SidecarWitness
  | effect_signature (tool : String) (effects : List String) : SidecarWitness

/-- Semantics structure as specified in the paper. -/
structure Semantics where
  Allowed : Role → Tool → Prop
  SidecarWitness : Type
  Checked : Step → SidecarWitness → Prop
  Invariants : List (Trace → Prop)
  NonInterf : Trace → Prop

/-- Mediated trace predicate: every step carries a checked witness. -/
inductive Mediated (sem : Semantics) : Trace → Prop where
  | nil : Mediated sem []
  | cons (stp : Step) (w : sem.SidecarWitness)
      (h : sem.Checked stp w) (τ : Trace)
      (ih : Mediated sem τ) : Mediated sem (stp :: τ)

/-- Conjunction of invariants. -/
def Conj (Invs : List (Trace → Prop)) (τ : Trace) : Prop :=
  ∀ inv ∈ Invs, inv τ

/-- Bundle safety type. -/
def BundleSafeType (sem : Semantics) :=
  (τ : Trace) → Mediated sem τ →
  (Conj sem.Invariants τ ∧ sem.NonInterf τ)

/-- Deterministic finite automaton over events. -/
structure DFAM (σ : Type) where
  start : σ
  acc : σ → Bool
  δ : σ → Event → σ

/-- Small-step interpreter state. -/
structure IState (σ : Type) where
  σ : σ
  st : State

/-- One interpreter step. -/
def interp_step {σ : Type} (M : DFAM σ) (is : IState σ) (evt : Event) (st' : State) :
    IState σ × Step :=
  let σ' := M.δ is.σ evt
  (⟨σ', st'⟩, ⟨is.st, evt, st'⟩)

/-- Interpreter run. -/
def interp_run {σ : Type} (M : DFAM σ) (init : IState σ)
    (es : List (Event × State)) : IState σ × Trace :=
  match es with
  | [] => (init, [])
  | (evt, st') :: rest =>
    let (next_state, step) := interp_step M init evt st'
    let (final_state, trace) := interp_run M next_state rest
    (final_state, step :: trace)

/-- Fold δ from an explicit start state, then test acceptance. -/
def acceptsFrom {σ : Type} (M : DFAM σ) (start : σ) : Trace → Bool
  | [] => M.acc start
  | step :: rest => acceptsFrom M (M.δ start step.evt) rest

/-- DFA acceptance on a trace. -/
def accepts {σ : Type} (M : DFAM σ) (τ : Trace) : Prop :=
  acceptsFrom M M.start τ = true

/-- True when any forbid clause matches the event. -/
def forbidEvent (clauses : List ActionClause) (evt : Event) : Bool :=
  clauses.any fun c => decide (c.action = "forbid") && decide (c.operation = evt)

/-- P4.1 — compile ActionDSL clauses to a 2-state DFA (ok / rejected). -/
def compileClauses (clauses : List ActionClause) : DFAM Bool where
  start := true
  acc := fun s => s
  δ := fun s evt => s && !forbidEvent clauses evt

/-- P4.2 — semantics builder from the same clauses. -/
def semanticsFromClauses (clauses : List ActionClause) : Semantics where
  Allowed := fun _ _ => True
  SidecarWitness := Unit
  Checked := fun stp _ => forbidEvent clauses stp.evt = false
  Invariants := []
  NonInterf := fun _ => True

/-- Compiled pair from one clause list (generator coupling). -/
def compilePair (clauses : List ActionClause) : DFAM Bool × Semantics :=
  (compileClauses clauses, semanticsFromClauses clauses)

/-- From a rejecting state the compiled DFA never recovers. -/
theorem acceptsFrom_false (clauses : List ActionClause) (τ : Trace) :
    acceptsFrom (compileClauses clauses) false τ = false := by
  induction τ with
  | nil => rfl
  | cons _ _ ih => simpa [acceptsFrom, compileClauses] using ih

/-- Acceptance from `true` iff every event is non-forbidden. -/
theorem acceptsFrom_true_iff (clauses : List ActionClause) (τ : Trace) :
    acceptsFrom (compileClauses clauses) true τ = true ↔
      ∀ stp ∈ τ, forbidEvent clauses stp.evt = false := by
  induction τ with
  | nil =>
    constructor
    · intro _; intro stp h; cases h
    · intro _; rfl
  | cons stp rest ih =>
    constructor
    · intro hacc s hs
      have hδ :
          acceptsFrom (compileClauses clauses)
            (!forbidEvent clauses stp.evt) rest = true := by
        simpa [acceptsFrom, compileClauses] using hacc
      cases hf : forbidEvent clauses stp.evt with
      | true =>
        simp [hf, acceptsFrom_false] at hδ
      | false =>
        cases hs with
        | head => exact hf
        | tail _ hin =>
          have hacc' : acceptsFrom (compileClauses clauses) true rest = true := by
            simpa [hf, compileClauses] using hδ
          exact (ih.mp hacc') s hin
    · intro hall
      have h0 : forbidEvent clauses stp.evt = false := hall stp (.head _)
      have hrest : ∀ s ∈ rest, forbidEvent clauses s.evt = false := fun s hs =>
        hall s (.tail _ hs)
      have hacc' := ih.mpr hrest
      simpa [acceptsFrom, compileClauses, h0] using hacc'

theorem accepts_compileClauses_iff (clauses : List ActionClause) (τ : Trace) :
    accepts (compileClauses clauses) τ ↔
      ∀ stp ∈ τ, forbidEvent clauses stp.evt = false := by
  simpa [accepts, compileClauses] using acceptsFrom_true_iff clauses τ

theorem mediated_semanticsFromClauses_iff (clauses : List ActionClause) (τ : Trace) :
    Mediated (semanticsFromClauses clauses) τ ↔
      ∀ stp ∈ τ, forbidEvent clauses stp.evt = false := by
  induction τ with
  | nil =>
    constructor
    · intro _; intro stp h; cases h
    · intro _; exact Mediated.nil
  | cons stp rest ih =>
    constructor
    · intro hmem s hs
      cases hmem with
      | cons _ w hchk τ' ih' =>
        cases hs with
        | head => simpa [semanticsFromClauses] using hchk
        | tail _ hin => exact (ih.mp ih') s hin
    · intro hall
      refine
        Mediated.cons stp
          (show (semanticsFromClauses clauses).SidecarWitness from ()) ?_ rest ?_
      · simpa [semanticsFromClauses] using hall stp (.head _)
      · exact ih.mpr fun s hs => hall s (.tail _ hs)

/-- P4.3 — DFA acceptance matches mediated semantics for the compiled pair. -/
theorem dfa_semantics_match (clauses : List ActionClause) (τ : Trace) :
    accepts (compileClauses clauses) τ ↔
      Mediated (semanticsFromClauses clauses) τ := by
  constructor
  · intro hacc
    exact (mediated_semanticsFromClauses_iff clauses τ).mpr
      ((accepts_compileClauses_iff clauses τ).mp hacc)
  · intro hmed
    exact (accepts_compileClauses_iff clauses τ).mpr
      ((mediated_semanticsFromClauses_iff clauses τ).mp hmed)

/-- Events of an interpreter-produced trace are exactly the input events. -/
theorem interp_run_events {σ : Type} (M : DFAM σ) (init : IState σ)
    (es : List (Event × State)) :
    ((interp_run M init es).2.map (·.evt)) = es.map (·.1) := by
  induction es generalizing init with
  | nil => rfl
  | cons head rest ih =>
    cases head
    simp [interp_run, interp_step, ih]

/-- Compiled interpreter run is mediated and accepted when no event is forbidden. -/
theorem micro_refine_compiled
    (clauses : List ActionClause)
    (init : IState Bool)
    (es : List (Event × State))
    (h_ok : ∀ p ∈ es, forbidEvent clauses p.1 = false) :
    Mediated (semanticsFromClauses clauses) (interp_run (compileClauses clauses) init es).2 ∧
      accepts (compileClauses clauses) (interp_run (compileClauses clauses) init es).2 := by
  let M := compileClauses clauses
  let τ := (interp_run M init es).2
  have hevents := interp_run_events M init es
  have hall : ∀ stp ∈ τ, forbidEvent clauses stp.evt = false := by
    intro stp hstp
    have hin : stp.evt ∈ es.map (·.1) := by
      have := List.mem_map_of_mem (fun s : Step => s.evt) hstp
      simpa [τ, hevents] using this
    obtain ⟨p, hp, hp_eq⟩ := List.mem_map.mp hin
    simpa [hp_eq.symm] using h_ok p hp
  exact ⟨
    (mediated_semanticsFromClauses_iff clauses τ).mpr hall,
    (accepts_compileClauses_iff clauses τ).mpr hall
  ⟩

/-- Empty invariant list + trivial NI ⇒ safety components for compiled semantics. -/
theorem refinement_preserves_safety_compiled
    (clauses : List ActionClause) (τ : Trace)
    (_h : Mediated (semanticsFromClauses clauses) τ) :
    Conj (semanticsFromClauses clauses).Invariants τ ∧
      (semanticsFromClauses clauses).NonInterf τ := by
  constructor
  · intro inv hin
    simp [semanticsFromClauses] at hin
  · simp [semanticsFromClauses]

end PF.Runtime
