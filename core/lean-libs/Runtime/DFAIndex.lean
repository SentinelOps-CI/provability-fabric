/-
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Provability-Fabric Contributors
-/
import Lean

/-!
Exact-symbol, partial DFA transitions. This model isolates transition
lookup from rate limits, accepting-state membership and external effects.
Row partitioning preserves first-match semantics even with repeated keys;
the Rust constructor must independently reject duplicates (it uses map
insertion). No hash function or dense-array implementation is modeled.
-/
namespace PF.Runtime.DFAIndex

structure Edge where
  source : Nat
  event : String
  target : Nat
  deriving Repr, DecidableEq

def scan (state : Nat) (event : String) : List Edge → Option Nat
  | [] => none
  | e :: rest =>
    if e.source = state ∧ e.event = event then some e.target
    else scan state event rest

def row (state : Nat) : List Edge → List (String × Nat)
  | [] => []
  | e :: rest =>
    if e.source = state then (e.event, e.target) :: row state rest
    else row state rest

def rowStep (event : String) : List (String × Nat) → Option Nat
  | [] => none
  | (symbol, target) :: rest =>
    if symbol = event then some target else rowStep event rest

/-- Partitioning by exact source state preserves every transition query,
including missing transitions, without a contiguous-ID hypothesis. -/
theorem row_refines_scan (edges : List Edge) (state : Nat) (event : String) :
    rowStep event (row state edges) = scan state event edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    by_cases hs : e.source = state
    · by_cases he : e.event = event
      · simp [row, rowStep, scan, hs, he]
      · simp [row, rowStep, scan, hs, he, ih]
    · simp [row, scan, hs, ih]

/-- Encode symbols using a policy-scoped injective map. Equality of codes
is justified only by the injectivity premise, never by hashing alone. -/
def encodedRow (code : String → Nat) :
    List (String × Nat) → List (Nat × Nat)
  | [] => []
  | (symbol, target) :: rest =>
      (code symbol, target) :: encodedRow code rest

def codeStep (code : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (symbol, target) :: rest =>
    if symbol = code then some target else codeStep code rest

theorem code_refines_row (code : String → Nat)
    (injective : ∀ a b, code a = code b → a = b)
    (event : String) (edges : List (String × Nat)) :
    codeStep (code event) (encodedRow code edges) = rowStep event edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨symbol, target⟩
    by_cases h : symbol = event
    · simp [encodedRow, codeStep, rowStep, h]
    · have hc : code symbol ≠ code event := fun he => h (injective symbol event he)
      simp [encodedRow, codeStep, rowStep, h, hc, ih]

theorem encoded_refines_scan (code : String → Nat)
    (injective : ∀ a b, code a = code b → a = b)
    (edges : List Edge) (state : Nat) (event : String) :
    codeStep (code event) (encodedRow code (row state edges)) =
      scan state event edges := by
  rw [code_refines_row code injective, row_refines_scan]

/-- Pure transition traces stop on the first absent edge. -/
def run (step : Nat → String → Option Nat) : Nat → List String → Option Nat
  | state, [] => some state
  | state, event :: rest =>
    match step state event with
    | none => none
    | some next => run step next rest

theorem trace_refinement (edges : List Edge) (state : Nat) (events : List String) :
    run (fun s e => rowStep e (row s edges)) state events =
      run (fun s e => scan s e edges) state events := by
  have h : (fun s e => rowStep e (row s edges)) =
      (fun s e => scan s e edges) := by
    funext s e
    exact row_refines_scan edges s e
  rw [h]

-- Keep this fixture synchronized with Rust reference_table in dfa_equiv.rs.
def fixture : List Edge :=
  [⟨42, "call(tool1,hash1)", 7⟩,
   ⟨7, "call(tool2,hash1)", 256⟩,
   ⟨7, "call(tool1,hash1)", 7⟩,
   ⟨256, "log(hash1)", 900⟩,
   ⟨256, "log(hash2)", 42⟩,
   ⟨900, "emit(plan1)", 42⟩]

def states : List Nat := [900, 42, 7, 256, 999]
def alphabet : List String :=
  ["call(tool1,hash1)", "call(tool2,hash1)", "call(tool1,hash2)",
   "log(hash1)", "log(hash2)", "emit(plan1)", "emit(plan2)", "unknown"]

def matrixRow (state : Nat) : String :=
  String.intercalate "" (alphabet.map fun event =>
    let expected := match scan state event fixture with
      | some target => toString target
      | none => "reject"
    s!"{state}\t{event}\t{expected}\n")

def matrix : String :=
  String.intercalate "" (states.map matrixRow)

#print axioms row_refines_scan
#print axioms code_refines_row
#print axioms encoded_refines_scan
#print axioms trace_refinement

end PF.Runtime.DFAIndex

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    IO.FS.writeFile path PF.Runtime.DFAIndex.matrix
    return 0
  | _ =>
    IO.eprintln "usage: lean --run Runtime/DFAIndex.lean OUTPUT"
    return 1
