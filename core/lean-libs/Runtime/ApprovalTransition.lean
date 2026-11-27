/-
SPDX-License-Identifier: Apache-2.0
Finite approval-state transition contract. Freshness, authenticated identity,
authorization, and distinct quorum are abstract inputs, not proved facts about
the Rust implementation, clock, or deployment. No execution permit is issued.
-/
import Lean

namespace PF.Runtime.ApprovalTransition

inductive Status where
  | pending | approved | denied | expired | cancelled
  deriving DecidableEq, Repr

inductive Event where
  | approve | deny | observe
  deriving DecidableEq, Repr

def transition (s : Status) (fresh authorized quorum : Bool) (e : Event) : Status :=
  match s with
  | .pending =>
    if !fresh then .expired
    else if !authorized then .pending
    else match e with
      | .approve => if quorum then .approved else .pending
      | .deny => .denied
      | .observe => .pending
  | other => other

theorem terminal_immutable (s : Status) (f a q : Bool) (e : Event)
    (h : s ≠ .pending) : transition s f a q e = s := by
  cases s <;> simp_all [transition]

theorem stale_pending_expires (a q : Bool) (e : Event) :
    transition .pending false a q e = .expired := by
  rfl

theorem approval_requires_all (f a q : Bool) (e : Event)
    (h : transition .pending f a q e = .approved) :
    f = true ∧ a = true ∧ q = true ∧ e = .approve := by
  cases f <;> cases a <;> cases q <;> cases e <;> simp_all [transition]

theorem fresh_quorum_approves :
    transition .pending true true true .approve = .approved := by
  rfl

theorem denial_requires_authority (f a q : Bool) (e : Event)
    (h : transition .pending f a q e = .denied) :
    f = true ∧ a = true ∧ e = .deny := by
  cases f <;> cases a <;> cases q <;> cases e <;> simp_all [transition]

theorem observe_never_grants (f a q : Bool) :
    transition .pending f a q .observe ≠ .approved := by
  cases f <;> cases a <;> cases q <;> decide

def statusCode : Status → Nat
  | .pending => 0
  | .approved => 1
  | .denied => 2
  | .expired => 3
  | .cancelled => 4

def eventCode : Event → Nat
  | .approve => 0
  | .deny => 1
  | .observe => 2

def boolCode (b : Bool) : Nat := if b then 1 else 0

def table : String := Id.run do
  let mut out := ""
  for s in [Status.pending, .approved, .denied, .expired, .cancelled] do
    for f in [false, true] do
      for a in [false, true] do
        for q in [false, true] do
          for e in [Event.approve, .deny, .observe] do
            out := out ++ s!"{statusCode s}\t{boolCode f}\t{boolCode a}\t{boolCode q}\t{eventCode e}\t{statusCode (transition s f a q e)}\n"
  return out

#print axioms terminal_immutable
#print axioms stale_pending_expires
#print axioms approval_requires_all
#print axioms fresh_quorum_approves
#print axioms denial_requires_authority
#print axioms observe_never_grants

end PF.Runtime.ApprovalTransition

def main (args : List String) : IO Unit := do
  match args with
  | [path] => IO.FS.writeFile path PF.Runtime.ApprovalTransition.table
  | _ => throw (IO.userError "expected one output path")
