/-
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Provability-Fabric Contributors
-/
import Lean

namespace PF.Runtime.EvidenceAccess

structure Credential where
  tenant : Nat
  read : Bool
  write : Bool

def permitted (c : Credential) (requested : Option Nat) (write : Bool) : Prop :=
  (if write then c.write else c.read) = true ∧
  (requested = none ∨ requested = some c.tenant)

def scope (credential : Option Credential) (requested : Option Nat)
    (write : Bool) : Option Nat :=
  match credential with
  | none => none
  | some c =>
    if (if write then c.write else c.read) = true ∧
        (requested = none ∨ requested = some c.tenant)
    then some c.tenant else none

theorem unauthenticated_denied (requested : Option Nat) (write : Bool) :
    scope none requested write = none := rfl

theorem scope_sound (c : Credential) (requested : Option Nat) (write : Bool)
    (result : Nat) (h : scope (some c) requested write = some result) :
    result = c.tenant ∧ permitted c requested write := by
  by_cases hp : (if write then c.write else c.read) = true ∧
      (requested = none ∨ requested = some c.tenant)
  · simp [scope, hp] at h
    exact ⟨h.symm, hp⟩
  · simp [scope, hp] at h

theorem scope_complete (c : Credential) (requested : Option Nat) (write : Bool)
    (h : permitted c requested write) :
    scope (some c) requested write = some c.tenant := by
  simpa [scope, permitted] using h

theorem cross_tenant_denied (c : Credential) (other : Nat) (write : Bool)
    (h : other ≠ c.tenant) :
    scope (some c) (some other) write = none := by
  simp [scope, h]

theorem missing_permission_denied (c : Credential) (requested : Option Nat)
    (write : Bool) (h : (if write then c.write else c.read) = false) :
    scope (some c) requested write = none := by
  simp [scope, h]

#print axioms unauthenticated_denied
#print axioms scope_sound
#print axioms scope_complete
#print axioms cross_tenant_denied
#print axioms missing_permission_denied

end PF.Runtime.EvidenceAccess

-- Exhaust the finite decision partition: recognized/unrecognized credential,
-- both permission bits, absent/matching/different request, read/write.
-- This abstracts successful token recognition and nonempty tenant identifiers.
def main : IO Unit := do
  for authenticated in [false, true] do
    for read in [false, true] do
      for write in [false, true] do
        for requested in [0, 1, 2] do
          for op in [false, true] do
            let c : PF.Runtime.EvidenceAccess.Credential := ⟨1, read, write⟩
            let credential := if authenticated then some c else none
            let tenant := if requested == 0 then none else some requested
            let result := PF.Runtime.EvidenceAccess.scope credential tenant op
            IO.println s!"CASE {authenticated} {read} {write} {requested} {op} {result.getD 0}"
