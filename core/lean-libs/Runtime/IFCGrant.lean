/-
SPDX-License-Identifier: Apache-2.0
Abstract grant relation, not a proof of Rust bitset layout or authorization
of the grant operation itself.
-/
import Lean

namespace PF.Runtime.IFCGrant

abbrev Key := Nat × Nat × Nat
abbrev Grants := Key → Bool

def grant (old : Grants) (key : Key) : Grants :=
  fun requested => if requested = key then true else old requested

def clear : Grants := fun _ => false

theorem grant_exact (old : Grants) (key : Key) :
    grant old key key = true := by
  simp [grant]

theorem other_key_unchanged (old : Grants) (key requested : Key)
    (h : requested ≠ key) :
    grant old key requested = old requested := by
  simp [grant, h]

theorem grant_monotone (old : Grants) (key requested : Key)
    (h : old requested = true) :
    grant old key requested = true := by
  by_cases heq : requested = key
  · simp [grant, heq]
  · simp [grant, heq, h]

theorem clear_denies (key : Key) : clear key = false := rfl

#print axioms grant_exact
#print axioms other_key_unchanged
#print axioms grant_monotone
#print axioms clear_denies

end PF.Runtime.IFCGrant
