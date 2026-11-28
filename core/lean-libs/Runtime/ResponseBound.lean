/-
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Provability-Fabric Contributors
-/

import Lean

/-!
# Bounded HTTP response accumulation

A natural-number model of the guard in adapters/http-get/src/lib.rs:
the initial body length is zero, and each chunk is rejected if its length
exceeds the remaining budget. A successful append increases the logical
body length by the chunk length.

The model concerns logical byte counts. It does not establish a bound on
allocator capacity, transport buffers, process memory or request duration.
The correspondence to Rust assumes the observed chunk length is unchanged
during append and that successful vector append adds exactly that length.
Allocation and transport failure abort accumulation. The invariant also
bounds the addition by the configured representable usize limit.
-/

namespace PF.Runtime.ResponseBound

/-- One checked append, matching the subtraction guard in the adapter. -/
def appendLength (limit used chunk : Nat) : Option Nat :=
  if chunk ≤ limit - used then some (used + chunk) else none

/-- A successful guarded addition stays inside the original budget. -/
theorem guarded_add_le (limit used chunk : Nat)
    (hu : used ≤ limit) (hc : chunk ≤ limit - used) :
    used + chunk ≤ limit := by
  calc
    used + chunk ≤ used + (limit - used) := Nat.add_le_add_left hc used
    _ = limit := by
      rw [Nat.add_comm used (limit - used), Nat.sub_add_cancel hu]

theorem append_sound (limit used chunk result : Nat)
    (hu : used ≤ limit)
    (h : appendLength limit used chunk = some result) :
    result ≤ limit := by
  by_cases hc : chunk ≤ limit - used
  · simp [appendLength, hc] at h
    rw [← h]
    exact guarded_add_le limit used chunk hu hc
  · simp [appendLength, hc] at h

theorem oversized_rejected (limit used chunk : Nat)
    (h : ¬ chunk ≤ limit - used) :
    appendLength limit used chunk = none := by
  simp [appendLength, h]

/-- Stop on the first rejected chunk, as the adapter returns an error. -/
def collect (limit : Nat) : Nat → List Nat → Option Nat
  | used, [] => some used
  | used, chunk :: rest =>
      match appendLength limit used chunk with
      | none => none
      | some next => collect limit next rest

/-- Every successful finite collection respects its initial budget.
The one-step theorem applies at each successful prefix, including prefixes
of a collection that subsequently rejects a chunk. -/
theorem collect_sound (limit : Nat) :
    ∀ (chunks : List Nat) (used result : Nat),
      used ≤ limit → collect limit used chunks = some result → result ≤ limit := by
  intro chunks
  induction chunks with
  | nil =>
    intro used result hu h
    simp [collect] at h
    rw [← h]
    exact hu
  | cons chunk rest ih =>
    intro used result hu h
    simp only [collect] at h
    cases ha : appendLength limit used chunk with
    | none => simp [ha] at h
    | some next =>
      rw [ha] at h
      exact ih next result (append_sound limit used chunk next hu ha) h

theorem empty_start_sound (limit : Nat) (chunks : List Nat) (result : Nat)
    (h : collect limit 0 chunks = some result) : result ≤ limit :=
  collect_sound limit chunks 0 result (Nat.zero_le limit) h

example : collect 8 0 [3, 0, 5] = some 8 := by decide
example : collect 8 0 [3, 6] = none := by decide
example : collect 0 0 [0, 0] = some 0 := by decide
example : collect 0 0 [1] = none := by decide

#print axioms guarded_add_le
#print axioms append_sound
#print axioms oversized_rejected
#print axioms collect_sound
#print axioms empty_start_sound

end PF.Runtime.ResponseBound
