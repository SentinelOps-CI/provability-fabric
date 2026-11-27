/-
SPDX-License-Identifier: Apache-2.0
Abstract bounded FIFO: the limit excludes the historically reserved slot.
No theorem here establishes Rust memory-model refinement or a latency bound.
-/
import Lean

namespace PF.Runtime.BoundedFIFO

def enqueue (limit : Nat) (items : List Nat) (item : Nat) : Option (List Nat) :=
  if items.length < limit then some (items ++ [item]) else none

def dequeue : List Nat → Option (Nat × List Nat)
  | [] => none
  | head :: tail => some (head, tail)

theorem enqueue_bounded (limit : Nat) (items : List Nat) (item : Nat) (next : List Nat)
    (h : enqueue limit items item = some next) : next.length ≤ limit := by
  by_cases hp : items.length < limit
  · simp [enqueue, hp] at h
    rw [← h]
    simp
    omega
  · simp [enqueue, hp] at h

theorem enqueue_appends (limit : Nat) (items : List Nat) (item : Nat) (next : List Nat)
    (h : enqueue limit items item = some next) : next = items ++ [item] := by
  by_cases hp : items.length < limit
  · simpa [enqueue, hp] using h.symm
  · simp [enqueue, hp] at h

theorem full_rejected (limit : Nat) (items : List Nat) (item : Nat)
    (h : limit ≤ items.length) : enqueue limit items item = none := by
  have hp : ¬ items.length < limit := by omega
  simp [enqueue, hp]

theorem dequeue_fifo (head : Nat) (tail : List Nat) :
    dequeue (head :: tail) = some (head, tail) := rfl

theorem empty_dequeue : dequeue [] = none := rfl

#print axioms enqueue_bounded
#print axioms enqueue_appends
#print axioms full_rejected
#print axioms dequeue_fifo
#print axioms empty_dequeue

end PF.Runtime.BoundedFIFO
