/-
SPDX-License-Identifier: Apache-2.0
Abstract exact nonnegative additive accounting. This is not a binary64 proof,
nor a proof that a claimed mechanism satisfies differential privacy.
-/
import Lean

namespace PF.Runtime.PrivacyCharge

structure Budget where
  epsilon : Nat
  delta : Nat

def within (value limit : Budget) : Prop :=
  value.epsilon ≤ limit.epsilon ∧ value.delta ≤ limit.delta

def add (used cost : Budget) : Budget :=
  ⟨used.epsilon + cost.epsilon, used.delta + cost.delta⟩

def charge (used cost limit : Budget) : Option Budget :=
  if (add used cost).epsilon ≤ limit.epsilon ∧
      (add used cost).delta ≤ limit.delta
  then some (add used cost) else none

def apply (used cost limit : Budget) : Budget :=
  (charge used cost limit).getD used

theorem accepted_bounded (used cost limit next : Budget)
    (h : charge used cost limit = some next) :
    within next limit := by
  by_cases hp : (add used cost).epsilon ≤ limit.epsilon ∧
      (add used cost).delta ≤ limit.delta
  · simp [charge, hp] at h
    rw [← h]
    exact hp
  · simp [charge, hp] at h

theorem accepted_monotone (used cost limit next : Budget)
    (h : charge used cost limit = some next) :
    within used next := by
  by_cases hp : (add used cost).epsilon ≤ limit.epsilon ∧
      (add used cost).delta ≤ limit.delta
  · simp [charge, hp] at h
    rw [← h]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · simp [charge, hp] at h

theorem rejected_unchanged (used cost limit : Budget)
    (h : charge used cost limit = none) :
    apply used cost limit = used := by
  simp [apply, h]

#print axioms accepted_bounded
#print axioms accepted_monotone
#print axioms rejected_unchanged

end PF.Runtime.PrivacyCharge
