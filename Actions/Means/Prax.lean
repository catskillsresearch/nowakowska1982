/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Means.EffortDominated
public import Actions.Promise.stringDuration
import Mathlib.Tactic

@[expose] public section

/-!
# Prax and Prax min

Economy of effort (not effort-dominated among realizers) and economy of time
(minimal duration among Prax strings).
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Prax strings for a goal: members of the realizing set that are not
effort-dominated by another realizing string. -/
def Prax (realizers : Set (List A.D)) : Set (List A.D) :=
  { u ∈ realizers |
      ¬ ∃ u' ∈ realizers, A.EffortDominated u u' ∧ u ≠ u' }

namespace Prax

/-- Prax-min: Prax strings of minimal duration. -/
noncomputable def Min (realizers : Set (List A.D)) : Set (List A.D) :=
  { u ∈ A.Prax realizers |
      ∀ u' ∈ A.Prax realizers, ¬ A.stringDuration u' < A.stringDuration u }

theorem subset (realizers : Set (List A.D)) :
    A.Prax realizers ⊆ realizers := by
  intro u hu
  exact hu.1

theorem Min_subset (realizers : Set (List A.D)) :
    Min A realizers ⊆ A.Prax realizers := by
  intro u hu
  exact hu.1

/-- Example lemma: the empty set of realizers has empty Prax. -/
theorem empty : A.Prax (∅ : Set (List A.D)) = ∅ := by
  ext u
  simp [Prax]

end Prax

end ActionSystem
end Actions
