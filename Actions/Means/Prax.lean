/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Attainability.Goals
import Mathlib.Tactic

@[expose] public section

/-!
# Algebra of means: Prax and Prax min

Economy of effort (replaceable actions by pause) and economy of time
(minimal duration among Prax strings).
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Pointwise “effort domination”: same length, and at every index the right
string is either equal or a pause replacing a non-pause. -/
def EffortDominated (u u' : List A.D) : Prop :=
  ∃ hlen : u.length = u'.length,
    ∀ i (hi : i < u.length),
      u[i] = u'[i]'(hlen ▸ hi) ∨
        (u'[i]'(hlen ▸ hi) = A.pause ∧ u[i] ≠ A.pause)

/-- Prax strings for a goal: members of the realizing set that are not
effort-dominated by another realizing string. -/
def Prax (realizers : Set (List A.D)) : Set (List A.D) :=
  { u ∈ realizers |
      ¬ ∃ u' ∈ realizers, A.EffortDominated u u' ∧ u ≠ u' }

/-- Prax-min: Prax strings of minimal duration. -/
noncomputable def PraxMin (realizers : Set (List A.D)) : Set (List A.D) :=
  { u ∈ A.Prax realizers |
      ∀ u' ∈ A.Prax realizers, ¬ A.stringDuration u' < A.stringDuration u }

theorem Prax_subset (realizers : Set (List A.D)) :
    A.Prax realizers ⊆ realizers := by
  intro u hu
  exact hu.1

theorem PraxMin_subset_Prax (realizers : Set (List A.D)) :
    A.PraxMin realizers ⊆ A.Prax realizers := by
  intro u hu
  exact hu.1

/-- Example lemma: the empty set of realizers has empty Prax. -/
theorem Prax_empty : A.Prax (∅ : Set (List A.D)) = ∅ := by
  ext u
  simp [Prax]

/-- Reflexivity of effort domination (equal strings). -/
theorem EffortDominated.refl (u : List A.D) : A.EffortDominated u u := by
  refine ⟨rfl, ?_⟩
  intro i hi
  left
  rfl

end ActionSystem
end Actions
