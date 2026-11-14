/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Promise.stringDuration
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Minimal fulfilling strings \(\hat T\) and finite horizons
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Minimal fulfilling strings: in \(T\), with no nonempty positive-duration
proper prefix still in \(T\). -/
def HatT (T : Set (List A.D)) : Set (List A.D) :=
  { x ∈ T |
      ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ T }

namespace HatT
-- compared Actions.ActionSystem.HatT.subset in Challenge.lean
theorem exists_prefix {T : Set (List A.D)} {x : List A.D}
    (hx : x ∈ T) : ∃ u v, x = u ++ v ∧ u ∈ A.HatT T := by
  have : ∀ n : ℕ, ∀ x : List A.D, x.length = n → x ∈ T →
      ∃ u v, x = u ++ v ∧ u ∈ A.HatT T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hlen hx
      by_cases hhat :
          ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ T
      · exact ⟨x, [], by simp, ⟨hx, hhat⟩⟩
      · push Not at hhat
        rcases hhat with ⟨x₁, x₂, rfl, hpos, hx₁⟩
        have hx₂ : x₂ ≠ [] := fun h => by simp [h, stringDuration] at hpos
        have hlen₁ : x₁.length < n := by
          rw [← hlen, List.length_append]
          have : 0 < x₂.length := List.length_pos_of_ne_nil hx₂
          omega
        rcases ih _ hlen₁ x₁ rfl hx₁ with ⟨u, v, rfl, hu⟩
        exact ⟨u, v ++ x₂, by simp [List.append_assoc], hu⟩
  exact this x.length x rfl hx

end HatT

noncomputable def horizon (T : Set (List A.D)) : WithTop ℝ :=
  sSup ((A.stringDuration ·) '' A.HatT T)

def FiniteHorizon (T : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatT T, A.stringDuration x ≤ M

end ActionSystem
end Actions
