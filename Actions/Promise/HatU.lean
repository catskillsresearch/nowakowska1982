/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Promise.stringDuration
import Mathlib.Tactic

@[expose] public section

/-!
# First offenses \(\hat U\) and finite offense horizons
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- First offenses: in \(U\), with no nonempty positive-duration proper prefix
still in \(U\). -/
def HatU (U : Set (List A.D)) : Set (List A.D) :=
  { v ∈ U |
      ∀ v₁ v₂, v = v₁ ++ v₂ → 0 < A.stringDuration v₂ → v₁ ∉ U }

namespace HatU

theorem subset (U : Set (List A.D)) : A.HatU U ⊆ U := fun _ hx => hx.1

theorem exists_prefix {U : Set (List A.D)} {x : List A.D}
    (hx : x ∈ U) : ∃ u v, x = u ++ v ∧ u ∈ A.HatU U := by
  have : ∀ n : ℕ, ∀ x : List A.D, x.length = n → x ∈ U →
      ∃ u v, x = u ++ v ∧ u ∈ A.HatU U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hlen hx
      by_cases hhat :
          ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ U
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

end HatU

def FiniteOffenseHorizon (U : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatU U, A.stringDuration x ≤ M

def OffensePrime (U : Set (List A.D)) : Prop :=
  ∀ {u v : List A.D}, u ++ v ∈ U → u ∈ U ∨ v ∈ U

end ActionSystem
end Actions
