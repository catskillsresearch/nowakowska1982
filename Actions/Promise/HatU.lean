/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Promise.stringDuration
import Mathlib.Tactic

@[expose] public section

/-!
# Factor-minimal first offenses \(\hat U\) and finite offense horizons

Following Nowakowska 1973 §5.3.3 / 1982 §7: a first offense is a member of
`U` with no proper positive-duration factor still in `U`.
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Factor-minimal first offenses: `v ∈ U` with no proper positive-duration
infix still in `U`. -/
def HatU (U : Set (List A.D)) : Set (List A.D) :=
  { v ∈ U |
      ∀ x y z, v = x ++ y ++ z →
        0 < A.stringDuration x + A.stringDuration z → y ∉ U }

namespace HatU

theorem subset (U : Set (List A.D)) : A.HatU U ⊆ U := fun _ hx => hx.1

private theorem length_lt_of_pos_sides {x y z : List A.D}
    (hpos : 0 < A.stringDuration x + A.stringDuration z) :
    y.length < (x ++ y ++ z).length := by
  have hxz : x ≠ [] ∨ z ≠ [] := by
    by_contra h
    push Not at h
    rcases h with ⟨hx0, hz0⟩
    subst hx0; subst hz0
    simp [stringDuration] at hpos
  simp only [List.length_append]
  cases hxz with
  | inl hx0 =>
      have := List.length_pos_of_ne_nil hx0
      omega
  | inr hz0 =>
      have := List.length_pos_of_ne_nil hz0
      omega

/-- Every member of `U` factors as `x ++ v ++ z` with `v` factor-minimal. -/
theorem exists_factor {U : Set (List A.D)} {w : List A.D}
    (hw : w ∈ U) : ∃ x v z, w = x ++ v ++ z ∧ v ∈ A.HatU U := by
  have : ∀ n : ℕ, ∀ w : List A.D, w.length = n → w ∈ U →
      ∃ x v z, w = x ++ v ++ z ∧ v ∈ A.HatU U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hlen hw
      by_cases hhat :
          ∀ x y z, w = x ++ y ++ z →
            0 < A.stringDuration x + A.stringDuration z → y ∉ U
      · exact ⟨[], w, [], by simp, ⟨hw, hhat⟩⟩
      · push Not at hhat
        rcases hhat with ⟨x, y, z, rfl, hpos, hy⟩
        have hlen_y : y.length < n := by
          rw [← hlen]
          exact length_lt_of_pos_sides (A := A) hpos
        rcases ih _ hlen_y y rfl hy with ⟨x', v, z', rfl, hv⟩
        exact ⟨x ++ x', v, z' ++ z, by simp [List.append_assoc], hv⟩
  exact this w.length w rfl hw

/-- Under a duration bound, \(\hat U\) is finite. -/
theorem finite_of_horizon [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)} {M : ℝ}
    (hM : ∀ x ∈ A.HatU U, A.stringDuration x ≤ M) :
    (A.HatU U).Finite :=
  (A.finite_bounded_duration M).subset fun _ hx => hM _ hx

end HatU

def FiniteOffenseHorizon (U : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatU U, A.stringDuration x ≤ M

/-- Primality: membership is inherited by a nonempty factor split (1973). -/
def OffensePrime (U : Set (List A.D)) : Prop :=
  ∀ {u v : List A.D}, u ++ v ∈ U → u ∈ U ∨ v ∈ U

end ActionSystem
end Actions
