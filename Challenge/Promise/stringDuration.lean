/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Promise.minφ
public import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

@[expose] public section

/-!
# String duration
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Duration of a composite string (sum of elementary durations). -/
noncomputable def stringDuration (u : List A.D) : ℝ :=
  (u.map A.φ).sum

@[simp] theorem stringDuration_nil :
    A.stringDuration [] = 0 := by
  simp [stringDuration]

@[simp] theorem stringDuration_cons (d : A.D) (u : List A.D) :
    A.stringDuration (d :: u) = A.φ d + A.stringDuration u := by
  simp [stringDuration]
-- compared Actions.ActionSystem.stringDuration_pauseString in Challenge.lean
namespace stringDuration
-- compared Actions.ActionSystem.stringDuration.nil_not_pos in Challenge.lean
theorem append (x y : List A.D) :
    A.stringDuration (x ++ y) = A.stringDuration x + A.stringDuration y := by
  induction x with
  | nil => simp [stringDuration]
  | cons d x ih =>
      rw [List.cons_append, stringDuration_cons, stringDuration_cons, ih]
      ring

theorem nonneg (x : List A.D) : 0 ≤ A.stringDuration x := by
  induction x with
  | nil => simp [stringDuration]
  | cons d x ih =>
      have hφ := A.φ_pos d
      rw [stringDuration_cons]
      linarith

theorem pos_of_ne_nil {x : List A.D} (hx : x ≠ []) :
    0 < A.stringDuration x := by
  match x with
  | [] => cases hx rfl
  | d :: x =>
      have hφ := A.φ_pos d
      have h := stringDuration.nonneg A x
      rw [stringDuration_cons]
      linarith

end stringDuration

theorem le_stringDuration_length [Fintype A.D] [Nonempty A.D] (x : List A.D) :
    (x.length : ℝ) * A.minφ ≤ A.stringDuration x := by
  induction x with
  | nil => simp [stringDuration]
  | cons d x ih =>
      have hd : A.minφ ≤ A.φ d := Finset.inf'_le _ (Finset.mem_univ d)
      rw [List.length_cons, stringDuration_cons]
      push_cast
      nlinarith

theorem finite_bounded_duration [Fintype A.D] [Nonempty A.D] (M : ℝ) :
    { x : List A.D | A.stringDuration x ≤ M }.Finite := by
  classical
  by_cases hM : M < 0
  · have : { x : List A.D | A.stringDuration x ≤ M } = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      have := stringDuration.nonneg A x
      linarith
    simp [this]
  · have hmin := minφ.pos A
    let N : ℕ := Nat.floor (M / A.minφ) + 1
    have hsub : { x : List A.D | A.stringDuration x ≤ M } ⊆
        { x : List A.D | x.length < N } := by
      intro x hx
      have hle : (x.length : ℝ) * A.minφ ≤ M :=
        le_trans (A.le_stringDuration_length x) hx
      have hdiv : (x.length : ℝ) ≤ M / A.minφ := (le_div_iff₀ hmin).mpr hle
      have : (x.length : ℝ) < (N : ℝ) := by
        have := lt_of_le_of_lt hdiv (Nat.lt_floor_add_one (M / A.minφ))
        simpa [N] using this
      exact_mod_cast this
    exact (List.finite_length_lt A.D N).subset hsub

end ActionSystem
end Actions
