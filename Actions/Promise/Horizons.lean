/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.ActionSystem
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

@[expose] public section

/-!
# Motivational horizons: conditions (a)/(b), hats, horizons

`PromiseClosed` / `OffenseClosed`, `HatT` / `HatU`, and finite-horizon
predicates from Nowakowska 1982 §7 / 1973 §5.3, plus duration helpers.
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

def PromiseClosed (T : Set (List A.D)) : Prop :=
  ∀ {x y : List A.D}, x ++ y ∈ A.L → x ∈ T → x ++ y ∈ T

def HatT (T : Set (List A.D)) : Set (List A.D) :=
  { x ∈ T |
      ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ T }

noncomputable def horizon (T : Set (List A.D)) : WithTop ℝ :=
  sSup ((A.stringDuration ·) '' A.HatT T)

def OffenseClosed (U : Set (List A.D)) : Prop :=
  ∀ {x y z : List A.D}, x ++ y ++ z ∈ A.L → y ∈ U → x ++ y ++ z ∈ U

def HatU (U : Set (List A.D)) : Set (List A.D) :=
  { v ∈ U |
      ∀ v₁ v₂, v = v₁ ++ v₂ → 0 < A.stringDuration v₂ → v₁ ∉ U }

def FiniteHorizon (T : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatT T, A.stringDuration x ≤ M

def FiniteOffenseHorizon (U : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatU U, A.stringDuration x ≤ M

def OffensePrime (U : Set (List A.D)) : Prop :=
  ∀ {u v : List A.D}, u ++ v ∈ U → u ∈ U ∨ v ∈ U

namespace PromiseClosed
theorem mono {T : Set (List A.D)}
    (ha : A.PromiseClosed T) {x y : List A.D}
    (hxy : x ++ y ∈ A.L) (hx : x ∈ T) : x ++ y ∈ T :=
  ha hxy hx
end PromiseClosed

namespace stringDuration
theorem nil_not_pos : ¬ (0 < A.stringDuration []) := by
  simp [stringDuration]

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

namespace HatT
theorem subset (T : Set (List A.D)) : A.HatT T ⊆ T := fun _ hx => hx.1
end HatT

namespace HatU
theorem subset (U : Set (List A.D)) : A.HatU U ⊆ U := fun _ hx => hx.1
end HatU

noncomputable def minφ [Fintype A.D] [Nonempty A.D] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty A.φ

namespace minφ
theorem pos [Fintype A.D] [Nonempty A.D] : 0 < A.minφ := by
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty A.φ
  simpa [minφ, hd] using A.φ_pos d
end minφ

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

open scoped Computability

/-- Classical Ch. 3 hypothesis: every regular language is context-free. -/
def RegularImpliesCF (α : Type*) : Prop :=
  ∀ L : Language α, Language.IsRegular L → Language.IsContextFree L

/-- Classical Ch. 3 hypothesis: CF languages are closed under intersection with
regular languages. -/
def CFInterRegular (α : Type*) : Prop :=
  ∀ L R : Language α,
    Language.IsContextFree L → Language.IsRegular R →
      Language.IsContextFree (L ⊓ R)

end ActionSystem
end Actions
