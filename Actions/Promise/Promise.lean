/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.ActionSystem
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Motivational consistency: promises

Structural conditions (a) and (b) on sets of strings that fulfill or break
a promise; minimal fulfilling strings `T̂` and first offenses `Û`; horizons.
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Condition (a): once a promise is fulfilled by `x`, every admissible
continuation `xy` remains fulfilling. (Print “is” corrected to “if”.) -/
def PromiseClosed (T : Set (List A.D)) : Prop :=
  ∀ {x y : List A.D}, x ++ y ∈ A.L → x ∈ T → x ++ y ∈ T

/-- Minimal (only-just) fulfilling strings: members of `T` with no nonempty
proper prefix still in `T`. -/
def HatT (T : Set (List A.D)) : Set (List A.D) :=
  { x ∈ T |
      ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ T }

/-- Motivational horizon of a positive promise. -/
noncomputable def horizon (T : Set (List A.D)) : WithTop ℝ :=
  sSup ((A.stringDuration ·) '' A.HatT T)

/-- Condition (b) for negative promises: if `y` breaks the promise, every
admissible embedding `xyz` also breaks it. -/
def OffenseClosed (U : Set (List A.D)) : Prop :=
  ∀ {x y z : List A.D}, x ++ y ++ z ∈ A.L → y ∈ U → x ++ y ++ z ∈ U

/-- First offenses: breaking strings with no proper prefix that already breaks. -/
def HatU (U : Set (List A.D)) : Set (List A.D) :=
  { v | ∃ u w, u ++ v ++ w ∈ U ∧ v ∈ U ∧ u ∉ U }

/-- Finite horizon for a promise set. -/
def FiniteHorizon (T : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatT T, A.stringDuration x ≤ M

/-- If `T ⊆ L` and `T` is promise-closed, concatenating on the right stays in `T`
whenever the continuation is admissible. -/
theorem promiseClosed_mono {T : Set (List A.D)}
    (ha : A.PromiseClosed T) {x y : List A.D}
    (hxy : x ++ y ∈ A.L) (hx : x ∈ T) : x ++ y ∈ T :=
  ha hxy hx

/-- Empty string has duration `0`, so it cannot be a nontrivial “only-just”
extension witness. -/
theorem stringDuration_nil_not_pos : ¬ (0 < A.stringDuration []) := by
  simp [stringDuration]

/-- `HatT T ⊆ T`. -/
theorem HatT_subset (T : Set (List A.D)) : A.HatT T ⊆ T := by
  intro x hx
  exact hx.1

end ActionSystem
end Actions
