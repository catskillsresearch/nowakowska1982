/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Nowakowska action system (sixtuplet)

Formalization of the primitive system
`⟨D, #, φ, L, S, R⟩` from Nowakowska, *A Formal Theory of Actions* (1982).
-/

namespace Actions

/-- Elementary actions, distinguished pause, duration, language of actions,
outcomes, and the causation relation `R`. -/
structure ActionSystem where
  /-- Alphabet of elementary actions. -/
  D : Type*
  /-- Distinguished pause action. -/
  pause : D
  /-- Duration of an elementary action (positive for every action). -/
  φ : D → ℝ
  φ_pos : ∀ d, 0 < φ d
  /-- Duration of a pause is `1`. -/
  φ_pause : φ pause = 1
  /-- Outcomes of interest. -/
  S : Type*
  /-- Admissible strings (`L ⊆ D*`). -/
  L : Set (List D)
  /-- Causation: string `u` brings about outcome `s` at discrete time `t`.
  Time is specialized to `ℕ` (Nowakowska’s countable time moments). -/
  R : List D → S → ℕ → Prop
  /-- Only admissible strings stand in `R`. -/
  R_mem_L : ∀ {u s t}, R u s t → u ∈ L

namespace ActionSystem

variable (A : ActionSystem)

/-- Longer pauses are concatenations of the pause action. -/
def pauseString (n : ℕ) : List A.D :=
  List.replicate n A.pause

/-- A time-result is a pair `(s, t)`. -/
abbrev TimeResult := A.S × ℕ

/-- Inverse image of a time-result under `R` (eq. (2) in the paper). -/
def Rinv (s : A.S) (t : ℕ) : Set (List A.D) :=
  { u | A.R u s t }
-- compared Actions.ActionSystem.Rinv_subset_L in Challenge.lean
def Attainable (s : A.S) (t : ℕ) : Prop :=
  (A.Rinv s t).Nonempty

end ActionSystem

end Actions
