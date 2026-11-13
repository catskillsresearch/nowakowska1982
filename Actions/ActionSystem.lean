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

/-- Duration of a composite string (sum of elementary durations). -/
noncomputable def stringDuration (u : List A.D) : ℝ :=
  (u.map A.φ).sum

@[simp] theorem stringDuration_nil :
    A.stringDuration [] = 0 := by
  simp [stringDuration]

@[simp] theorem stringDuration_cons (d : A.D) (u : List A.D) :
    A.stringDuration (d :: u) = A.φ d + A.stringDuration u := by
  simp [stringDuration]

/-- Longer pauses are concatenations of the pause action. -/
def pauseString (n : ℕ) : List A.D :=
  List.replicate n A.pause

theorem stringDuration_pauseString (n : ℕ) :
    A.stringDuration (A.pauseString n) = n := by
  induction n with
  | zero => simp [pauseString]
  | succ n ih =>
      calc
        A.stringDuration (A.pauseString (n + 1))
            = A.stringDuration (A.pause :: A.pauseString n) := by
              simp [pauseString, List.replicate_succ]
        _ = A.φ A.pause + A.stringDuration (A.pauseString n) := by
              simp [stringDuration]
        _ = 1 + A.stringDuration (A.pauseString n) := by rw [A.φ_pause]
        _ = 1 + (n : ℝ) := by rw [ih]
        _ = ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- A time-result is a pair `(s, t)`. -/
abbrev TimeResult := A.S × ℕ

/-- Inverse image of a time-result under `R` (eq. (2) in the paper). -/
def Rinv (s : A.S) (t : ℕ) : Set (List A.D) :=
  { u | A.R u s t }

theorem Rinv_subset_L (s : A.S) (t : ℕ) :
    A.Rinv s t ⊆ A.L := by
  intro u hu
  exact A.R_mem_L hu

/-- A time-result is attainable when its inverse image is nonempty. -/
def Attainable (s : A.S) (t : ℕ) : Prop :=
  (A.Rinv s t).Nonempty

end ActionSystem

end Actions
