/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Basic.ActionSystem
import Mathlib.Tactic

@[expose] public section

/-!
# Algebra of goals: weak and strong attainability

Nowakowska (1982), §4: configurations of time-results, with weak attainability
as nonempty union of inverse images and strong attainability as nonempty
intersection (editorial correction of the printed union typo for “strongly”).
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Finite list of time-results forming a composite goal set `C`. -/
abbrev GoalSet := List A.TimeResult

/-- Strings bringing about the disjunction of all time-results in `C`
(weak goal: at least one). -/
def RinvUnion (C : GoalSet A) : Set (List A.D) :=
  { u | ∃ st ∈ C, u ∈ A.Rinv st.1 st.2 }

/-- Strings bringing about the conjunction of all time-results in `C`
(strong goal: all of them). -/
def RinvInter (C : GoalSet A) : Set (List A.D) :=
  { u | ∀ st ∈ C, u ∈ A.Rinv st.1 st.2 }

/-- Weak attainability: `⋃ R⁻¹(sᵢ,tᵢ) ≠ ∅`. -/
def WeaklyAttainable (C : GoalSet A) : Prop :=
  (A.RinvUnion C).Nonempty

/-- Strong attainability: `⋂ R⁻¹(sᵢ,tᵢ) ≠ ∅`. -/
def StronglyAttainable (C : GoalSet A) : Prop :=
  (A.RinvInter C).Nonempty

/-- Strong attainability implies weak attainability whenever `C` is nonempty. -/
theorem strongly_implies_weakly {C : GoalSet A} (hC : C ≠ [])
    (h : A.StronglyAttainable C) : A.WeaklyAttainable C := by
  obtain ⟨u, hu⟩ := h
  match C, hC with
  | [], hne => exact (hne rfl).elim
  | st :: rest, _ =>
      have hmem : st ∈ st :: rest := by simp
      exact ⟨u, st, hmem, hu st hmem⟩

/-- Negation of a time-result: strings in `L` that do not cause `(s,t)`. -/
def RinvNeg (s : A.S) (t : ℕ) : Set (List A.D) :=
  A.L \ A.Rinv s t

/-- Internal conflict: desirable goals that are weakly but not strongly attainable. -/
def MotiveConflict (C : GoalSet A) : Prop :=
  A.WeaklyAttainable C ∧ ¬ A.StronglyAttainable C

/-- On a singleton goal set, weak and strong attainability coincide. -/
theorem weakly_iff_strongly_singleton (st : A.TimeResult) :
    A.WeaklyAttainable [st] ↔ A.StronglyAttainable [st] := by
  constructor
  · intro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    intro st' hst'
    simp only [List.mem_singleton] at hst'
    subst hst'
    obtain ⟨st'', hmem, hR⟩ := hu
    simp only [List.mem_singleton] at hmem
    subst hmem
    exact hR
  · intro ⟨u, hu⟩
    exact ⟨u, ⟨st, List.mem_singleton_self st, hu st (List.mem_singleton_self st)⟩⟩

end ActionSystem
end Actions
