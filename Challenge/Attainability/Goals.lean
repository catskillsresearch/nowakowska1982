/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.ActionSystem
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
-- compared Actions.ActionSystem.strongly_implies_weakly in Challenge.lean
def RinvNeg (s : A.S) (t : ℕ) : Set (List A.D) :=
  A.L \ A.Rinv s t

/-- Internal conflict: desirable goals that are weakly but not strongly attainable. -/
def MotiveConflict (C : GoalSet A) : Prop :=
  A.WeaklyAttainable C ∧ ¬ A.StronglyAttainable C
-- compared Actions.ActionSystem.weakly_iff_strongly_singleton in Challenge.lean
end ActionSystem
end Actions
