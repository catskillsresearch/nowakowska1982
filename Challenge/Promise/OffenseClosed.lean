/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Promise.HatU
public import Challenge.Promise.offenseSuffixLang
public import Challenge.Promise.LanguageHypotheses
public import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Tactic

@[expose] public section

/-!
# Condition (b): offense closure and offense CF
-/

open scoped Computability

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Condition (b): breaking strings are closed under two-sided admissible
embedding. -/
def OffenseClosed (U : Set (List A.D)) : Prop :=
  ∀ {x y z : List A.D}, x ++ y ++ z ∈ A.L → y ∈ U → x ++ y ++ z ∈ U

namespace OffenseClosed

theorem eq_L_inter_suffix {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) :
    U = A.L ∩ A.offenseSuffixLang U := by
  ext x
  constructor
  · intro hx
    refine ⟨hSub hx, ?_⟩
    rcases HatU.exists_prefix A hx with ⟨u, v, rfl, hu⟩
    exact ⟨u, hu, v, rfl⟩
  · intro ⟨hxL, hxC⟩
    rcases hxC with ⟨u, hu, v, rfl⟩
    have : [] ++ u ++ v ∈ A.L := by simpa using hxL
    exact hb this hu.1
-- compared Actions.ActionSystem.OffenseClosed.isContextFree in Challenge.lean
end OffenseClosed

end ActionSystem
end Actions
