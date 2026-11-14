/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Promise.HatT
public import Challenge.Promise.promiseSuffixLang
public import Challenge.Promise.LanguageHypotheses
public import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Tactic

@[expose] public section

/-!
# Condition (a): promise closure and positive CF
-/

open scoped Computability

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Condition (a): fulfilling strings are closed under admissible right
continuation. -/
def PromiseClosed (T : Set (List A.D)) : Prop :=
  ∀ {x y : List A.D}, x ++ y ∈ A.L → x ∈ T → x ++ y ∈ T

namespace PromiseClosed
-- compared Actions.ActionSystem.PromiseClosed.mono in Challenge.lean
theorem eq_L_inter_suffix {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) :
    T = A.L ∩ A.promiseSuffixLang T := by
  ext x
  constructor
  · intro hx
    refine ⟨hSub hx, ?_⟩
    rcases HatT.exists_prefix A hx with ⟨u, v, rfl, hu⟩
    exact ⟨u, hu, v, rfl⟩
  · intro ⟨hxL, hxC⟩
    rcases hxC with ⟨u, hu, v, rfl⟩
    exact ha hxL hu.1
-- compared Actions.ActionSystem.PromiseClosed.isContextFree in Challenge.lean
end PromiseClosed

end ActionSystem
end Actions
