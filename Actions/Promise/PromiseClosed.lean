/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Promise.HatT
public import Actions.Promise.promiseSuffixLang
public import Actions.Promise.LanguageHypotheses
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

theorem mono {T : Set (List A.D)}
    (ha : A.PromiseClosed T) {x y : List A.D}
    (hxy : x ++ y ∈ A.L) (hx : x ∈ T) : x ++ y ∈ T :=
  ha hxy hx

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

/-- Positive promise CF (1982 §7 / 1973 Thm 1). Palomar novel reconstruction. -/
theorem isContextFree [Fintype A.D] [Nonempty A.D]
    {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) (hFin : A.FiniteHorizon T)
    (hL : Language.IsContextFree (A.L : Language A.D)) :
    Language.IsContextFree (T : Language A.D) := by
  have hCreg := promiseSuffixLang.isRegular A hFin
  have hEq : (T : Language A.D) =
      (A.L : Language A.D) ⊓ A.promiseSuffixLang T := by
    change (T : Set _) = (A.L ∩ A.promiseSuffixLang T : Set _)
    exact PromiseClosed.eq_L_inter_suffix A hSub ha
  rw [hEq]
  exact hL.inter_regular hCreg

end PromiseClosed

end ActionSystem
end Actions
