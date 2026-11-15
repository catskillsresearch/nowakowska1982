/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Promise.HatU
public import Actions.Promise.offenseSuffixLang
public import Actions.Promise.LanguageHypotheses
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

/-- Under condition (b), `U` is exactly the admissible strings containing a
factor-minimal first offense as an infix. -/
theorem eq_L_inter_suffix {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) :
    U = A.L ∩ A.offenseSuffixLang U := by
  ext x
  constructor
  · intro hx
    refine ⟨hSub hx, ?_⟩
    rcases HatU.exists_factor A hx with ⟨pref, v, suff, rfl, hv⟩
    exact ⟨pref, v, suff, hv, rfl⟩
  · rintro ⟨hxL, pref, v, suff, hv, rfl⟩
    exact hb hxL hv.1

/-- Negative/offense CF (1982 §7 / 1973 Thm 4). Palomar novel reconstruction. -/
theorem isContextFree [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) (hFin : A.FiniteOffenseHorizon U)
    (hL : Language.IsContextFree (A.L : Language A.D)) :
    Language.IsContextFree (U : Language A.D) := by
  have hCreg := offenseSuffixLang.isRegular A hFin
  have hEq : (U : Language A.D) =
      (A.L : Language A.D) ⊓ A.offenseSuffixLang U := by
    change (U : Set _) = (A.L ∩ A.offenseSuffixLang U : Set _)
    exact OffenseClosed.eq_L_inter_suffix A hSub hb
  rw [hEq]
  exact hL.inter_regular hCreg

end OffenseClosed

end ActionSystem
end Actions
