/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Motivation.SemImp
import Mathlib.Tactic

@[expose] public section

/-!
# Sampled SemImp bundle
-/

namespace Actions
namespace MotCalc

variable {X : Type*}

/-- Bundle of sampled §2.1.4 rules validated by the epistemic model. -/
structure SampledSemImp (X : Type*) (M : EpistemicModel X) : Prop where
  K_and : ∀ p q, SemImp (M.Know (p ∩ q)) (M.Know p ∧ M.Know q)
  Cr_and : ∀ p q, SemImp (M.Certain (p ∩ q)) (M.Certain p ∧ M.Certain q)
  T_and : ∀ p q, SemImp (M.Think (p ∩ q)) (M.Think p ∧ M.Think q)
  T_Tprime_not : ∀ p, SemImp (M.Think p) (M.DontThink (pᶜ))
  D_Tprime : ∀ p, SemImp (M.Doubt p) (M.DontThink p)
  Tprime_or : ∀ p q, SemImp (M.DontThink p ∧ M.DontThink q) (M.DontThink (p ∪ q))
  Kprime_not_K : ∀ p q, SemImp (M.DontKnowWhether p q) (¬ M.Know p)
  Bprime_T_not : ∀ p, SemImp (M.DontBelieve p) (M.Think (pᶜ))
  Cr_not_T_not : M.vT.Nonempty → ∀ p, SemImp (M.Certain p) (¬ M.Think (pᶜ))
  Tprime_not_T : M.vT.Nonempty → ∀ p, SemImp (M.DontThink p) (¬ M.Think p)

namespace SampledSemImp

theorem epistemicModel (M : EpistemicModel X) : SampledSemImp X M where
  K_and p q := (SemImp.K_and M p q).1
  Cr_and p q := (SemImp.Cr_and M p q).1
  T_and p q := (SemImp.T_and M p q).1
  T_Tprime_not p := SemImp.T_Tprime_not M p
  D_Tprime p := SemImp.D_Tprime M p
  Tprime_or p q := fun ⟨hp, hq⟩ => SemImp.Tprime_or M p q hp hq
  Kprime_not_K p q := SemImp.Kprime_not_K M p q
  Bprime_T_not p := SemImp.Bprime_T_not M p
  Cr_not_T_not hv p := SemImp.Cr_not_T_not M p hv
  Tprime_not_T hv p := SemImp.Tprime_not_T M p hv

end SampledSemImp

end MotCalc
end Actions
