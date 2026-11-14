/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Motivation.SemImp
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
-- compared Actions.MotCalc.SampledSemImp.epistemicModel in Challenge.lean
end SampledSemImp

end MotCalc
end Actions
