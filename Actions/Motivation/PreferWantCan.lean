/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Motivation.EpistemicModel

@[expose] public section

/-!
# Prefer / want / can sample (thin cross-functor packaging)
-/

namespace Actions
namespace MotCalc

/-- Prefer / want / can sample (thin; cross-functor packaging). -/
structure PreferWantCan (X : Type*) where
  Prefer : PropSet X → PropSet X → Prop
  Want : PropSet X → Prop
  DontWant : PropSet X → Prop
  Can : PropSet X → Prop
  Cannot : PropSet X → Prop
  Ought : PropSet X → Prop
  Must : PropSet X → Prop
  prefer_asymm : ∀ p q, Prefer p q → ¬ Prefer q p
  want_not_dont : ∀ p, Want p → ¬ DontWant p
  can_not_cannot : ∀ p, Can p → ¬ Cannot p
  must_imp_ought : ∀ p, Must p → Ought p
  /-- Sampled cross-functor: prefer forces want of the preferred side. -/
  prefer_imp_want : ∀ p q, Prefer p q → Want p

end MotCalc
end Actions
