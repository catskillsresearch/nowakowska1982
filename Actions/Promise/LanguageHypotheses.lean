/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Promise.CFInterRegular

@[expose] public section

/-!
# Classical Ch. 3 language facts for promise/offense CF

These were formerly named hypotheses (`def … : Prop`) threaded through
`PromiseClosed.isContextFree` / `OffenseClosed.isContextFree`. They are now
theorems, proved in `Actions.Promise.CFInterRegular` by the Bar-Hillel
grammar × DFA product construction.
-/

namespace Actions
namespace ActionSystem

open scoped Computability

/-- Classical Ch. 3 fact: over a finite alphabet every regular language is
context-free. (The finiteness assumption is necessary: a context-free grammar
has finitely many rules, so it mentions only finitely many terminals.) -/
theorem RegularImpliesCF (α : Type*) [Finite α] (L : Language α)
    (hL : Language.IsRegular L) : Language.IsContextFree L :=
  hL.isContextFree

/-- Classical Ch. 3 fact (Bar-Hillel): CF languages are closed under
intersection with regular languages. -/
theorem CFInterRegular (α : Type*) (L R : Language α)
    (hL : Language.IsContextFree L) (hR : Language.IsRegular R) :
    Language.IsContextFree (L ⊓ R) :=
  hL.inter_regular hR

end ActionSystem
end Actions
