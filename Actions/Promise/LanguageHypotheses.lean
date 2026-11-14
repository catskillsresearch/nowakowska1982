/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA

@[expose] public section

/-!
# Classical Ch. 3 language hypotheses for promise/offense CF
-/

namespace Actions
namespace ActionSystem

open scoped Computability

/-- Classical Ch. 3 hypothesis: every regular language is context-free. -/
def RegularImpliesCF (α : Type*) : Prop :=
  ∀ L : Language α, Language.IsRegular L → Language.IsContextFree L

/-- Classical Ch. 3 hypothesis: CF languages are closed under intersection with
regular languages. -/
def CFInterRegular (α : Type*) : Prop :=
  ∀ L R : Language α,
    Language.IsContextFree L → Language.IsRegular R →
      Language.IsContextFree (L ⊓ R)

end ActionSystem
end Actions
