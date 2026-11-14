/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Choice.prefer
import Mathlib.Tactic

@[expose] public section

/-!
# Pure scale-1 dictator SWF
-/

namespace Actions
namespace Arrow

def scale1Dictator : SWF2 := fun π => π.1

namespace scale1Dictator
theorem isDictator : IsDictator scale1Dictator 0 := fun _ _ _ h => h
theorem unanimity : Unanimity scale1Dictator := fun _ _ _ h₁ _ => h₁
theorem IIA : IIA scale1Dictator := by
  intro π π' a b h1 _ _ _
  simpa [scale1Dictator, rankingPreorder] using h1
theorem not_lack : ¬ LackOfDictator scale1Dictator := fun h =>
  h 0 isDictator
theorem sovereignty : Sovereignty scale1Dictator := by
  intro a b hne
  constructor
  · exact ⟨(prefer a b, prefer a b), by simpa [scale1Dictator] using prefer.lt hne⟩
  · exact ⟨(prefer b a, prefer b a), by simpa [scale1Dictator] using prefer.lt (Ne.symm hne)⟩
end scale1Dictator

end Arrow
end Actions
