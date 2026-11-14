/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Choice.prefer
import Mathlib.Tactic

@[expose] public section

/-!
# Pure scale-2 dictator SWF
-/

namespace Actions
namespace Arrow

def scale2Dictator : SWF2 := fun π => π.2

namespace scale2Dictator
theorem isDictator : IsDictator scale2Dictator 1 := fun _ _ _ h => h
theorem unanimity : Unanimity scale2Dictator := fun _ _ _ _ h₂ => h₂
theorem IIA : IIA scale2Dictator := by
  intro π π' a b _ _ h2 _
  simpa [scale2Dictator, rankingPreorder] using h2
theorem not_lack : ¬ LackOfDictator scale2Dictator := fun h =>
  h 1 isDictator
theorem sovereignty : Sovereignty scale2Dictator := by
  intro a b hne
  constructor
  · exact ⟨(prefer a b, prefer a b), by simpa [scale2Dictator] using prefer.lt hne⟩
  · exact ⟨(prefer b a, prefer b a), by simpa [scale2Dictator] using prefer.lt (Ne.symm hne)⟩
end scale2Dictator

end Arrow
end Actions
