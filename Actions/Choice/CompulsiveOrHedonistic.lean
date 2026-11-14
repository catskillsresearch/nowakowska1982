/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Choice.scale1Dictator
public import Actions.Choice.scale2Dictator
import Mathlib.Tactic

@[expose] public section

/-!
# Compulsive / hedonistic packaging of dictator failure

Interpretive library packaging for postulate (1) failure (Nowakowska 1982
§5): a dominating Superego or Id continuum. Not a new psychology theorem.
-/

namespace Actions
namespace Arrow

/-- Clinical packaging: some scale is a dictator. -/
def CompulsiveOrHedonistic (F : SWF2) : Prop := ∃ i, IsDictator F i

namespace CompulsiveOrHedonistic

theorem of_not_lack {F : SWF2} (h : ¬ LackOfDictator F) :
    CompulsiveOrHedonistic F := by
  unfold LackOfDictator at h
  push Not at h
  exact h

theorem of_dictator {F : SWF2} {i : Fin 2} (h : IsDictator F i) :
    CompulsiveOrHedonistic F := ⟨i, h⟩

end CompulsiveOrHedonistic

namespace scale1Dictator
theorem compulsive : CompulsiveOrHedonistic scale1Dictator :=
  ⟨0, isDictator⟩
end scale1Dictator

namespace scale2Dictator
theorem compulsive : CompulsiveOrHedonistic scale2Dictator :=
  ⟨1, isDictator⟩
end scale2Dictator

end Arrow
end Actions
