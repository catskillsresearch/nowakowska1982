/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Choice.scale1Dictator
public import Challenge.Choice.scale2Dictator
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
-- compared Actions.Arrow.CompulsiveOrHedonistic.of_not_lack in Challenge.lean
-- compared Actions.Arrow.CompulsiveOrHedonistic.of_dictator in Challenge.lean
end CompulsiveOrHedonistic

namespace scale1Dictator
-- compared Actions.Arrow.scale1Dictator.compulsive in Challenge.lean
end scale1Dictator

namespace scale2Dictator
theorem compulsive : CompulsiveOrHedonistic scale2Dictator :=
  ⟨1, isDictator⟩
end scale2Dictator

end Arrow
end Actions
