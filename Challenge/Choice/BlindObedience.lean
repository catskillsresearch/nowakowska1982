/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Choice.Arrow

@[expose] public section

/-!
# Blind obedience packaging of sovereignty failure

Interpretive library packaging for postulate (2) failure (Nowakowska 1982
§5). Not a new psychology theorem.
-/

namespace Actions
namespace Arrow

/-- Clinical packaging: sovereignty fails. -/
def BlindObedience (F : SWF2) : Prop := ¬ Sovereignty F

namespace BlindObedience
-- compared Actions.Arrow.BlindObedience.of_not_sovereignty in Challenge.lean
end BlindObedience

end Arrow
end Actions
