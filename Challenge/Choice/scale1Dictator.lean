/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Choice.prefer
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
-- compared Actions.Arrow.scale1Dictator.unanimity in Challenge.lean
-- compared Actions.Arrow.scale1Dictator.IIA in Challenge.lean
-- compared Actions.Arrow.scale1Dictator.not_lack in Challenge.lean
-- compared Actions.Arrow.scale1Dictator.sovereignty in Challenge.lean
end scale1Dictator

end Arrow
end Actions
