/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Choice.prefer
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
-- compared Actions.Arrow.scale2Dictator.unanimity in Challenge.lean
-- compared Actions.Arrow.scale2Dictator.IIA in Challenge.lean
-- compared Actions.Arrow.scale2Dictator.not_lack in Challenge.lean
-- compared Actions.Arrow.scale2Dictator.sovereignty in Challenge.lean
end scale2Dictator

end Arrow
end Actions
