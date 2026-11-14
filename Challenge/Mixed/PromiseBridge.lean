/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Mixed.MixedSystem
public import Challenge.Promise.PromiseClosed
public import Challenge.Promise.OffenseClosed
import Mathlib.Tactic

@[expose] public section

/-!
# Bridge from §5.1 assumptions (11)/(12) to abstract promise/offense closure
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)
-- compared Actions.MixedSystem.O_promiseClosed in Challenge.lean
-- compared Actions.MixedSystem.O'_offenseClosed in Challenge.lean
end MixedSystem
end Actions
