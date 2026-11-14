/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Mixed.MixedSystem
public import Actions.Promise.PromiseClosed
public import Actions.Promise.OffenseClosed
import Mathlib.Tactic

@[expose] public section

/-!
# Bridge from §5.1 assumptions (11)/(12) to abstract promise/offense closure
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- Assumption (11) implies condition (a) on each obligation set. -/
theorem O_promiseClosed (α : S.M) (k : ℕ) :
    S.base.PromiseClosed (S.O α k) := by
  intro x y hxy hx
  exact S.O_right_closed α k hx ⟨[], [], by simpa using hxy⟩

/-- Assumption (12) implies condition (b) on each prohibition set. -/
theorem O'_offenseClosed (α : S.M) (k : ℕ) :
    S.base.OffenseClosed (S.O' α k) := by
  intro x y z hxyz hy
  exact S.O'_embed_closed α k hy ⟨[], [], by simpa using hxyz⟩

end MixedSystem
end Actions
