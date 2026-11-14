/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.ActionSystem
import Mathlib.Tactic

@[expose] public section

/-!
# Non-L-parasitic strings \(D^*_+\)

A string is not \(L\)-parasitic when it appears as a substring of some
admissible string (Nowakowska 1973, §5.1 n.3).
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- `u` is not \(L\)-parasitic: some extension places it inside `L`. -/
def NonParasitic (u : List A.D) : Prop :=
  ∃ w₁ w₂ : List A.D, w₁ ++ u ++ w₂ ∈ A.L

namespace NonParasitic
-- compared Actions.ActionSystem.NonParasitic.of_mem_L in Challenge.lean
-- compared Actions.ActionSystem.NonParasitic.append_left_right in Challenge.lean
end NonParasitic

end ActionSystem
end Actions
