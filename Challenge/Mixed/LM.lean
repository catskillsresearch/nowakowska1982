/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Mixed.pi
import Mathlib.Tactic

@[expose] public section

/-!
# Mixed language \(L_M = \pi^{-1}(L)\) (§5.2.1)
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- Physically admissible mixed strings: behavioural part in `L`. -/
def LM : Set (List S.Letter) :=
  { x | S.pi x ∈ S.base.L }

namespace LM
-- compared Actions.MixedSystem.LM.mem_iff in Challenge.lean
-- compared Actions.MixedSystem.LM.of_pure_actions in Challenge.lean
end LM

/-- Mixed strings that contain at least one sentence. -/
def hasUtterance (x : List S.Letter) : Prop :=
  ∃ α : S.M, Sum.inr α ∈ x

/-- Domain of motivational consistency: `L_M \ L` (strings with utterances). -/
def LM_minus_L : Set (List S.Letter) :=
  { x | x ∈ S.LM ∧ S.hasUtterance x }

end MixedSystem
end Actions
