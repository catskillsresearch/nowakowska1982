/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Mixed.MotivationalConsistency
public import Challenge.Mixed.Realizes
import Mathlib.Tactic

@[expose] public section

/-!
# Satisfiable utterance systems (§5.3.1)

A timed sequence of sentences is satisfiable when some mixed string is
motivationally consistent and realizes those sentences at those times.
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- Satisfiability of a timed sentence list (§5.3.1): some motivationally
consistent mixed string realizes it. -/
def Satisfiable (alphas : List S.M) (times : List ℕ) : Prop :=
  ∃ x : List S.Letter,
    S.MotivationalConsistency x ∧ S.Realizes x alphas times

namespace Satisfiable
-- compared Actions.MixedSystem.Satisfiable.of_motivationalConsistency in Challenge.lean
end Satisfiable

end MixedSystem
end Actions
