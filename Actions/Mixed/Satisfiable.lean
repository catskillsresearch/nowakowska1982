/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Mixed.MotivationalConsistency
public import Actions.Mixed.Realizes
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

/-- **Proposition 1 (§5.3.1):** every motivationally consistent mixed string
supplies a satisfiable utterance system (itself as witness). -/
theorem of_motivationalConsistency {x : List S.Letter}
    (h : S.MotivationalConsistency x) :
    S.Satisfiable ((S.verbalOccs x).map (·.α))
      ((S.verbalOccs x).map (VerbalOcc.time S)) :=
  ⟨x, h, Realizes.of_refl S x⟩

end Satisfiable

end MixedSystem
end Actions
