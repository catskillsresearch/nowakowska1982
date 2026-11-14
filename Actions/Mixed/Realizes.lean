/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Mixed.VerbalPart
import Mathlib.Tactic

@[expose] public section

/-!
# Realization of timed sentence lists (§5.3.1)
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- `x` realizes the utterance skeleton `(alphas, times)`. -/
def Realizes (x : List S.Letter) (alphas : List S.M) (times : List ℕ) : Prop :=
  (S.verbalOccs x).map (·.α) = alphas ∧
    (S.verbalOccs x).map (VerbalOcc.time S) = times

namespace Realizes

theorem of_refl (x : List S.Letter) :
    S.Realizes x ((S.verbalOccs x).map (·.α))
      ((S.verbalOccs x).map (VerbalOcc.time S)) :=
  ⟨rfl, rfl⟩

end Realizes

end MixedSystem
end Actions
