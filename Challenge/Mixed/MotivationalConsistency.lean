/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Mixed.VerbalPart
import Mathlib.Tactic

@[expose] public section

/-!
# Motivational consistency (§5.2.2)

Definition 1 and Proposition 1: consistent mixed strings have disjoint
aggregate wanted / unwanted time-result sets.
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- Motivational consistency of a mixed string with at least one utterance
(1973 §5.2.2 Def. 1). Empty obligation/want sets vacate their conditions. -/
def MotivationalConsistency (x : List S.Letter) : Prop :=
  x ∈ S.LM ∧
    S.hasUtterance x ∧
      ∀ occ ∈ S.verbalOccs x,
        (VerbalOcc.W_at S occ = ∅ ∨
          S.pi x ∈ S.base.RinvWanted (VerbalOcc.W_at S occ)) ∧
        (VerbalOcc.W'_at S occ = ∅ ∨
          S.pi x ∉ S.base.RinvUnwanted (VerbalOcc.W'_at S occ)) ∧
        (VerbalOcc.O_at S occ = ∅ ∨
          VerbalOcc.piSuffix S occ ∈ VerbalOcc.O_at S occ) ∧
        (VerbalOcc.O'_at S occ = ∅ ∨
          VerbalOcc.piSuffix S occ ∉ VerbalOcc.O'_at S occ)

namespace MotivationalConsistency

/-- Aggregate wanted time-results across occurrences. -/
noncomputable def wantedUnion (x : List S.Letter) : Set S.TimeResult :=
  { st | ∃ occ ∈ S.verbalOccs x, st ∈ VerbalOcc.W_at S occ }

/-- Aggregate unwanted time-results across occurrences. -/
noncomputable def unwantedUnion (x : List S.Letter) : Set S.TimeResult :=
  { st | ∃ occ ∈ S.verbalOccs x, st ∈ VerbalOcc.W'_at S occ }
-- compared Actions.MixedSystem.MotivationalConsistency.wanted_unwanted_disjoint in Challenge.lean
end MotivationalConsistency

end MixedSystem
end Actions
