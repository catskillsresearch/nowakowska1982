/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Mixed.VerbalPart
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

/-- **Proposition 1 (§5.2.2):** consistency implies aggregate wants and
unwants are disjoint. -/
theorem wanted_unwanted_disjoint {x : List S.Letter}
    (h : S.MotivationalConsistency x) :
    wantedUnion S x ∩ unwantedUnion S x = ∅ := by
  ext st
  constructor
  · intro ⟨hw, hu⟩
    rcases hw with ⟨occ₁, hocc₁, hst₁⟩
    rcases hu with ⟨occ₂, hocc₂, hst₂⟩
    -- From consistency at occ₁: πx ∈ RinvWanted W₁ (if W₁ nonempty)
    have hcons := h.2.2
    have h1 := hcons occ₁ hocc₁
    have h2 := hcons occ₂ hocc₂
    have hW1ne : VerbalOcc.W_at S occ₁ ≠ ∅ :=
      fun hempty => by simp [hempty] at hst₁
    have hW2ne : VerbalOcc.W'_at S occ₂ ≠ ∅ :=
      fun hempty => by simp [hempty] at hst₂
    have hwant : S.pi x ∈ S.base.RinvWanted (VerbalOcc.W_at S occ₁) := by
      cases h1.1 with
      | inl hempty => exact (hW1ne hempty).elim
      | inr hmem => exact hmem
    have havoid : S.pi x ∉ S.base.RinvUnwanted (VerbalOcc.W'_at S occ₂) := by
      cases h2.2.1 with
      | inl hempty => exact (hW2ne hempty).elim
      | inr hnot => exact hnot
    have hin : S.pi x ∈ S.base.Rinv st.1 st.2 :=
      hwant st hst₁
    have : S.pi x ∈ S.base.RinvUnwanted (VerbalOcc.W'_at S occ₂) :=
      ⟨st, hst₂, hin⟩
    exact havoid this
  · intro hfalse
    exact hfalse.elim

end MotivationalConsistency

end MixedSystem
end Actions
