/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Mixed.LM
import Mathlib.Tactic

@[expose] public section

/-!
# Representation of the verbal part (§5.2.1)

Successive occurrences `x = pref ++ [inr α] ++ suff` for each sentence
in `x`, with utterance time read from the discrete time of `pref`.
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- One utterance occurrence (not yet tied to a concrete host string). -/
structure VerbalOcc where
  α : S.M
  pref : List S.Letter
  suff : List S.Letter

namespace VerbalOcc

/-- Rebuild the mixed string from a split. -/
def reconstruct (occ : VerbalOcc (S := S)) : List S.Letter :=
  occ.pref ++ Sum.inr occ.α :: occ.suff

/-- Behavioural prefix before this utterance. -/
def piPrefix (occ : VerbalOcc (S := S)) : List S.D := S.pi occ.pref

/-- Behavioural suffix after this utterance. -/
def piSuffix (occ : VerbalOcc (S := S)) : List S.D := S.pi occ.suff

/-- Discrete time contribution of one letter (pause-units). -/
noncomputable def letterTime : S.Letter → ℕ
  | Sum.inl d => Nat.floor (S.base.φ d)
  | Sum.inr α => S.φM α

/-- Utterance moment = total discrete time of the prefix. -/
noncomputable def time (occ : VerbalOcc (S := S)) : ℕ :=
  (occ.pref.map (letterTime S)).sum

/-- Wanted time-results at this occurrence. -/
noncomputable def W_at (occ : VerbalOcc (S := S)) := S.W occ.α (time S occ)

/-- Unwanted time-results at this occurrence. -/
noncomputable def W'_at (occ : VerbalOcc (S := S)) := S.W' occ.α (time S occ)

/-- Obligation set at this occurrence. -/
noncomputable def O_at (occ : VerbalOcc (S := S)) := S.O occ.α (time S occ)

/-- Prohibition set at this occurrence. -/
noncomputable def O'_at (occ : VerbalOcc (S := S)) := S.O' occ.α (time S occ)

end VerbalOcc

/-- Collect successive verbal occurrences (paper (4)(a)–(b)). -/
def verbalOccsAux : List S.Letter → List S.Letter → List (VerbalOcc (S := S))
  | _pref, [] => []
  | pref, Sum.inl d :: rs => verbalOccsAux (pref ++ [Sum.inl d]) rs
  | pref, Sum.inr α :: rs =>
      { α := α, pref := pref, suff := rs } ::
        verbalOccsAux (pref ++ [Sum.inr α]) rs

def verbalOccs (x : List S.Letter) : List (VerbalOcc (S := S)) :=
  verbalOccsAux S [] x

namespace verbalOccs

theorem reconstruct (x : List S.Letter) :
    ∀ occ ∈ S.verbalOccs x, VerbalOcc.reconstruct S occ = x := by
  suffices h : ∀ pref rest occ,
      occ ∈ verbalOccsAux S pref rest →
        VerbalOcc.reconstruct S occ = pref ++ rest by
    intro occ hx
    simpa [verbalOccs] using h [] x occ hx
  intro pref rest
  induction rest generalizing pref with
  | nil =>
      intro occ hx
      simp [verbalOccsAux] at hx
  | cons c rs ih =>
      intro occ hx
      cases c with
      | inl d =>
          simp [verbalOccsAux] at hx
          have := ih (pref ++ [Sum.inl d]) occ hx
          simpa [List.append_assoc] using this
      | inr α =>
          simp [verbalOccsAux] at hx
          cases hx with
          | inl h0 =>
              subst h0
              simp [VerbalOcc.reconstruct]
          | inr hrest =>
              have := ih (pref ++ [Sum.inr α]) occ hrest
              simpa [List.append_assoc] using this

end verbalOccs

end MixedSystem
end Actions
