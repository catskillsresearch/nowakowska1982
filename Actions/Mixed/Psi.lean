/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Mixed.ConsistentWith
public import Actions.Mixed.MotivationalConsistency
import Mathlib.Tactic

@[expose] public section

/-!
# The set `ψ(A)` of action strings consistent with utterances `A` (§5.3.5)
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- `ψ(A) = { u ∈ L | u is consistent with respect to A }`. -/
def Psi (A : Set S.Lambda) : Set (List S.D) :=
  { u | u ∈ S.base.L ∧ S.ConsistentWithSet u A }

namespace Psi

theorem mem_iff {A : Set S.Lambda} {u : List S.D} :
    u ∈ S.Psi A ↔ u ∈ S.base.L ∧ S.ConsistentWithSet u A :=
  Iff.rfl

/-- **Proposition 5 (§5.3.5):** `ψ` is antitone in the utterance set. -/
theorem antitone {A B : Set S.Lambda} (h : A ⊆ B) : S.Psi B ⊆ S.Psi A := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  intro αk hαk
  exact hu.2 αk (h hαk)

/-- Utterance set of a mixed string. -/
noncomputable def utterancesOf (x : List S.Letter) : Set S.Lambda :=
  { αk | ∃ occ ∈ S.verbalOccs x, αk = (occ.α, VerbalOcc.time S occ) }

/-- Motivational consistency implies `π(x) ∈ ψ(A(x))` (§5.3.5). -/
theorem pi_mem_of_motivationalConsistency {x : List S.Letter}
    (h : S.MotivationalConsistency x) :
    S.pi x ∈ S.Psi (utterancesOf S x) := by
  refine ⟨h.1, ?_⟩
  intro αk hαk
  rcases hαk with ⟨occ, hocc, rfl⟩
  have hxrec := verbalOccs.reconstruct S x occ hocc
  have hpi : S.pi x =
      S.pi occ.pref ++ S.pi (Sum.inr occ.α :: occ.suff) := by
    rw [← hxrec]
    simpa [VerbalOcc.reconstruct] using
      (pi.map_append S occ.pref (Sum.inr occ.α :: occ.suff))
  have hα : S.pi (Sum.inr occ.α :: occ.suff) =
      S.base.pauseString (S.φM occ.α) ++ S.pi occ.suff := by
    simp only [pi, piGo]
    simpa using (pi.go_add_pending S (S.φM occ.α) 0 occ.suff)
  have hsplit : S.pi x =
      (S.pi occ.pref ++ S.base.pauseString (S.φM occ.α)) ++ S.pi occ.suff := by
    rw [hpi, hα, List.append_assoc]
  have hocc' := h.2.2 occ hocc
  refine ⟨h.1, hocc'.1, hocc'.2.1, ?_⟩
  refine ⟨S.pi occ.pref ++ S.base.pauseString (S.φM occ.α),
    S.pi occ.suff, hsplit, hocc'.2.2.1, hocc'.2.2.2⟩

end Psi

end MixedSystem
end Actions
