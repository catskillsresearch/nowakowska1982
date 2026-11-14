/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Mixed.ConsistentWith
public import Challenge.Mixed.MotivationalConsistency
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
-- compared Actions.MixedSystem.Psi.mem_iff in Challenge.lean
theorem antitone {A B : Set S.Lambda} (h : A ⊆ B) : S.Psi B ⊆ S.Psi A := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  intro αk hαk
  exact hu.2 αk (h hαk)

/-- Utterance set of a mixed string. -/
noncomputable def utterancesOf (x : List S.Letter) : Set S.Lambda :=
  { αk | ∃ occ ∈ S.verbalOccs x, αk = (occ.α, VerbalOcc.time S occ) }
-- compared Actions.MixedSystem.Psi.pi_mem_of_motivationalConsistency in Challenge.lean
end Psi

end MixedSystem
end Actions
