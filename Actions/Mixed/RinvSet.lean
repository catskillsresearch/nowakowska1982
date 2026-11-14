/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Attainability.Goals
import Mathlib.Tactic

@[expose] public section

/-!
# Inverse images for arbitrary sets of time-results

\(\hat R^{-1}(W)\) and \(R^{-1}(W')\) for sets of time-results used by
motivational consistency (1973 §5.2).
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- \(\hat R^{-1}(W) = \bigcap_{(s,n)\in W} R^{-1}(s,n)\). -/
def RinvWanted (W : Set A.TimeResult) : Set (List A.D) :=
  { u | ∀ st ∈ W, u ∈ A.Rinv st.1 st.2 }

/-- \(R^{-1}(W')\) for a set of time-results (union of singletons). -/
def RinvUnwanted (W' : Set A.TimeResult) : Set (List A.D) :=
  { u | ∃ st ∈ W', u ∈ A.Rinv st.1 st.2 }

namespace RinvWanted

theorem mem_iff {W : Set A.TimeResult} {u : List A.D} :
    u ∈ A.RinvWanted W ↔ ∀ st ∈ W, u ∈ A.Rinv st.1 st.2 :=
  Iff.rfl

theorem empty : A.RinvWanted (∅ : Set A.TimeResult) = Set.univ := by
  ext u
  simp [RinvWanted]

end RinvWanted

namespace RinvUnwanted

theorem mem_iff {W' : Set A.TimeResult} {u : List A.D} :
    u ∈ A.RinvUnwanted W' ↔ ∃ st ∈ W', u ∈ A.Rinv st.1 st.2 :=
  Iff.rfl

theorem empty : A.RinvUnwanted (∅ : Set A.TimeResult) = ∅ := by
  ext u
  simp [RinvUnwanted]

end RinvUnwanted

end ActionSystem
end Actions
