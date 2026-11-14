/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Attainability.Goals
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
-- compared Actions.ActionSystem.RinvWanted.mem_iff in Challenge.lean
-- compared Actions.ActionSystem.RinvWanted.empty in Challenge.lean
end RinvWanted

namespace RinvUnwanted
-- compared Actions.ActionSystem.RinvUnwanted.mem_iff in Challenge.lean
theorem empty : A.RinvUnwanted (∅ : Set A.TimeResult) = ∅ := by
  ext u
  simp [RinvUnwanted]

end RinvUnwanted

end ActionSystem
end Actions
