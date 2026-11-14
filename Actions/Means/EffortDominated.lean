/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.ActionSystem
import Mathlib.Tactic

@[expose] public section

/-!
# Effort domination
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Pointwise “effort domination”: same length, and at every index the right
string is either equal or a pause replacing a non-pause. -/
def EffortDominated (u u' : List A.D) : Prop :=
  ∃ hlen : u.length = u'.length,
    ∀ i (hi : i < u.length),
      u[i] = u'[i]'(hlen ▸ hi) ∨
        (u'[i]'(hlen ▸ hi) = A.pause ∧ u[i] ≠ A.pause)

namespace EffortDominated

/-- Reflexivity of effort domination (equal strings). -/
theorem refl (u : List A.D) : A.EffortDominated u u := by
  refine ⟨rfl, ?_⟩
  intro i hi
  left
  rfl

end EffortDominated

end ActionSystem
end Actions
