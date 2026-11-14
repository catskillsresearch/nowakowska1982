/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Motivation.EpistemicModel

@[expose] public section

/-!
# Gladness extension of the epistemic model (§2.2.4 c)
-/

namespace Actions
namespace MotCalc

/-- Extended model with gladness set \(v_G\) disjoint from \(v_T\). -/
structure GladModel (X : Type*) extends EpistemicModel X where
  vG : PropSet X
  vG_disjoint_vT : vG ∩ vT = ∅

namespace GladModel

/-- Reading of \(G\alpha\) used for rule (48): gladness forces think-containment
or (when the gladness seed sits in \(\alpha\)) knowledge. -/
def Glad {X} (M : GladModel X) (α : PropSet X) : Prop :=
  M.vT ⊆ α ∨ (M.vG ⊆ α ∧ M.P α = 1)

end GladModel

end MotCalc
end Actions
