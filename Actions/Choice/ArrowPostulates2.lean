/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Choice.scale1Dictator
public import Actions.Choice.scale2Dictator
import Mathlib.Tactic

@[expose] public section

/-!
# Packaged Arrow postulates and their inconsistency

`ArrowPostulates2 F` packages the four §5 postulates (Nowakowska 1982,
pp. 152–156) for an SWF on 2 motivational scales / 3 options.

* `arrow_impossibility`: no SWF satisfies `ArrowPostulates2`. This is the
  standard impossibility in this finite 2×3 encoding, not a new theorem:
  `arrow_dictator_of_unanimity_IIA` (in `Arrow`) yields a dictating scale from
  `Unanimity` and `IIA`, contradicting `LackOfDictator`. `Sovereignty` is not
  used (it already follows from `Unanimity`).
* `ArrowPostulates2.impossibility_dictatorial_core`: the two pure scale
  dictators — the compared claim — as the special case.
-/

namespace Actions
namespace Arrow

def ArrowPostulates2 (F : SWF2) : Prop :=
  LackOfDictator F ∧ Unanimity F ∧ IIA F ∧ Sovereignty F

/-- **Arrow impossibility, 2 scales × 3 options.** Standard impossibility in
this finite encoding: `Unanimity` and `IIA` force a dictating scale, which
`LackOfDictator` forbids. `Sovereignty` is not needed. -/
theorem arrow_impossibility (F : SWF2) : ¬ ArrowPostulates2 F := by
  rintro ⟨hLack, hU, hI, _⟩
  obtain ⟨i, hi⟩ := arrow_dictator_of_unanimity_IIA F hU hI
  exact hLack i hi

namespace ArrowPostulates2
theorem not_of_dictator {F : SWF2} {i : Fin 2}
    (h : IsDictator F i) : ¬ ArrowPostulates2 F := by
  rintro ⟨hLack, _, _, _⟩
  exact hLack i h

/-- **Compared claim (dictatorial core):** the pure scale dictators — the
§5 compulsive/hedonistic solutions — do not satisfy `ArrowPostulates2`.
Corollary of `arrow_impossibility`. -/
theorem impossibility_dictatorial_core :
    ¬ ArrowPostulates2 scale1Dictator ∧ ¬ ArrowPostulates2 scale2Dictator :=
  ⟨arrow_impossibility _, arrow_impossibility _⟩
end ArrowPostulates2

end Arrow
end Actions
