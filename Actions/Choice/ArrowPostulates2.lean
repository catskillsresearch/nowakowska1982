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
# Packaged Arrow postulates and dictatorial-core inconsistency
-/

namespace Actions
namespace Arrow

def ArrowPostulates2 (F : SWF2) : Prop :=
  LackOfDictator F ∧ Unanimity F ∧ IIA F ∧ Sovereignty F

namespace ArrowPostulates2
theorem not_of_dictator {F : SWF2} {i : Fin 2}
    (h : IsDictator F i) : ¬ ArrowPostulates2 F := by
  rintro ⟨hLack, _, _, _⟩
  exact hLack i h

/-- **Compared claim (dictatorial core):** the pure scale dictators — the
§5 compulsive/hedonistic solutions — do not satisfy `ArrowPostulates2`. -/
theorem impossibility_dictatorial_core :
    ¬ ArrowPostulates2 scale1Dictator ∧ ¬ ArrowPostulates2 scale2Dictator :=
  ⟨not_of_dictator scale1Dictator.isDictator,
    not_of_dictator scale2Dictator.isDictator⟩
end ArrowPostulates2

end Arrow
end Actions
