/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Choice.Arrow

@[expose] public section

/-!
# Neurotic all-or-nothing packaging of IIA failure

Interpretive library packaging for postulate (4) failure (Nowakowska 1982
§5). Not a new psychology theorem.
-/

namespace Actions
namespace Arrow

/-- Clinical packaging: IIA fails. -/
def NeuroticAllOrNothing (F : SWF2) : Prop := ¬ IIA F

namespace NeuroticAllOrNothing

theorem of_not_IIA {F : SWF2} (h : ¬ IIA F) :
    NeuroticAllOrNothing F := h

end NeuroticAllOrNothing

end Arrow
end Actions
