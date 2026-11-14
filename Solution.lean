/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Attainability.Conflicts
public import Actions.Automata.Automaton
public import Actions.Choice.Arrow

@[expose] public section

/-!
# Palomar Solution (Batch A)
-/

namespace Solution

theorem conflictPattern_card :
    Actions.Conflicts.conflictPatternCount = 113 :=
  Actions.Conflicts.conflictPattern_card

theorem toActionSystem_L (M : Actions.ActionAutomaton) (u₀ : M.U) (b₀ : M.B) :
    (M.toActionSystem u₀ b₀).L = M.language u₀ b₀ :=
  Actions.ActionAutomaton.toActionSystem_L M u₀ b₀

theorem arrow_impossibility_dictatorial_core :
    ¬ Actions.Arrow.ArrowPostulates2 Actions.Arrow.scale1Dictator ∧
      ¬ Actions.Arrow.ArrowPostulates2 Actions.Arrow.scale2Dictator :=
  Actions.Arrow.arrow_impossibility_dictatorial_core

abbrev CompulsiveOrHedonistic := Actions.Arrow.CompulsiveOrHedonistic
abbrev BlindObedience := Actions.Arrow.BlindObedience
abbrev NeuroticAllOrNothing := Actions.Arrow.NeuroticAllOrNothing

end Solution
