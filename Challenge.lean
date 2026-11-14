/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions
public import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

open scoped Computability

/-!
# Palomar Challenge (statement of record)

Compared family for Palomar Comparator (see `comparator.json`,
`formalization.yaml`, `PROVENANCE.md`).

Includes every theorem that is a sink in the theorems-only dependency graph
(no successor), plus the automaton realization `toActionSystem.L`.
Clinical abbrevs remain packaging of Arrow postulate failure.
-/

namespace Challenge

abbrev CompulsiveOrHedonistic := Actions.Arrow.CompulsiveOrHedonistic
abbrev BlindObedience := Actions.Arrow.BlindObedience
abbrev NeuroticAllOrNothing := Actions.Arrow.NeuroticAllOrNothing


export Actions.Conflicts (conflictPattern_card)

namespace ActionAutomaton
export Actions.ActionAutomaton (admissible_cons_nextState mem_language_iff nextState_eq nil_mem_language singleton_admissible)
end ActionAutomaton

namespace ActionAutomaton.toActionSystem
export Actions.ActionAutomaton.toActionSystem (mem_L_iff)
end toActionSystem
end ActionAutomaton

namespace ActionSystem
export Actions.ActionSystem (Rinv_subset_L stringDuration_pauseString strongly_implies_weakly weakly_iff_strongly_singleton)
end ActionSystem

namespace ActionSystem.EffortDominated
export Actions.ActionSystem.EffortDominated (refl)
end EffortDominated
end ActionSystem

namespace ActionSystem.HatT
export Actions.ActionSystem.HatT (subset)
end HatT
end ActionSystem

namespace ActionSystem.NonParasitic
export Actions.ActionSystem.NonParasitic (append_left_right of_mem_L)
end NonParasitic
end ActionSystem

namespace ActionSystem.Prax
export Actions.ActionSystem.Prax (Min_subset subset)
end Prax
end ActionSystem

namespace ActionSystem.PromiseClosed
export Actions.ActionSystem.PromiseClosed (mono)
end PromiseClosed
end ActionSystem

namespace ActionSystem.RinvUnwanted
export Actions.ActionSystem.RinvUnwanted (mem_iff)
end RinvUnwanted
end ActionSystem

namespace ActionSystem.RinvWanted
export Actions.ActionSystem.RinvWanted (empty mem_iff)
end RinvWanted
end ActionSystem

namespace ActionSystem.stringDuration
export Actions.ActionSystem.stringDuration (nil_not_pos)
end stringDuration
end ActionSystem

namespace Arrow.BlindObedience
export Actions.Arrow.BlindObedience (of_not_sovereignty)
end BlindObedience
end Arrow

namespace Arrow.CompulsiveOrHedonistic
export Actions.Arrow.CompulsiveOrHedonistic (of_dictator of_not_lack)
end CompulsiveOrHedonistic
end Arrow

namespace Arrow.NeuroticAllOrNothing
export Actions.Arrow.NeuroticAllOrNothing (of_not_IIA)
end NeuroticAllOrNothing
end Arrow

namespace Arrow.scale1Dictator
export Actions.Arrow.scale1Dictator (IIA compulsive not_lack sovereignty unanimity)
end scale1Dictator
end Arrow

namespace Arrow.scale2Dictator
export Actions.Arrow.scale2Dictator (IIA not_lack sovereignty unanimity)
end scale2Dictator
end Arrow

namespace ArrowPostulates2
export Actions.Arrow.ArrowPostulates2 (impossibility_dictatorial_core)
end ArrowPostulates2

namespace Conflicts
export Actions.Conflicts (isConflictPattern_decide patternsFor_allDoubletons patternsFor_zero)
end Conflicts

namespace MixedSystem
export Actions.MixedSystem (O'_offenseClosed O_promiseClosed W_disjoint)
end MixedSystem

namespace MixedSystem.LM
export Actions.MixedSystem.LM (mem_iff of_pure_actions)
end LM
end MixedSystem

namespace MixedSystem.MotivationalConsistency
export Actions.MixedSystem.MotivationalConsistency (wanted_unwanted_disjoint)
end MotivationalConsistency
end MixedSystem

namespace MixedSystem.Psi
export Actions.MixedSystem.Psi (mem_iff pi_mem_of_motivationalConsistency)
end Psi
end MixedSystem

namespace MixedSystem.Satisfiable
export Actions.MixedSystem.Satisfiable (of_motivationalConsistency)
end Satisfiable
end MixedSystem

namespace OffenseClosed
export Actions.ActionSystem.OffenseClosed (isContextFree)
end OffenseClosed

namespace PromiseClosed
export Actions.ActionSystem.PromiseClosed (isContextFree)
end PromiseClosed

namespace SampledSemImp
export Actions.MotCalc.SampledSemImp (epistemicModel)
end SampledSemImp

namespace Toy
export Actions.Toy (Prax_empty_example nil_not_mem_promiseT promiseT_closed toy_pause_duration toy_work_duration twoGoals_conflict work_attains work_mem_promiseT work_string_duration)
end Toy

namespace toActionSystem
export Actions.ActionAutomaton.toActionSystem (L)
end toActionSystem

end Challenge
