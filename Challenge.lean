/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Attainability.Conflicts
public import Actions.Automata.toActionSystem
public import Actions.Choice.ArrowPostulates2
public import Actions.Choice.CompulsiveOrHedonistic
public import Actions.Choice.BlindObedience
public import Actions.Choice.NeuroticAllOrNothing
public import Actions.Motivation.SampledSemImp
public import Actions.Promise.PromiseClosed
public import Actions.Promise.OffenseClosed
public import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

open scoped Computability

/-!
# Palomar Challenge (statement of record)

Compared family for Palomar Comparator (see `comparator.json`,
`formalization.yaml`, `PROVENANCE.md`):

* `conflictPattern_card` — novel 113 labeled four-motive conflict count;
* `toActionSystem.L` — novel automaton / sixtuplet language equality;
* `ArrowPostulates2.impossibility_dictatorial_core` — dictatorial-core
  inconsistency, with clinical abbrevs `CompulsiveOrHedonistic`,
  `BlindObedience`, `NeuroticAllOrNothing`;
* `SampledSemImp.epistemicModel` — MotCalc sample on the §2.2.4 model;
* `PromiseClosed.isContextFree` / `OffenseClosed.isContextFree` — novel
  reconstructions of 1973 Thm 1 / Thm 4 (1982 §7), with Ch. 3 closures as
  named hypotheses.

Wrappers re-export the sorry-free `Actions/` proofs. `Solution.lean` matches
these declarations for Comparator. Palomar registration ID is pending.
-/

namespace Challenge

theorem conflictPattern_card :
    Actions.Conflicts.conflictPatternCount = 113 :=
  Actions.Conflicts.conflictPattern_card

theorem toActionSystem.L (M : Actions.ActionAutomaton) (u₀ : M.U) (b₀ : M.B) :
    (M.toActionSystem u₀ b₀).L = M.language u₀ b₀ :=
  Actions.ActionAutomaton.toActionSystem.L M u₀ b₀

theorem ArrowPostulates2.impossibility_dictatorial_core :
    ¬ Actions.Arrow.ArrowPostulates2 Actions.Arrow.scale1Dictator ∧
      ¬ Actions.Arrow.ArrowPostulates2 Actions.Arrow.scale2Dictator :=
  Actions.Arrow.ArrowPostulates2.impossibility_dictatorial_core

abbrev CompulsiveOrHedonistic := Actions.Arrow.CompulsiveOrHedonistic
abbrev BlindObedience := Actions.Arrow.BlindObedience
abbrev NeuroticAllOrNothing := Actions.Arrow.NeuroticAllOrNothing

/-- MotCalc sample: every epistemic model validates the sampled SemImp bundle. -/
theorem SampledSemImp.epistemicModel {X : Type*} (M : Actions.MotCalc.EpistemicModel X) :
    Actions.MotCalc.SampledSemImp X M :=
  Actions.MotCalc.SampledSemImp.epistemicModel M

/-- Positive promise CF (hypotheses: Ch. 3 closures). -/
theorem PromiseClosed.isContextFree
    (A : Actions.ActionSystem) [Fintype A.D] [Nonempty A.D]
    {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) (hFin : A.FiniteHorizon T)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (hRegCF : Actions.ActionSystem.RegularImpliesCF A.D)
    (hInter : Actions.ActionSystem.CFInterRegular A.D) :
    Language.IsContextFree (T : Language A.D) :=
  Actions.ActionSystem.PromiseClosed.isContextFree A hSub ha hFin hL hRegCF hInter

/-- Negative / offense CF (hypotheses: Ch. 3 closures). -/
theorem OffenseClosed.isContextFree
    (A : Actions.ActionSystem) [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) (hFin : A.FiniteOffenseHorizon U)
    (hPrime : A.OffensePrime U)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (hRegCF : Actions.ActionSystem.RegularImpliesCF A.D)
    (hInter : Actions.ActionSystem.CFInterRegular A.D) :
    Language.IsContextFree (U : Language A.D) :=
  Actions.ActionSystem.OffenseClosed.isContextFree A hSub hb hFin hPrime hL hRegCF hInter

end Challenge
