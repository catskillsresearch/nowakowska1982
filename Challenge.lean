/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Attainability.Conflicts
public import Actions.Automata.Automaton
public import Actions.Choice.Arrow
public import Actions.Motivation.MotCalc
public import Actions.Promise.Promise
public import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

open scoped Computability

/-!
# Palomar Challenge

Compared family: 113 conflict count (novel), automaton realization (novel),
Arrow dictatorial core + clinical defs, MotCalc sampled SemImp validity,
promise CF preservation (novel reconstructions from 1973 §5.3).
-/

namespace Challenge

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

/-- MotCalc sample: every epistemic model validates the sampled SemImp bundle. -/
theorem epistemicModel_sampledSemImp {X : Type*} (M : Actions.MotCalc.EpistemicModel X) :
    Actions.MotCalc.SampledSemImp X M :=
  Actions.MotCalc.epistemicModel_sampledSemImp M

/-- Positive promise CF (hypotheses: Ch. 3 closures). -/
theorem promise_isContextFree
    (A : Actions.ActionSystem) [Fintype A.D] [Nonempty A.D]
    {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) (hFin : A.FiniteHorizon T)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (hRegCF : Actions.ActionSystem.RegularImpliesCF A.D)
    (hInter : Actions.ActionSystem.CFInterRegular A.D) :
    Language.IsContextFree (T : Language A.D) :=
  A.promise_isContextFree hSub ha hFin hL hRegCF hInter

/-- Negative / offense CF (hypotheses: Ch. 3 closures). -/
theorem offense_isContextFree
    (A : Actions.ActionSystem) [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) (hFin : A.FiniteOffenseHorizon U)
    (hPrime : A.OffensePrime U)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (hRegCF : Actions.ActionSystem.RegularImpliesCF A.D)
    (hInter : Actions.ActionSystem.CFInterRegular A.D) :
    Language.IsContextFree (U : Language A.D) :=
  A.offense_isContextFree hSub hb hFin hPrime hL hRegCF hInter

end Challenge
