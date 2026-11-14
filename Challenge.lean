/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Attainability.Conflicts
public import Actions.Automata.ToActionSystem
public import Actions.Choice.Arrow
public import Actions.Motivation.SampledSemImp
public import Actions.Promise.PositiveCF
public import Actions.Promise.OffenseCF
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
