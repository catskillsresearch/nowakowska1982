/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module -- shake: keep-all

-- Single library root: every `.lean` under Actions/ is imported here.
-- lake build elaborates this module (hence all of them). Rename/delete without
-- updating this list breaks the build.

public import Actions.ActionSystem
public import Actions.Attainability.Goals
public import Actions.Attainability.Conflicts
public import Actions.Means.Prax
public import Actions.Motivation.EpistemicModel
public import Actions.Motivation.GladModel
public import Actions.Motivation.SemImp
public import Actions.Motivation.SampledSemImp
public import Actions.Motivation.PreferWantCan
public import Actions.Promise.minφ
public import Actions.Promise.stringDuration
public import Actions.Promise.HatT
public import Actions.Promise.HatU
public import Actions.Promise.LanguageHypotheses
public import Actions.Promise.promiseSuffixLang
public import Actions.Promise.PromiseClosed
public import Actions.Promise.offenseSuffixLang
public import Actions.Promise.OffenseClosed
public import Actions.Automata.ActionAutomaton
public import Actions.Automata.toActionSystem
public import Actions.Choice.TotalPreorder
public import Actions.Choice.Arrow
public import Actions.Choice.prefer
public import Actions.Choice.scale1Dictator
public import Actions.Choice.scale2Dictator
public import Actions.Choice.ArrowPostulates2
public import Actions.Choice.CompulsiveOrHedonistic
public import Actions.Choice.BlindObedience
public import Actions.Choice.NeuroticAllOrNothing
public import Actions.Examples.ToyWorld

