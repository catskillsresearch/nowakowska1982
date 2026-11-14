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
public import Actions.Promise.Horizons
public import Actions.Promise.PositiveCF
public import Actions.Promise.OffenseCF
public import Actions.Automata.Automaton
public import Actions.Choice.TotalPreorder
public import Actions.Choice.Arrow
public import Actions.Examples.ToyWorld

