/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module -- shake: keep-all

-- Single library root: every `.lean` under Actions/ is imported here.
-- lake build elaborates this module (hence all of them). Rename/delete without
-- updating this list breaks the build.

public import Actions.Basic.ActionSystem
public import Actions.Attainability.Goals
public import Actions.Means.Prax
public import Actions.Promise.Promise
public import Actions.Automata.Automaton
public import Actions.Examples.ToyWorld
