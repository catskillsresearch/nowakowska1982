/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Automata.ActionAutomaton
import Mathlib.Tactic

@[expose] public section

/-!
# Automaton → action-system bridge

An automaton with a fixed start induces an `ActionSystem` skeleton
(duration constantly `1`, outcomes = states).
-/

namespace Actions
namespace ActionAutomaton

variable (M : ActionAutomaton)

/-- Bridge: an automaton with a fixed start induces an `ActionSystem`
skeleton (duration constantly `1`, outcomes = states). -/
noncomputable def toActionSystem (u₀ : M.U) (b₀ : M.B) : ActionSystem where
  D := M.D
  pause := M.pause
  φ := fun _ => (1 : ℝ)
  φ_pos := fun _ => by norm_num
  φ_pause := rfl
  S := M.U
  L := M.language u₀ b₀
  R := fun u s _t => u ∈ M.language u₀ b₀ ∧ s = u₀
  R_mem_L := fun h => h.1

namespace toActionSystem
-- compared Actions.ActionAutomaton.toActionSystem.L in Challenge.lean
-- compared Actions.ActionAutomaton.toActionSystem.mem_L_iff in Challenge.lean
theorem R_mem_L (u₀ : M.U) (b₀ : M.B)
    {u : List M.D} {s : M.U} {t : ℕ}
    (h : (M.toActionSystem u₀ b₀).R u s t) :
    u ∈ (M.toActionSystem u₀ b₀).L :=
  (M.toActionSystem u₀ b₀).R_mem_L h

end toActionSystem

end ActionAutomaton
end Actions
