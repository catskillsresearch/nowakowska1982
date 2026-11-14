/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module
public import Challenge.Attainability.Goals
public import Challenge.Means.Prax
public import Challenge.Promise.PromiseClosed
import Mathlib.Tactic
@[expose] public section
/-!
# Toy example world
A tiny checked instance: two actions (pause / act), one outcome, and a
conflict between two time-results that is weakly but not strongly attainable.
-/
namespace Actions
namespace Toy

inductive Act where
  | pause
  | work
  deriving DecidableEq, Repr

inductive Out where
  | done
  deriving DecidableEq, Repr

/-- Toy system: any string is admissible; `work` causes `done` at time equal
to string length. -/
def toy : ActionSystem where
  D := Act
  pause := Act.pause
  φ := fun
    | Act.pause => 1
    | Act.work => 2
  φ_pos := fun
    | Act.pause => by norm_num
    | Act.work => by norm_num
  φ_pause := rfl
  S := Out
  L := Set.univ
  R := fun u s t => s = Out.done ∧ t = u.length ∧ Act.work ∈ u
  R_mem_L := fun _ => trivial
-- compared Actions.Toy.toy_pause_duration in Challenge.lean
-- compared Actions.Toy.toy_work_duration in Challenge.lean
-- compared Actions.Toy.work_attains in Challenge.lean
def twoGoals : toy.GoalSet :=
  [(Out.done, 1), (Out.done, 2)]

theorem mem_twoGoals_1 : (Out.done, 1) ∈ twoGoals :=
  List.Mem.head _

theorem mem_twoGoals_2 : (Out.done, 2) ∈ twoGoals :=
  List.Mem.tail _ (List.Mem.head _)

theorem twoGoals_weakly : toy.WeaklyAttainable twoGoals := by
  refine ⟨[Act.work], (Out.done, 1), mem_twoGoals_1, ?_⟩
  simp [ActionSystem.Rinv, toy]
  decide

theorem twoGoals_not_strongly : ¬ toy.StronglyAttainable twoGoals := by
  intro ⟨u, hu⟩
  have h1 := hu (Out.done, 1) mem_twoGoals_1
  have h2 := hu (Out.done, 2) mem_twoGoals_2
  simp [ActionSystem.Rinv, toy] at h1 h2
  obtain ⟨hlen1, _⟩ := h1
  obtain ⟨hlen2, _⟩ := h2
  have : (1 : ℕ) = 2 := hlen1.trans hlen2.symm
  exact absurd this (by decide)
-- compared Actions.Toy.twoGoals_conflict in Challenge.lean
def promiseT : Set (List Act) :=
  { u | Act.work ∈ u }
-- compared Actions.Toy.promiseT_closed in Challenge.lean
-- compared Actions.Toy.work_mem_promiseT in Challenge.lean
-- compared Actions.Toy.nil_not_mem_promiseT in Challenge.lean
-- compared Actions.Toy.Prax_empty_example in Challenge.lean
-- compared Actions.Toy.work_string_duration in Challenge.lean
end Toy
end Actions
