/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Attainability.Goals
public import Actions.Means.Prax
public import Actions.Promise.Promise
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

theorem toy_pause_duration : toy.φ Act.pause = 1 := rfl

theorem toy_work_duration : toy.φ Act.work = 2 := rfl

/-- The string `[work]` attains `(done, 1)`. -/
theorem work_attains : toy.Attainable Out.done 1 := by
  refine ⟨[Act.work], ?_⟩
  simp [ActionSystem.Rinv, toy]
  decide

/-- Two goals at incompatible times: weakly attainable, not strongly. -/
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

theorem twoGoals_conflict : toy.MotiveConflict twoGoals :=
  ⟨twoGoals_weakly, twoGoals_not_strongly⟩

/-- Positive promise set: all strings containing `work`. -/
def promiseT : Set (List Act) :=
  { u | Act.work ∈ u }

theorem promiseT_closed : toy.PromiseClosed promiseT := by
  intro x y _ hx
  simp only [promiseT] at hx ⊢
  exact List.mem_append.mpr (Or.inl hx)

/-- `[work]` belongs to the promise set. -/
theorem work_mem_promiseT : [Act.work] ∈ promiseT := by
  simp [promiseT]

/-- Empty string is not in the promise set. -/
theorem nil_not_mem_promiseT : ([] : List Act) ∉ promiseT := by
  simp [promiseT]

theorem Prax_empty_example : toy.Prax (∅ : Set (List Act)) = ∅ :=
  toy.Prax_empty

/-- Duration of a single `work` action. -/
theorem work_string_duration : toy.stringDuration [Act.work] = 2 := by
  simp [ActionSystem.stringDuration, toy]

end Toy
end Actions
