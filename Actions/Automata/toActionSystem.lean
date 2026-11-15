/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Automata.ActionAutomaton
import Mathlib.Tactic

@[expose] public section

/-!
# Automaton → action-system bridge

An automaton with a fixed start `(u₀,b₀)` induces an `ActionSystem`:
duration is constantly `1`, outcomes are the automaton states, the language
is the automaton language, and causation is *reachability*:
`R u s t` holds when the run `u` from `(u₀,b₀)` ends in state `s`, at time
`t = u.length` (every letter lasts one time unit).

The substantive content is `Attainable_iff_reaches_length` /
`Attainable_iff_reachableIn`: a time-result `(s,t)` is attainable in the
induced system iff `s` is reachable from the start in exactly `t` steps.
-/

namespace Actions
namespace ActionAutomaton

variable (M : ActionAutomaton)

/-- Bridge: an automaton with a fixed start induces an `ActionSystem`
(duration constantly `1`, outcomes = states, causation = reachability, with
the time of a run being its length). -/
noncomputable def toActionSystem (u₀ : M.U) (b₀ : M.B) : ActionSystem where
  D := M.D
  pause := M.pause
  φ := fun _ => (1 : ℝ)
  φ_pos := fun _ => zero_lt_one
  φ_pause := rfl
  S := M.U
  L := M.language u₀ b₀
  R := fun u s t => M.Reaches u₀ b₀ u s ∧ t = u.length
  R_mem_L := fun h => (Reaches.admissible (M := M) h.1)

namespace toActionSystem

/-- **Novel realization theorem** (1982 §13 states the reading; no proof is
given there): the induced sixtuplet’s language is exactly the automaton
language from `(u₀,b₀)`. -/
theorem L (u₀ : M.U) (b₀ : M.B) :
    (M.toActionSystem u₀ b₀).L = M.language u₀ b₀ :=
  rfl

/-- Strings of the induced system are precisely the admissible runs. -/
theorem mem_L_iff (u₀ : M.U) (b₀ : M.B) (ds : List M.D) :
    ds ∈ (M.toActionSystem u₀ b₀).L ↔ M.Admissible u₀ b₀ ds :=
  Iff.rfl

/-- Every letter of the induced system lasts one time unit. -/
theorem φ_eq_one (u₀ : M.U) (b₀ : M.B) (d : M.D) :
    (M.toActionSystem u₀ b₀).φ d = 1 :=
  rfl

/-- Causation in the induced system: the run `u` from the start ends in `s`,
and the time is the length of `u`. -/
theorem R_iff (u₀ : M.U) (b₀ : M.B) (u : List M.D) (s : M.U) (t : ℕ) :
    (M.toActionSystem u₀ b₀).R u s t ↔ M.Reaches u₀ b₀ u s ∧ t = u.length :=
  Iff.rfl

/-- Causation only holds for admissible strings (sixtuplet law): a run that
reaches a state is admissible. -/
theorem R_mem_L (u₀ : M.U) (b₀ : M.B)
    {u : List M.D} {s : M.U} {t : ℕ}
    (h : (M.toActionSystem u₀ b₀).R u s t) :
    u ∈ (M.toActionSystem u₀ b₀).L :=
  (M.mem_language_iff_exists_reaches u₀ b₀ u).2 ⟨s, h.1⟩

/-- Conversely, every string of the language causes some outcome, at the time
given by its length. -/
theorem mem_L_iff_exists_R (u₀ : M.U) (b₀ : M.B) (ds : List M.D) :
    ds ∈ (M.toActionSystem u₀ b₀).L ↔
      ∃ s, (M.toActionSystem u₀ b₀).R ds s ds.length := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (M.mem_language_iff_exists_reaches u₀ b₀ ds).1 h
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs⟩
    exact R_mem_L M u₀ b₀ hs

/-- The inverse image of `(s,t)`: runs of length `t` from the start to `s`. -/
theorem mem_Rinv_iff (u₀ : M.U) (b₀ : M.B) (s : M.U) (t : ℕ) (ds : List M.D) :
    ds ∈ (M.toActionSystem u₀ b₀).Rinv s t ↔
      M.Reaches u₀ b₀ ds s ∧ ds.length = t := by
  change M.Reaches u₀ b₀ ds s ∧ t = ds.length ↔ _
  rw [eq_comm]

/-- **Attainability is reachability**: `(s,t)` is attainable in the induced
system iff some run of length `t` from `(u₀,b₀)` ends in `s`. -/
theorem Attainable_iff_reaches_length (u₀ : M.U) (b₀ : M.B) (s : M.U) (t : ℕ) :
    (M.toActionSystem u₀ b₀).Attainable s t ↔
      ∃ ds : List M.D, ds.length = t ∧ M.Reaches u₀ b₀ ds s := by
  constructor
  · rintro ⟨ds, hds⟩
    obtain ⟨hr, hlen⟩ := (mem_Rinv_iff M u₀ b₀ s t ds).1 hds
    exact ⟨ds, hlen, hr⟩
  · rintro ⟨ds, hlen, hr⟩
    exact ⟨ds, (mem_Rinv_iff M u₀ b₀ s t ds).2 ⟨hr, hlen⟩⟩

/-- **Attainability is step-counted reachability** (string-free form):
`(s,t)` is attainable iff `s` is reachable from `(u₀,b₀)` in exactly `t`
steps of the transition structure. -/
theorem Attainable_iff_reachableIn (u₀ : M.U) (b₀ : M.B) (s : M.U) (t : ℕ) :
    (M.toActionSystem u₀ b₀).Attainable s t ↔ M.ReachableIn u₀ b₀ t s := by
  rw [Attainable_iff_reaches_length, reachableIn_iff_exists_reaches]

/-- At time `0` exactly the start state is attainable. -/
theorem Attainable_zero_iff (u₀ : M.U) (b₀ : M.B) (s : M.U) :
    (M.toActionSystem u₀ b₀).Attainable s 0 ↔ s = u₀ := by
  rw [Attainable_iff_reachableIn, reachableIn_zero_iff]

/-- The start state is attainable at time `0`. -/
theorem start_Attainable (u₀ : M.U) (b₀ : M.B) :
    (M.toActionSystem u₀ b₀).Attainable u₀ 0 :=
  (Attainable_zero_iff M u₀ b₀ u₀).2 rfl

/-- Attainability recurrence: `(s,t+1)` is attainable from `(u₀,b₀)` iff after
one admissible letter `d` and some next stimulus `b'`, `(s,t)` is attainable
in the system restarted at `(π u₀ b₀ d, b')`. -/
theorem Attainable_succ_iff (u₀ : M.U) (b₀ : M.B) (s : M.U) (t : ℕ) :
    (M.toActionSystem u₀ b₀).Attainable s (t + 1) ↔
      ∃ d ∈ M.τ u₀ b₀, ∃ b',
        (M.toActionSystem (M.π u₀ b₀ d) b').Attainable s t := by
  simp only [Attainable_iff_reachableIn, reachableIn_succ_iff]

/-- An attainable time-result is witnessed by a string of the language whose
length is the time. -/
theorem Attainable.exists_mem_L (u₀ : M.U) (b₀ : M.B) {s : M.U} {t : ℕ}
    (h : (M.toActionSystem u₀ b₀).Attainable s t) :
    ∃ ds ∈ (M.toActionSystem u₀ b₀).L, ds.length = t := by
  obtain ⟨ds, hlen, hr⟩ := (Attainable_iff_reaches_length M u₀ b₀ s t).1 h
  exact ⟨ds, hr.admissible, hlen⟩

end toActionSystem

end ActionAutomaton
end Actions
