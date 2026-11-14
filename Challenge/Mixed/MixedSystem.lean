/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Mixed.NonParasitic
public import Challenge.Mixed.RinvSet
public import Challenge.Promise.stringDuration
import Mathlib.Tactic

@[expose] public section

/-!
# Enriched action system with verbal primitives (§5.1)

Nowakowska (1973) §5.1: system
`⟨D, L, M, φ, S, ρ, W, W', O, O'⟩` with assumptions (7), (11)–(13).
Sentence durations are discrete pause-units (`ℕ`), a modeling simplification
of the paper’s real-valued `φ` on `M` (still allowed to be zero).
-/

namespace Actions

/-- Action system enriched by motivational sentences and the four utterance
relations. -/
structure MixedSystem where
  /-- Underlying action sixtuplet. -/
  toActionSystem : ActionSystem
  /-- Alphabet of motivational sentences. -/
  M : Type*
  /-- Duration of a sentence in pause-units (may be zero). -/
  φM : M → ℕ
  /-- Wanted time-results when `α` is uttered at discrete time `k`. -/
  W : M → ℕ → Set (toActionSystem.S × ℕ)
  /-- Unwanted *results* when `α` is uttered at time `k`. -/
  W'_results : M → ℕ → Set toActionSystem.S
  /-- Obligation: subsequent strings that ought to be chosen. -/
  O : M → ℕ → Set (List toActionSystem.D)
  /-- Prohibition: subsequent strings that should not be chosen. -/
  O' : M → ℕ → Set (List toActionSystem.D)
  /-- Assumption (7): same utterance is not self-contradictory on wants. -/
  W_disjoint_W' : ∀ α k s n,
    (s, n) ∈ W α k → s ∉ W'_results α k
  /-- Assumption (11): positive obligations are right-closed in `D*₊`. -/
  O_right_closed : ∀ α k {u v : List toActionSystem.D},
    u ∈ O α k → (∃ w₁ w₂, w₁ ++ u ++ v ++ w₂ ∈ toActionSystem.L) →
      u ++ v ∈ O α k
  /-- Assumption (12): prohibitions are two-sided closed in `D*₊`. -/
  O'_embed_closed : ∀ α k {u v w : List toActionSystem.D},
    v ∈ O' α k → (∃ w₁ w₂, w₁ ++ u ++ v ++ w ++ w₂ ∈ toActionSystem.L) →
      u ++ v ++ w ∈ O' α k
  /-- Assumption (13): every utterance asserts at least one of the four. -/
  utterance_nonempty : ∀ α k,
    (W α k).Nonempty ∨ (W'_results α k).Nonempty ∨
      (O α k).Nonempty ∨ (O' α k).Nonempty

namespace MixedSystem

variable (S : MixedSystem)

/-- Underlying action system. -/
abbrev base : ActionSystem := S.toActionSystem

abbrev D := S.base.D
abbrev L := S.base.L
abbrev TimeResult := S.base.TimeResult

/-- Unwanted time-results: all times for each unwanted result (formula (6)). -/
def W' (α : S.M) (k : ℕ) : Set S.TimeResult :=
  { p | p.1 ∈ S.W'_results α k }
-- compared Actions.MixedSystem.W_disjoint in Challenge.lean
abbrev Letter := Sum S.D S.M

/-- Duration of one mixed letter. -/
noncomputable def letterDuration : S.Letter → ℝ
  | Sum.inl d => S.base.φ d
  | Sum.inr α => (S.φM α : ℝ)

/-- Duration of a mixed string. -/
noncomputable def mixedDuration (x : List S.Letter) : ℝ :=
  (x.map S.letterDuration).sum

@[simp] theorem mixedDuration_nil : S.mixedDuration [] = 0 := by
  simp [mixedDuration]

@[simp] theorem mixedDuration_cons (c : S.Letter) (x : List S.Letter) :
    S.mixedDuration (c :: x) = S.letterDuration c + S.mixedDuration x := by
  simp [mixedDuration]

/-- Discrete utterance time of an action prefix. -/
noncomputable def utteranceTime (u : List S.D) : ℕ :=
  Nat.floor (S.base.stringDuration u)

end MixedSystem

end Actions
