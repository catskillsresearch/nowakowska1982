/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Mixed.MixedSystem
import Mathlib.Tactic

@[expose] public section

/-!
# Projection `π` from mixed strings to action strings (§5.2.1)

Verbal runs are replaced by `pauseString` of total sentence duration in
pause-units; actions pass through. This yields a monoid homomorphism.
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- Flush pending sentence-duration as pauses, then continue. -/
def piGo : ℕ → List S.Letter → List S.D
  | pending, [] => S.base.pauseString pending
  | pending, Sum.inl d :: rest =>
      S.base.pauseString pending ++ d :: piGo 0 rest
  | pending, Sum.inr α :: rest =>
      piGo (pending + S.φM α) rest

/-- Behavioural projection `π : (D ∪ M)* → D*`. -/
def pi (x : List S.Letter) : List S.D :=
  piGo S 0 x

namespace pi

theorem go_add_pending (p q : ℕ) (x : List S.Letter) :
    S.piGo (p + q) x = S.base.pauseString p ++ S.piGo q x := by
  induction x generalizing p q with
  | nil =>
      simp only [piGo, ActionSystem.pauseString]
      rw [List.replicate_add]
  | cons c rest ih =>
      match c with
      | Sum.inl d =>
          simp only [piGo]
          have hpq : S.base.pauseString (p + q) =
              S.base.pauseString p ++ S.base.pauseString q := by
            simp only [ActionSystem.pauseString]
            rw [List.replicate_add]
          rw [hpq, List.append_assoc]
      | Sum.inr α =>
          have h := ih p (q + S.φM α)
          simpa [piGo, Nat.add_assoc] using h

theorem map_append (x y : List S.Letter) :
    S.pi (x ++ y) = S.pi x ++ S.pi y := by
  have aux : ∀ p (x y : List S.Letter),
      S.piGo p (x ++ y) = S.piGo p x ++ S.piGo 0 y := by
    intro p x
    induction x generalizing p with
    | nil =>
        intro y
        simpa [piGo] using go_add_pending S p 0 y
    | cons c rest ih =>
        intro y
        match c with
        | Sum.inl d =>
            simp only [piGo, List.cons_append]
            rw [ih]
            simp [List.cons_append]
        | Sum.inr α =>
            simp only [piGo, List.cons_append]
            exact ih (p + S.φM α) y
  simpa [pi] using aux 0 x y

@[simp] theorem nil : S.pi ([] : List S.Letter) = [] := by
  simp only [pi, piGo, ActionSystem.pauseString, List.replicate_zero]

theorem pure_actions (u : List S.D) :
    S.pi (u.map Sum.inl) = u := by
  induction u with
  | nil => simp
  | cons d rest ih =>
      simp only [List.map_cons, pi, piGo, ActionSystem.pauseString, List.replicate_zero,
        List.nil_append]
      exact congrArg (d :: ·) (by simpa [pi] using ih)

/-- Duration of `π` equals mixed duration, after flushing `pending` pauses. -/
theorem stringDuration_piGo (p : ℕ) (x : List S.Letter) :
    S.base.stringDuration (S.piGo p x) = (p : ℝ) + S.mixedDuration x := by
  induction x generalizing p with
  | nil =>
      simp [piGo, mixedDuration, ActionSystem.stringDuration_pauseString]
  | cons c rest ih =>
      match c with
      | Sum.inl d =>
          simp only [piGo, mixedDuration_cons, letterDuration]
          rw [ActionSystem.stringDuration.append, ActionSystem.stringDuration_pauseString,
            ActionSystem.stringDuration_cons, ih 0]
          ring
      | Sum.inr α =>
          simp only [piGo, mixedDuration_cons, letterDuration]
          have h := ih (p + S.φM α)
          rw [h]
          push_cast
          ring

/-- **Duration homomorphism:** `stringDuration (π x) = mixedDuration x`. -/
theorem stringDuration_pi (x : List S.Letter) :
    S.base.stringDuration (S.pi x) = S.mixedDuration x := by
  simpa [pi] using stringDuration_piGo S 0 x

/-- Discrete utterance time of `π x` is the floor of mixed duration. -/
theorem utteranceTime_pi (x : List S.Letter) :
    S.utteranceTime (S.pi x) = Nat.floor (S.mixedDuration x) := by
  simp [utteranceTime, stringDuration_pi]

end pi

end MixedSystem
end Actions
