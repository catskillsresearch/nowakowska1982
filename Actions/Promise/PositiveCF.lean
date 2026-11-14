/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Promise.Horizons
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.MyhillNerode
import Mathlib.Tactic

@[expose] public section

/-!
# Positive promise context-freeness

Reconstruction of Nowakowska 1973 Thm 1 / 1982 §7 positive promise CF.
-/

open scoped Computability

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

def promiseSuffixLang (T : Set (List A.D)) : Language A.D :=
  { x | ∃ u ∈ A.HatT T, ∃ v : List A.D, x = u ++ v }

namespace promiseSuffixLang

theorem suffix_closed {T : Set (List A.D)}
    {x y : List A.D} (hx : x ∈ A.promiseSuffixLang T) :
    x ++ y ∈ A.promiseSuffixLang T := by
  rcases hx with ⟨u, hu, v, rfl⟩
  exact ⟨u, hu, v ++ y, by simp [List.append_assoc]⟩

theorem none_of_long {T : Set (List A.D)} {M : ℝ}
    (hFin : ∀ z ∈ A.HatT T, A.stringDuration z ≤ M)
    {x : List A.D} (hxC : x ∉ A.promiseSuffixLang T)
    (hxM : M < A.stringDuration x) (y : List A.D) :
    x ++ y ∉ A.promiseSuffixLang T := by
  intro h
  rcases h with ⟨u, hu, v, hv⟩
  have huM := hFin u hu
  rcases List.append_eq_append_iff.mp hv with (⟨w, hu_eq, _⟩ | ⟨w, hx_eq, _⟩)
  · subst hu_eq
    by_cases hw0 : w = []
    · subst hw0
      have : x ∈ A.HatT T := by simpa using hu
      exact hxC ⟨x, this, [], by simp⟩
    · have hwpos := stringDuration.pos_of_ne_nil A hw0
      have hdur := stringDuration.append A x w
      linarith
  · subst hx_eq
    exact hxC ⟨u, hu, w, rfl⟩

theorem isRegular [Fintype A.D] [Nonempty A.D]
    {T : Set (List A.D)} (hFin : A.FiniteHorizon T) :
    Language.IsRegular (A.promiseSuffixLang T) := by
  classical
  rcases hFin with ⟨M, hM⟩
  let Short : Set (List A.D) := { x | A.stringDuration x ≤ M }
  have hShort : Short.Finite := A.finite_bounded_duration M
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  let candidates : Set (Language A.D) :=
    {(⊤ : Language A.D), (⊥ : Language A.D)} ∪
      (A.promiseSuffixLang T).leftQuotient '' Short
  have hfin : candidates.Finite :=
    (Set.toFinite {(⊤ : Language A.D), (⊥ : Language A.D)}).union (hShort.image _)
  refine hfin.subset ?_
  intro L hL
  rcases hL with ⟨x, rfl⟩
  by_cases hx : x ∈ A.promiseSuffixLang T
  · refine Or.inl (Or.inl ?_)
    ext y
    constructor
    · intro; trivial
    · intro
      exact promiseSuffixLang.suffix_closed A hx
  · by_cases hxM : A.stringDuration x ≤ M
    · exact Or.inr ⟨x, hxM, rfl⟩
    · refine Or.inl (Or.inr ?_)
      push Not at hxM
      ext y
      constructor
      · intro hy
        have : x ++ y ∈ A.promiseSuffixLang T := by
          simpa [Language.mem_leftQuotient] using hy
        exact (promiseSuffixLang.none_of_long A hM hx hxM y this).elim
      · intro hy; exact hy.elim

end promiseSuffixLang

namespace HatT
theorem exists_prefix {T : Set (List A.D)} {x : List A.D}
    (hx : x ∈ T) : ∃ u v, x = u ++ v ∧ u ∈ A.HatT T := by
  have : ∀ n : ℕ, ∀ x : List A.D, x.length = n → x ∈ T →
      ∃ u v, x = u ++ v ∧ u ∈ A.HatT T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hlen hx
      by_cases hhat :
          ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ T
      · exact ⟨x, [], by simp, ⟨hx, hhat⟩⟩
      · push Not at hhat
        rcases hhat with ⟨x₁, x₂, rfl, hpos, hx₁⟩
        have hx₂ : x₂ ≠ [] := fun h => by simp [h, stringDuration] at hpos
        have hlen₁ : x₁.length < n := by
          rw [← hlen, List.length_append]
          have : 0 < x₂.length := List.length_pos_of_ne_nil hx₂
          omega
        rcases ih _ hlen₁ x₁ rfl hx₁ with ⟨u, v, rfl, hu⟩
        exact ⟨u, v ++ x₂, by simp [List.append_assoc], hu⟩
  exact this x.length x rfl hx
end HatT

namespace PromiseClosed
theorem eq_L_inter_suffix {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) :
    T = A.L ∩ A.promiseSuffixLang T := by
  ext x
  constructor
  · intro hx
    refine ⟨hSub hx, ?_⟩
    rcases HatT.exists_prefix A hx with ⟨u, v, rfl, hu⟩
    exact ⟨u, hu, v, rfl⟩
  · intro ⟨hxL, hxC⟩
    rcases hxC with ⟨u, hu, v, rfl⟩
    exact ha hxL hu.1

/-- Positive promise CF (1982 §7 / 1973 Thm 1). Palomar novel reconstruction. -/
theorem isContextFree [Fintype A.D] [Nonempty A.D]
    {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) (hFin : A.FiniteHorizon T)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (_hRegCF : RegularImpliesCF A.D) (hInter : CFInterRegular A.D) :
    Language.IsContextFree (T : Language A.D) := by
  have hCreg := promiseSuffixLang.isRegular A hFin
  have hEq : (T : Language A.D) =
      (A.L : Language A.D) ⊓ A.promiseSuffixLang T := by
    change (T : Set _) = (A.L ∩ A.promiseSuffixLang T : Set _)
    exact PromiseClosed.eq_L_inter_suffix A hSub ha
  rw [hEq]
  exact hInter _ _ hL hCreg
end PromiseClosed

end ActionSystem
end Actions
