/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Promise.HatT
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.MyhillNerode
import Mathlib.Tactic

@[expose] public section

/-!
# Regular suffix envelope of \(\hat T\)
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

end ActionSystem
end Actions
