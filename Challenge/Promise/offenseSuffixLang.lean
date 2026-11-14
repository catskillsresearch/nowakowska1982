/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Promise.HatU
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.MyhillNerode
import Mathlib.Tactic

@[expose] public section

/-!
# Regular suffix envelope of \(\hat U\)
-/

open scoped Computability

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

def offenseSuffixLang (U : Set (List A.D)) : Language A.D :=
  { x | ∃ u ∈ A.HatU U, ∃ v : List A.D, x = u ++ v }

namespace offenseSuffixLang

theorem suffix_closed {U : Set (List A.D)}
    {x y : List A.D} (hx : x ∈ A.offenseSuffixLang U) :
    x ++ y ∈ A.offenseSuffixLang U := by
  rcases hx with ⟨u, hu, v, rfl⟩
  exact ⟨u, hu, v ++ y, by simp [List.append_assoc]⟩

theorem none_of_long {U : Set (List A.D)} {M : ℝ}
    (hFin : ∀ z ∈ A.HatU U, A.stringDuration z ≤ M)
    {x : List A.D} (hxC : x ∉ A.offenseSuffixLang U)
    (hxM : M < A.stringDuration x) (y : List A.D) :
    x ++ y ∉ A.offenseSuffixLang U := by
  intro h
  rcases h with ⟨u, hu, v, hv⟩
  have huM := hFin u hu
  rcases List.append_eq_append_iff.mp hv with (⟨w, hu_eq, _⟩ | ⟨w, hx_eq, _⟩)
  · subst hu_eq
    by_cases hw0 : w = []
    · subst hw0
      have : x ∈ A.HatU U := by simpa using hu
      exact hxC ⟨x, this, [], by simp⟩
    · have hwpos := stringDuration.pos_of_ne_nil A hw0
      have hdur := stringDuration.append A x w
      linarith
  · subst hx_eq
    exact hxC ⟨u, hu, w, rfl⟩

theorem isRegular [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)} (hFin : A.FiniteOffenseHorizon U) :
    Language.IsRegular (A.offenseSuffixLang U) := by
  classical
  rcases hFin with ⟨M, hM⟩
  let Short : Set (List A.D) := { x | A.stringDuration x ≤ M }
  have hShort : Short.Finite := A.finite_bounded_duration M
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  let candidates : Set (Language A.D) :=
    {(⊤ : Language A.D), (⊥ : Language A.D)} ∪
      (A.offenseSuffixLang U).leftQuotient '' Short
  have hfin : candidates.Finite :=
    (Set.toFinite {(⊤ : Language A.D), (⊥ : Language A.D)}).union (hShort.image _)
  refine hfin.subset ?_
  intro L hL
  rcases hL with ⟨x, rfl⟩
  by_cases hx : x ∈ A.offenseSuffixLang U
  · refine Or.inl (Or.inl ?_)
    ext y
    constructor
    · intro; trivial
    · intro; exact offenseSuffixLang.suffix_closed A hx
  · by_cases hxM : A.stringDuration x ≤ M
    · exact Or.inr ⟨x, hxM, rfl⟩
    · refine Or.inl (Or.inr ?_)
      push Not at hxM
      ext y
      constructor
      · intro hy
        have : x ++ y ∈ A.offenseSuffixLang U := by
          simpa [Language.mem_leftQuotient] using hy
        exact (offenseSuffixLang.none_of_long A hM hx hxM y this).elim
      · intro hy; exact hy.elim

end offenseSuffixLang

end ActionSystem
end Actions
