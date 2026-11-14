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
# Offense / negative promise context-freeness

Reconstruction of Nowakowska 1973 Thm 4 / 1982 §7 offense CF.
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

namespace HatU
theorem exists_prefix {U : Set (List A.D)} {x : List A.D}
    (hx : x ∈ U) : ∃ u v, x = u ++ v ∧ u ∈ A.HatU U := by
  have : ∀ n : ℕ, ∀ x : List A.D, x.length = n → x ∈ U →
      ∃ u v, x = u ++ v ∧ u ∈ A.HatU U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hlen hx
      by_cases hhat :
          ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ U
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
end HatU

namespace OffenseClosed
theorem eq_L_inter_suffix {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) :
    U = A.L ∩ A.offenseSuffixLang U := by
  ext x
  constructor
  · intro hx
    refine ⟨hSub hx, ?_⟩
    rcases HatU.exists_prefix A hx with ⟨u, v, rfl, hu⟩
    exact ⟨u, hu, v, rfl⟩
  · intro ⟨hxL, hxC⟩
    rcases hxC with ⟨u, hu, v, rfl⟩
    have : [] ++ u ++ v ∈ A.L := by simpa using hxL
    exact hb this hu.1

/-- Negative/offense CF (1982 §7 / 1973 Thm 4). Palomar novel reconstruction. -/
theorem isContextFree [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) (hFin : A.FiniteOffenseHorizon U)
    (_hPrime : A.OffensePrime U)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (_hRegCF : RegularImpliesCF A.D) (hInter : CFInterRegular A.D) :
    Language.IsContextFree (U : Language A.D) := by
  have hCreg := offenseSuffixLang.isRegular A hFin
  have hEq : (U : Language A.D) =
      (A.L : Language A.D) ⊓ A.offenseSuffixLang U := by
    change (U : Set _) = (A.L ∩ A.offenseSuffixLang U : Set _)
    exact OffenseClosed.eq_L_inter_suffix A hSub hb
  rw [hEq]
  exact hInter _ _ hL hCreg
end OffenseClosed

end ActionSystem
end Actions
