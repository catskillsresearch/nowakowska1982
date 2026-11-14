/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.ActionSystem
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

@[expose] public section

/-!
# Motivational consistency: promises

Structural conditions (a)/(b), `HatT`/`HatU`, horizons, and context-free
preservation reconstructed from Nowakowska 1973 §5.3.2–5.3.3. Classical
Ch. 3 closures are explicit hypotheses (`CFInterRegular`, `RegularImpliesCF`).
-/

open scoped Computability

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

def PromiseClosed (T : Set (List A.D)) : Prop :=
  ∀ {x y : List A.D}, x ++ y ∈ A.L → x ∈ T → x ++ y ∈ T

def HatT (T : Set (List A.D)) : Set (List A.D) :=
  { x ∈ T |
      ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ T }

noncomputable def horizon (T : Set (List A.D)) : WithTop ℝ :=
  sSup ((A.stringDuration ·) '' A.HatT T)

def OffenseClosed (U : Set (List A.D)) : Prop :=
  ∀ {x y z : List A.D}, x ++ y ++ z ∈ A.L → y ∈ U → x ++ y ++ z ∈ U

def HatU (U : Set (List A.D)) : Set (List A.D) :=
  { v ∈ U |
      ∀ v₁ v₂, v = v₁ ++ v₂ → 0 < A.stringDuration v₂ → v₁ ∉ U }

def FiniteHorizon (T : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatT T, A.stringDuration x ≤ M

def FiniteOffenseHorizon (U : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatU U, A.stringDuration x ≤ M

def OffensePrime (U : Set (List A.D)) : Prop :=
  ∀ {u v : List A.D}, u ++ v ∈ U → u ∈ U ∨ v ∈ U

theorem promiseClosed_mono {T : Set (List A.D)}
    (ha : A.PromiseClosed T) {x y : List A.D}
    (hxy : x ++ y ∈ A.L) (hx : x ∈ T) : x ++ y ∈ T :=
  ha hxy hx

theorem stringDuration_nil_not_pos : ¬ (0 < A.stringDuration []) := by
  simp [stringDuration]

theorem HatT_subset (T : Set (List A.D)) : A.HatT T ⊆ T := fun _ hx => hx.1

theorem HatU_subset (U : Set (List A.D)) : A.HatU U ⊆ U := fun _ hx => hx.1

theorem stringDuration_append (x y : List A.D) :
    A.stringDuration (x ++ y) = A.stringDuration x + A.stringDuration y := by
  induction x with
  | nil => simp [stringDuration]
  | cons d x ih =>
      rw [List.cons_append, stringDuration_cons, stringDuration_cons, ih]
      ring

theorem stringDuration_nonneg (x : List A.D) : 0 ≤ A.stringDuration x := by
  induction x with
  | nil => simp [stringDuration]
  | cons d x ih =>
      have hφ := A.φ_pos d
      rw [stringDuration_cons]
      linarith

theorem stringDuration_pos_of_ne_nil {x : List A.D} (hx : x ≠ []) :
    0 < A.stringDuration x := by
  match x with
  | [] => cases hx rfl
  | d :: x =>
      have hφ := A.φ_pos d
      have h := A.stringDuration_nonneg x
      rw [stringDuration_cons]
      linarith

noncomputable def minφ [Fintype A.D] [Nonempty A.D] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty A.φ

theorem minφ_pos [Fintype A.D] [Nonempty A.D] : 0 < A.minφ := by
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty A.φ
  simpa [minφ, hd] using A.φ_pos d

theorem le_stringDuration_length [Fintype A.D] [Nonempty A.D] (x : List A.D) :
    (x.length : ℝ) * A.minφ ≤ A.stringDuration x := by
  induction x with
  | nil => simp [stringDuration]
  | cons d x ih =>
      have hd : A.minφ ≤ A.φ d := Finset.inf'_le _ (Finset.mem_univ d)
      rw [List.length_cons, stringDuration_cons]
      push_cast
      nlinarith

theorem finite_bounded_duration [Fintype A.D] [Nonempty A.D] (M : ℝ) :
    { x : List A.D | A.stringDuration x ≤ M }.Finite := by
  classical
  by_cases hM : M < 0
  · have : { x : List A.D | A.stringDuration x ≤ M } = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      have := A.stringDuration_nonneg x
      linarith
    simpa [this] using Set.finite_empty
  · have hmin := A.minφ_pos
    let N : ℕ := Nat.floor (M / A.minφ) + 1
    have hsub : { x : List A.D | A.stringDuration x ≤ M } ⊆
        { x : List A.D | x.length < N } := by
      intro x hx
      have hle : (x.length : ℝ) * A.minφ ≤ M :=
        le_trans (A.le_stringDuration_length x) hx
      have hdiv : (x.length : ℝ) ≤ M / A.minφ := (le_div_iff₀ hmin).mpr hle
      have : (x.length : ℝ) < (N : ℝ) := by
        have := lt_of_le_of_lt hdiv (Nat.lt_floor_add_one (M / A.minφ))
        simpa [N] using this
      exact_mod_cast this
    exact (List.finite_length_lt A.D N).subset hsub

def promiseSuffixLang (T : Set (List A.D)) : Language A.D :=
  { x | ∃ u ∈ A.HatT T, ∃ v : List A.D, x = u ++ v }

theorem promiseSuffixLang_suffix_closed {T : Set (List A.D)}
    {x y : List A.D} (hx : x ∈ A.promiseSuffixLang T) :
    x ++ y ∈ A.promiseSuffixLang T := by
  rcases hx with ⟨u, hu, v, rfl⟩
  exact ⟨u, hu, v ++ y, by simp [List.append_assoc]⟩

theorem exists_hatT_prefix {T : Set (List A.D)} {x : List A.D}
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

theorem promise_eq_L_inter_suffix {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) :
    T = A.L ∩ A.promiseSuffixLang T := by
  ext x
  constructor
  · intro hx
    refine ⟨hSub hx, ?_⟩
    rcases A.exists_hatT_prefix hx with ⟨u, v, rfl, hu⟩
    exact ⟨u, hu, v, rfl⟩
  · intro ⟨hxL, hxC⟩
    rcases hxC with ⟨u, hu, v, rfl⟩
    exact ha hxL hu.1

theorem promiseSuffixLang_none_of_long {T : Set (List A.D)} {M : ℝ}
    (hFin : ∀ z ∈ A.HatT T, A.stringDuration z ≤ M)
    {x : List A.D} (hxC : x ∉ A.promiseSuffixLang T)
    (hxM : M < A.stringDuration x) (y : List A.D) :
    x ++ y ∉ A.promiseSuffixLang T := by
  intro h
  rcases h with ⟨u, hu, v, hv⟩
  have huM := hFin u hu
  -- x++y = u++v
  rcases List.append_eq_append_iff.mp hv with (⟨w, hu_eq, _⟩ | ⟨w, hx_eq, _⟩)
  · -- u = x ++ w
    subst hu_eq
    by_cases hw0 : w = []
    · subst hw0
      have : x ∈ A.HatT T := by simpa using hu
      exact hxC ⟨x, this, [], by simp⟩
    · have hwpos := A.stringDuration_pos_of_ne_nil hw0
      have hdur := A.stringDuration_append x w
      linarith
  · -- x = u ++ w
    subst hx_eq
    exact hxC ⟨u, hu, w, rfl⟩

theorem promiseSuffixLang_isRegular [Fintype A.D] [Nonempty A.D]
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
      exact A.promiseSuffixLang_suffix_closed hx
  · by_cases hxM : A.stringDuration x ≤ M
    · exact Or.inr ⟨x, hxM, rfl⟩
    · refine Or.inl (Or.inr ?_)
      push Not at hxM
      ext y
      constructor
      · intro hy
        have : x ++ y ∈ A.promiseSuffixLang T := by
          simpa [Language.mem_leftQuotient] using hy
        exact (A.promiseSuffixLang_none_of_long hM hx hxM y this).elim
      · intro hy; exact hy.elim

def RegularImpliesCF (α : Type*) : Prop :=
  ∀ L : Language α, Language.IsRegular L → Language.IsContextFree L

def CFInterRegular (α : Type*) : Prop :=
  ∀ L R : Language α,
    Language.IsContextFree L → Language.IsRegular R →
      Language.IsContextFree (L ⊓ R)

/-- Positive promise CF (1982 §7 / 1973 Thm 1). Palomar novel reconstruction. -/
theorem promise_isContextFree [Fintype A.D] [Nonempty A.D]
    {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) (hFin : A.FiniteHorizon T)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (_hRegCF : RegularImpliesCF A.D) (hInter : CFInterRegular A.D) :
    Language.IsContextFree (T : Language A.D) := by
  have hCreg := A.promiseSuffixLang_isRegular hFin
  have hEq : (T : Language A.D) =
      (A.L : Language A.D) ⊓ A.promiseSuffixLang T := by
    change (T : Set _) = (A.L ∩ A.promiseSuffixLang T : Set _)
    exact A.promise_eq_L_inter_suffix hSub ha
  rw [hEq]
  exact hInter _ _ hL hCreg

def offenseSuffixLang (U : Set (List A.D)) : Language A.D :=
  { x | ∃ u ∈ A.HatU U, ∃ v : List A.D, x = u ++ v }

theorem offenseSuffixLang_suffix_closed {U : Set (List A.D)}
    {x y : List A.D} (hx : x ∈ A.offenseSuffixLang U) :
    x ++ y ∈ A.offenseSuffixLang U := by
  rcases hx with ⟨u, hu, v, rfl⟩
  exact ⟨u, hu, v ++ y, by simp [List.append_assoc]⟩

theorem offenseSuffixLang_none_of_long {U : Set (List A.D)} {M : ℝ}
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
    · have hwpos := A.stringDuration_pos_of_ne_nil hw0
      have hdur := A.stringDuration_append x w
      linarith
  · subst hx_eq
    exact hxC ⟨u, hu, w, rfl⟩

theorem offenseSuffixLang_isRegular [Fintype A.D] [Nonempty A.D]
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
    · intro; exact A.offenseSuffixLang_suffix_closed hx
  · by_cases hxM : A.stringDuration x ≤ M
    · exact Or.inr ⟨x, hxM, rfl⟩
    · refine Or.inl (Or.inr ?_)
      push Not at hxM
      ext y
      constructor
      · intro hy
        have : x ++ y ∈ A.offenseSuffixLang U := by
          simpa [Language.mem_leftQuotient] using hy
        exact (A.offenseSuffixLang_none_of_long hM hx hxM y this).elim
      · intro hy; exact hy.elim

theorem exists_hatU_prefix {U : Set (List A.D)} {x : List A.D}
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

theorem offense_eq_L_inter_suffix {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) :
    U = A.L ∩ A.offenseSuffixLang U := by
  ext x
  constructor
  · intro hx
    refine ⟨hSub hx, ?_⟩
    rcases A.exists_hatU_prefix hx with ⟨u, v, rfl, hu⟩
    exact ⟨u, hu, v, rfl⟩
  · intro ⟨hxL, hxC⟩
    rcases hxC with ⟨u, hu, v, rfl⟩
    have : [] ++ u ++ v ∈ A.L := by simpa using hxL
    exact hb this hu.1

/-- Negative/offense CF (1982 §7 / 1973 Thm 4). Palomar novel reconstruction. -/
theorem offense_isContextFree [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) (hFin : A.FiniteOffenseHorizon U)
    (_hPrime : A.OffensePrime U)
    (hL : Language.IsContextFree (A.L : Language A.D))
    (_hRegCF : RegularImpliesCF A.D) (hInter : CFInterRegular A.D) :
    Language.IsContextFree (U : Language A.D) := by
  have hCreg := A.offenseSuffixLang_isRegular hFin
  have hEq : (U : Language A.D) =
      (A.L : Language A.D) ⊓ A.offenseSuffixLang U := by
    change (U : Set _) = (A.L ∩ A.offenseSuffixLang U : Set _)
    exact A.offense_eq_L_inter_suffix hSub hb
  rw [hEq]
  exact hInter _ _ hL hCreg

end ActionSystem
end Actions
