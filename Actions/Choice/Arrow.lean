/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Choice.TotalPreorder
public import Mathlib.Tactic

@[expose] public section

/-!
# Arrow’s theorem (§5 postulates) — SWF building blocks

Nowakowska (1982), pp. 152–156. Rankings, dictators, and the four individual
postulates on 2 motivational scales / 3 options. The packaged conjunction and
the impossibility statement live in `ArrowPostulates2`.

## Dictator theorem in this encoding

`arrow_dictator_of_unanimity_IIA` is the standard Arrow impossibility argument,
specialised to this finite 2×3 encoding (two scales, three options, rankings
given by `Fin 3` scores, ties allowed). It is not a new result: it is the
textbook decisive-coalition proof, written out for two voters.

* `Decisive1 F a b`: scale 1 forces `a` strictly below `b` whenever the two
  scales strictly disagree on that pair.
* `Decisive1.spread`: decisiveness on one pair spreads to the adjacent pairs
  (unanimity + IIA + transitivity of the social scores).
* `Decisive1.all`: hence to every pair of distinct options.
* `Decisive1.isDictator`: decisive on every pair ⇒ dictator, including the
  case where the other scale is indifferent.
* `arrow_dictator_of_unanimity_IIA`: one reference profile (`0 < 1 < 2` against
  `1 < 2 < 0`) makes one of the two scales decisive on some pair.

The domain is all of `Ranking3` (no injectivity restriction). An SWF may in
principle depend on scores rather than on the induced preorders; `IIA` rules
that out, so no restriction is needed.
-/

namespace Actions
namespace Arrow

abbrev Ranking3 := Fin 3 → Fin 3

def rankingPreorder (r : Ranking3) : TotalPreorder (Fin 3) where
  le a b := r a ≤ r b
  refl _ := le_rfl
  trans h₁ h₂ := le_trans h₁ h₂
  total a b := le_total (r a) (r b)

abbrev Profile2 := Ranking3 × Ranking3
abbrev SWF2 := Profile2 → Ranking3

def IsDictator (F : SWF2) : Fin 2 → Prop
  | ⟨0, _⟩ => ∀ π a b, (rankingPreorder π.1).lt a b → (rankingPreorder (F π)).lt a b
  | ⟨1, _⟩ => ∀ π a b, (rankingPreorder π.2).lt a b → (rankingPreorder (F π)).lt a b

def LackOfDictator (F : SWF2) : Prop := ∀ i, ¬ IsDictator F i

def Unanimity (F : SWF2) : Prop :=
  ∀ π a b,
    (rankingPreorder π.1).lt a b → (rankingPreorder π.2).lt a b →
      (rankingPreorder (F π)).lt a b

def IIA (F : SWF2) : Prop :=
  ∀ π π' a b,
    ((rankingPreorder π.1).le a b ↔ (rankingPreorder π'.1).le a b) →
    ((rankingPreorder π.1).le b a ↔ (rankingPreorder π'.1).le b a) →
    ((rankingPreorder π.2).le a b ↔ (rankingPreorder π'.2).le a b) →
    ((rankingPreorder π.2).le b a ↔ (rankingPreorder π'.2).le b a) →
      ((rankingPreorder (F π)).le a b ↔ (rankingPreorder (F π')).le a b)

def Sovereignty (F : SWF2) : Prop :=
  ∀ a b : Fin 3, a ≠ b →
    (∃ π, (rankingPreorder (F π)).lt a b) ∧
    (∃ π, (rankingPreorder (F π)).lt b a)

/-! ### Score-level restatements -/

theorem rankingPreorder_lt_iff {r : Ranking3} {a b : Fin 3} :
    (rankingPreorder r).lt a b ↔ r a < r b :=
  ⟨fun h => not_le.1 h.2, fun h => ⟨h.le, not_le.2 h⟩⟩

/-- Any two options of `Fin 3` miss a third one. -/
theorem exists_third (a b : Fin 3) : ∃ c, a ≠ c ∧ b ≠ c := by
  decide +revert

/-- Three pairwise distinct options exhaust `Fin 3`. -/
theorem eq_or_eq_or_eq {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (z : Fin 3) : z = a ∨ z = b ∨ z = c := by
  decide +revert

/-- `IIA` transfers strict social comparisons between two profiles that agree,
scale by scale, on the pair `a`, `b`. -/
theorem IIA.lt_congr {F : SWF2} (hI : IIA F) {π π' : Profile2} {a b : Fin 3}
    (h1 : π.1 a ≤ π.1 b ↔ π'.1 a ≤ π'.1 b) (h1' : π.1 b ≤ π.1 a ↔ π'.1 b ≤ π'.1 a)
    (h2 : π.2 a ≤ π.2 b ↔ π'.2 a ≤ π'.2 b) (h2' : π.2 b ≤ π.2 a ↔ π'.2 b ≤ π'.2 a) :
    F π a < F π b ↔ F π' a < F π' b := by
  have hba : F π b ≤ F π a ↔ F π' b ≤ F π' a := hI π π' b a h1' h1 h2' h2
  rw [← not_le, ← not_le, hba]

theorem Unanimity.lt {F : SWF2} (hU : Unanimity F) {π : Profile2} {a b : Fin 3}
    (h1 : π.1 a < π.1 b) (h2 : π.2 a < π.2 b) : F π a < F π b :=
  rankingPreorder_lt_iff.1
    (hU π a b (rankingPreorder_lt_iff.2 h1) (rankingPreorder_lt_iff.2 h2))

/-! ### Explicit rankings and the scale swap -/

/-- Ranking with scores `a ↦ p`, `b ↦ q`, and the remaining option `↦ s`. -/
def rank3 (a b : Fin 3) (p q s : Fin 3) : Ranking3 := fun x =>
  if x = a then p else if x = b then q else s

namespace rank3
variable {a b c p q s : Fin 3}

@[simp] theorem apply_fst : rank3 a b p q s a = p := by simp [rank3]

theorem apply_snd (hab : a ≠ b) : rank3 a b p q s b = q := by
  simp [rank3, hab.symm]

theorem apply_thd (hac : a ≠ c) (hbc : b ≠ c) : rank3 a b p q s c = s := by
  simp [rank3, hac.symm, hbc.symm]
end rank3

/-- The same SWF with the two scales exchanged. -/
def swapSWF (F : SWF2) : SWF2 := fun π => F (π.2, π.1)

namespace swapSWF
variable {F : SWF2}

theorem unanimity (hU : Unanimity F) : Unanimity (swapSWF F) :=
  fun π a b h1 h2 => hU (π.2, π.1) a b h2 h1

theorem IIA (hI : IIA F) : Arrow.IIA (swapSWF F) :=
  fun π π' a b h1 h1' h2 h2' => hI (π.2, π.1) (π'.2, π'.1) a b h2 h2' h1 h1'

theorem isDictator_one (h : IsDictator (swapSWF F) 0) : IsDictator F 1 :=
  fun π a b hlt => h (π.2, π.1) a b hlt
end swapSWF

/-! ### Decisiveness -/

/-- Scale 1 is *decisive* for `a` over `b`: whenever scale 1 ranks `a` strictly
below `b` and scale 2 ranks `b` strictly below `a`, the SWF follows scale 1. -/
def Decisive1 (F : SWF2) (a b : Fin 3) : Prop :=
  ∀ π : Profile2, π.1 a < π.1 b → π.2 b < π.2 a → F π a < F π b

namespace Decisive1
variable {F : SWF2}

/-- A single profile with strict disagreement on `a`, `b` in which the SWF
follows scale 1 already gives decisiveness, by `IIA`. -/
theorem of_profile (hI : IIA F) {π₀ : Profile2} {a b : Fin 3}
    (h1 : π₀.1 a < π₀.1 b) (h2 : π₀.2 b < π₀.2 a) (h : F π₀ a < F π₀ b) :
    Decisive1 F a b := fun π g1 g2 =>
  (hI.lt_congr (by simp [g1.le, h1.le]) (by simp [g1.not_ge, h1.not_ge])
    (by simp [g2.not_ge, h2.not_ge]) (by simp [g2.le, h2.le])).2 h

/-- Contagion: decisiveness for `a` over `b` spreads to `a` over `c` and to
`c` over `b`, for the third option `c`. -/
theorem spread (hU : Unanimity F) (hI : IIA F) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hD : Decisive1 F a b) :
    Decisive1 F a c ∧ Decisive1 F c b := by
  constructor
  · -- scale 1: `a < b < c`; scale 2: `b < c < a`
    have e1 : ∀ p q s, rank3 a b p q s b = q := fun _ _ _ => rank3.apply_snd hab
    have e2 : ∀ p q s, rank3 a b p q s c = s := fun _ _ _ => rank3.apply_thd hac hbc
    let π' : Profile2 := (rank3 a b 0 1 2, rank3 a b 2 0 1)
    have hab' : F π' a < F π' b := hD π' (by simp [π', e1]) (by simp [π', e1])
    have hbc' : F π' b < F π' c := hU.lt (by simp [π', e1, e2]) (by simp [π', e1, e2])
    exact of_profile hI (π₀ := π') (by simp [π', e2]) (by simp [π', e2])
      (hab'.trans hbc')
  · -- scale 1: `c < a < b`; scale 2: `b < c < a`
    have e1 : ∀ p q s, rank3 a b p q s b = q := fun _ _ _ => rank3.apply_snd hab
    have e2 : ∀ p q s, rank3 a b p q s c = s := fun _ _ _ => rank3.apply_thd hac hbc
    let π' : Profile2 := (rank3 a b 1 2 0, rank3 a b 2 0 1)
    have hab' : F π' a < F π' b := hD π' (by simp [π', e1]) (by simp [π', e1])
    have hca' : F π' c < F π' a := hU.lt (by simp [π', e2]) (by simp [π', e2])
    exact of_profile hI (π₀ := π') (by simp [π', e1, e2]) (by simp [π', e1, e2])
      (hca'.trans hab')

/-- Decisiveness on one pair of distinct options gives decisiveness on all. -/
theorem all (hU : Unanimity F) (hI : IIA F) {a b : Fin 3} (hab : a ≠ b)
    (hD : Decisive1 F a b) : ∀ x y : Fin 3, x ≠ y → Decisive1 F x y := by
  obtain ⟨c, hac, hbc⟩ := exists_third a b
  obtain ⟨Dac, Dcb⟩ := spread hU hI hab hac hbc hD
  obtain ⟨-, Dbc⟩ := spread hU hI hac hab hbc.symm Dac
  obtain ⟨Dca, -⟩ := spread hU hI hbc.symm hac.symm hab.symm Dcb
  obtain ⟨Dba, -⟩ := spread hU hI hbc hab.symm hac.symm Dbc
  intro x y hxy
  have cover := eq_or_eq_or_eq hab hac hbc
  rcases cover x with rfl | rfl | rfl <;> rcases cover y with rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | assumption

/-- Decisive on every pair ⇒ dictator: scale 1's strict comparisons are
followed whatever scale 2 says, including indifference. -/
theorem isDictator (hU : Unanimity F) (hI : IIA F)
    (hD : ∀ x y : Fin 3, x ≠ y → Decisive1 F x y) : IsDictator F 0 := by
  change ∀ π a b, (rankingPreorder π.1).lt a b → (rankingPreorder (F π)).lt a b
  intro π a b h
  rw [rankingPreorder_lt_iff] at h ⊢
  have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
  rcases lt_trichotomy (π.2 a) (π.2 b) with h2 | h2 | h2
  · exact hU.lt h h2
  · -- scale 2 indifferent: route through the third option `c`
    obtain ⟨c, hac, hbc⟩ := exists_third a b
    -- scale 1: `a < c < b`; scale 2: `c < a ~ b`
    have e1 : ∀ p q s, rank3 a c p q s c = q := fun _ _ _ => rank3.apply_snd hac
    have e2 : ∀ p q s, rank3 a c p q s b = s := fun _ _ _ =>
      rank3.apply_thd hab hbc.symm
    let π' : Profile2 := (rank3 a c 0 1 2, rank3 a c 1 0 1)
    have hac' : F π' a < F π' c := hD a c hac π' (by simp [π', e1]) (by simp [π', e1])
    have hcb' : F π' c < F π' b := hU.lt (by simp [π', e1, e2]) (by simp [π', e1, e2])
    exact (hI.lt_congr (π' := π') (by simp [π', e2, h.le]) (by simp [π', e2, h.not_ge])
      (by simp [π', e2, h2]) (by simp [π', e2, h2])).2 (hac'.trans hcb')
  · exact hD a b hab π h h2
end Decisive1

/-- **Arrow's dictator theorem, 2 scales × 3 options.** Standard impossibility
argument in this finite encoding: any SWF on `Ranking3 × Ranking3` satisfying
`Unanimity` and `IIA` has a dictating scale. Holds on all of `Ranking3`,
ties included. -/
theorem arrow_dictator_of_unanimity_IIA (F : SWF2) :
    Unanimity F → IIA F → ∃ i : Fin 2, IsDictator F i := by
  intro hU hI
  -- reference profile — scale 1: `0 < 1 < 2`; scale 2: `1 < 2 < 0`
  let π₀ : Profile2 := (rank3 0 1 0 1 2, rank3 0 1 2 0 1)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  rcases lt_trichotomy (F π₀ 0) (F π₀ 1) with h | h | h
  · -- society follows scale 1 on `0`, `1`
    have hD : Decisive1 F 0 1 :=
      Decisive1.of_profile hI (π₀ := π₀) (by simp [π₀, rank3]) (by simp [π₀, rank3]) h
    exact ⟨0, Decisive1.isDictator hU hI (Decisive1.all hU hI h01 hD)⟩
  · -- social tie on `0`, `1`; unanimity gives `1 < 2`, hence `0 < 2` socially
    have h12 : F π₀ 1 < F π₀ 2 := hU.lt (by simp [π₀, rank3]) (by simp [π₀, rank3])
    have hD : Decisive1 F 0 2 :=
      Decisive1.of_profile hI (π₀ := π₀) (by simp [π₀, rank3]) (by simp [π₀, rank3])
        (h ▸ h12)
    exact ⟨0, Decisive1.isDictator hU hI (Decisive1.all hU hI h02 hD)⟩
  · -- society follows scale 2 on `0`, `1`: swap the scales
    have hD : Decisive1 (swapSWF F) 1 0 :=
      Decisive1.of_profile (swapSWF.IIA hI) (π₀ := (π₀.2, π₀.1))
        (by simp [π₀, rank3]) (by simp [π₀, rank3]) h
    exact ⟨1, swapSWF.isDictator_one (Decisive1.isDictator (swapSWF.unanimity hU)
      (swapSWF.IIA hI) (Decisive1.all (swapSWF.unanimity hU) (swapSWF.IIA hI) h01.symm hD))⟩

end Arrow
end Actions
