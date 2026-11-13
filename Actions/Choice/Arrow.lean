/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Tactic

@[expose] public section

/-!
# Arrow’s theorem and clinical corollaries (§5)

Nowakowska (1982), pp. 152–156. Thin formalization of total preorders, Arrow
postulates on 2 motivational scales / 3 options, named clinical failure modes,
and the dictatorial-core inconsistency used in her §5 reading.

Clinical names are interpretive library packaging, not new psychology theorems.
-/

namespace Actions
namespace Arrow

structure TotalPreorder (α : Type*) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a

namespace TotalPreorder
variable {α : Type*} (p : TotalPreorder α)
def lt (a b : α) : Prop := p.le a b ∧ ¬ p.le b a
end TotalPreorder

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

def ArrowPostulates2 (F : SWF2) : Prop :=
  LackOfDictator F ∧ Unanimity F ∧ IIA F ∧ Sovereignty F

def CompulsiveOrHedonistic (F : SWF2) : Prop := ∃ i, IsDictator F i
def BlindObedience (F : SWF2) : Prop := ¬ Sovereignty F
def NeuroticAllOrNothing (F : SWF2) : Prop := ¬ IIA F

theorem compulsive_of_not_lack {F : SWF2} (h : ¬ LackOfDictator F) :
    CompulsiveOrHedonistic F := by
  unfold LackOfDictator at h
  push Not at h
  exact h

theorem blind_of_not_sovereignty {F : SWF2} (h : ¬ Sovereignty F) :
    BlindObedience F := h

theorem neurotic_of_not_IIA {F : SWF2} (h : ¬ IIA F) :
    NeuroticAllOrNothing F := h

def scale1Dictator : SWF2 := fun π => π.1
def scale2Dictator : SWF2 := fun π => π.2

theorem scale1_isDictator : IsDictator scale1Dictator 0 := fun _ _ _ h => h
theorem scale2_isDictator : IsDictator scale2Dictator 1 := fun _ _ _ h => h

theorem scale1_unanimity : Unanimity scale1Dictator := fun _ _ _ h₁ _ => h₁
theorem scale2_unanimity : Unanimity scale2Dictator := fun _ _ _ _ h₂ => h₂

theorem scale1_IIA : IIA scale1Dictator := by
  intro π π' a b h1 _ _ _
  simpa [scale1Dictator, rankingPreorder] using h1

theorem scale2_IIA : IIA scale2Dictator := by
  intro π π' a b _ _ h2 _
  simpa [scale2Dictator, rankingPreorder] using h2

theorem scale1_not_lack : ¬ LackOfDictator scale1Dictator := fun h =>
  h 0 scale1_isDictator

theorem scale2_not_lack : ¬ LackOfDictator scale2Dictator := fun h =>
  h 1 scale2_isDictator

theorem scale1_compulsive : CompulsiveOrHedonistic scale1Dictator :=
  ⟨0, scale1_isDictator⟩

theorem scale2_compulsive : CompulsiveOrHedonistic scale2Dictator :=
  ⟨1, scale2_isDictator⟩

/-- Pairwise ranking with `a` best, `b` second, other option last. -/
def prefer (a b : Fin 3) : Ranking3 := fun x =>
  if x = a then (0 : Fin 3) else if x = b then (1 : Fin 3) else (2 : Fin 3)

theorem prefer_lt {a b : Fin 3} (hne : a ≠ b) :
    (rankingPreorder (prefer a b)).lt a b := by
  dsimp [TotalPreorder.lt, rankingPreorder, prefer]
  simp [Ne.symm hne]

theorem scale1_sovereignty : Sovereignty scale1Dictator := by
  intro a b hne
  constructor
  · exact ⟨(prefer a b, prefer a b), by simpa [scale1Dictator] using prefer_lt hne⟩
  · exact ⟨(prefer b a, prefer b a), by simpa [scale1Dictator] using prefer_lt (Ne.symm hne)⟩

theorem scale2_sovereignty : Sovereignty scale2Dictator := by
  intro a b hne
  constructor
  · exact ⟨(prefer a b, prefer a b), by simpa [scale2Dictator] using prefer_lt hne⟩
  · exact ⟨(prefer b a, prefer b a), by simpa [scale2Dictator] using prefer_lt (Ne.symm hne)⟩

/-- Dictatorship violates the Arrow bundle via postulate (1). -/
theorem not_arrowPostulates_of_dictator {F : SWF2} {i : Fin 2}
    (h : IsDictator F i) : ¬ ArrowPostulates2 F := by
  rintro ⟨hLack, _, _, _⟩
  exact hLack i h

/-- **Compared claim (dictatorial core):** the pure scale dictators — the
§5 compulsive/hedonistic solutions — do not satisfy `ArrowPostulates2`. -/
theorem arrow_impossibility_dictatorial_core :
    ¬ ArrowPostulates2 scale1Dictator ∧ ¬ ArrowPostulates2 scale2Dictator :=
  ⟨not_arrowPostulates_of_dictator scale1_isDictator,
    not_arrowPostulates_of_dictator scale2_isDictator⟩

/-- Clinical packaging of postulate (1) failure. -/
theorem compulsive_of_dictator {F : SWF2} {i : Fin 2} (h : IsDictator F i) :
    CompulsiveOrHedonistic F := ⟨i, h⟩

end Arrow
end Actions
