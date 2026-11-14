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
dictatorial-core claim live in `ArrowPostulates2`.
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

end Arrow
end Actions
