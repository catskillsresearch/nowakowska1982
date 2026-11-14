/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Tactic

@[expose] public section

/-!
# Total preorders

Total preorders used by the §5 Arrow reading (Nowakowska 1982, pp. 152–156).
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

end Arrow
end Actions
