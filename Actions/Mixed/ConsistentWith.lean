/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Mixed.MixedSystem
import Mathlib.Tactic

@[expose] public section

/-!
# Consistency of an action string with an utterance pair (§5.3.5)

The paper requires a split `x = uv` with `φ(u) = k`. Here the split is
existential and `k` is carried by the pair; exact duration matching is left
to instances where `φ` is discrete.
-/

namespace Actions
namespace MixedSystem

variable (S : MixedSystem)

/-- Utterance index set `Λ = M × ℕ`. -/
abbrev Lambda := S.M × ℕ

/-- Action string `x ∈ L` is consistent with `(α, k)` (1973 §5.3.5). -/
def ConsistentWith (x : List S.D) (αk : S.Lambda) : Prop :=
  x ∈ S.base.L ∧
    (S.W αk.1 αk.2 = ∅ ∨ x ∈ S.base.RinvWanted (S.W αk.1 αk.2)) ∧
    (S.W' αk.1 αk.2 = ∅ ∨ x ∉ S.base.RinvUnwanted (S.W' αk.1 αk.2)) ∧
    ∃ u v : List S.D, x = u ++ v ∧
      (S.O αk.1 αk.2 = ∅ ∨ v ∈ S.O αk.1 αk.2) ∧
      (S.O' αk.1 αk.2 = ∅ ∨ v ∉ S.O' αk.1 αk.2)

/-- Consistency with respect to a set `A ⊆ Λ`. -/
def ConsistentWithSet (x : List S.D) (A : Set S.Lambda) : Prop :=
  ∀ αk ∈ A, S.ConsistentWith x αk

end MixedSystem
end Actions
