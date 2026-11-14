/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Choice.Arrow
import Mathlib.Tactic

@[expose] public section

/-!
# Pairwise prefer rankings for sovereignty witnesses
-/

namespace Actions
namespace Arrow

/-- Pairwise ranking with `a` best, `b` second, other option last. -/
def prefer (a b : Fin 3) : Ranking3 := fun x =>
  if x = a then (0 : Fin 3) else if x = b then (1 : Fin 3) else (2 : Fin 3)

namespace prefer
theorem lt {a b : Fin 3} (hne : a ≠ b) :
    (rankingPreorder (prefer a b)).lt a b := by
  dsimp [TotalPreorder.lt, rankingPreorder, prefer]
  simp [Ne.symm hne]
end prefer

end Arrow
end Actions
