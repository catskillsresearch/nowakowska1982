/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.ActionSystem
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic

@[expose] public section

/-!
# Minimum elementary duration
-/

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

noncomputable def minφ [Fintype A.D] [Nonempty A.D] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty A.φ

namespace minφ
theorem pos [Fintype A.D] [Nonempty A.D] : 0 < A.minφ := by
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty A.φ
  simpa [minφ, hd] using A.φ_pos d
end minφ

end ActionSystem
end Actions
