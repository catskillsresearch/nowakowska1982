/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Tactic

@[expose] public section

/-!
# Taxonomy of four-motive conflicts

Nowakowska (1982), §4, pp. 150–151: when four labeled motives are not jointly
strongly attainable, conflict types are the patterns of which subsets *are*
strongly attainable. Strong attainability is downward closed, so a pattern is an
order ideal (downset) in the Boolean lattice on four atoms that

* contains every singleton (each motive is individually attainable), and
* does not contain the full four-set.

This file machine-checks that there are exactly **113** such patterns (labeled;
no quotient by \(S_4\)). The count is a **novel Palomar compared claim**: the
paper states 113 without exhibiting the enumeration.
-/

namespace Actions
namespace Conflicts

/-- Bitmask encoding of a family of subsets (bit `s` ↔ subset mask `s` is in). -/
abbrev FamMask := ℕ

/-- Subset-mask `i` is ⊆ subset-mask `j`. -/
def subMaskLe (i j : ℕ) : Bool :=
  (i &&& j) == i

/-- Family `mask` is a downset in the power set of four motives. -/
def isDownset (mask : FamMask) : Bool :=
  (List.range 16).all fun j =>
    !mask.testBit j ||
      (List.range 16).all fun i =>
        !(subMaskLe i j) || mask.testBit i

/-- Every singleton motive-set is marked attainable. -/
def hasAllAtoms (mask : FamMask) : Bool :=
  mask.testBit 1 && mask.testBit 2 && mask.testBit 4 && mask.testBit 8

/-- The full four-motive set is marked attainable. -/
def hasTop (mask : FamMask) : Bool :=
  mask.testBit 15

/-- Nowakowska four-motive conflict pattern (labeled). -/
def isConflictPattern (mask : FamMask) : Bool :=
  isDownset mask && hasAllAtoms mask && !hasTop mask

/-- All bit families on 16 subsets: `0 … 2¹⁶ - 1`. -/
def allFamMasks : List FamMask :=
  List.range (2 ^ 16)

/-- Conflict patterns among all `2¹⁶` candidate families. -/
def conflictPatterns : List FamMask :=
  allFamMasks.filter isConflictPattern

/-- **Novel compared claim:** there are exactly 113 labeled four-motive conflict
patterns in the downset model of §4. -/
theorem conflictPattern_card : conflictPatterns.length = 113 := by
  native_decide

/-- Convenience: the Boolean recognizer decides membership. -/
theorem isConflictPattern_decide (mask : FamMask) :
    isConflictPattern mask = true ∨ isConflictPattern mask = false := by
  cases isConflictPattern mask <;> simp

end Conflicts
end Actions
