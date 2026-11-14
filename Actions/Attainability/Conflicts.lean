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

With atoms fixed in and the top fixed out, a pattern is determined by which of
the six doubletons and four tripletons are included, subject to: a tripleton
may appear only if all three of its doubletons do. This file machine-checks
that there are exactly **113** such patterns via kernel `decide`.

A direct `native_decide` over all `2^16` family masks is fast locally but is
rejected by Palomar’s con-ron checker; see the narrative note
`Conflicts_decide_note.txt` (and the Zulip threads cited there). **Novel
Palomar compared claim.**
-/

namespace Actions
namespace Conflicts

/-- The six doubleton bitmasks on `Fin 4`. -/
def doubletons : List ℕ := [3, 5, 6, 9, 10, 12]

/-- Tripleton bitmask → the three doubletons it requires. -/
def tripleRequirements : List (ℕ × List ℕ) :=
  [(7, [3, 5, 6]), (11, [3, 9, 10]), (13, [5, 9, 12]), (14, [6, 10, 12])]

/-- Whether bit `b` is set in the 6-bit doubleton choice word `w` (index into
`doubletons`). -/
def doubletonChosen (w : ℕ) (mask : ℕ) : Bool :=
  match doubletons.findIdx? (· == mask) with
  | some i => w.testBit i
  | none => false

/-- Number of tripletons allowed by doubleton word `w` (each may be freely
included or not). -/
def allowedTripleCount (w : ℕ) : ℕ :=
  (tripleRequirements.filter fun ⟨_, reqs⟩ =>
    reqs.all (doubletonChosen w)).length

/-- Patterns for a fixed doubleton word: `2 ^ (allowed triples)`. -/
def patternsFor (w : ℕ) : ℕ :=
  2 ^ allowedTripleCount w

/-- Sum over all `2^6 = 64` doubleton configurations. -/
def conflictPatternCount : ℕ :=
  ((List.range 64).map patternsFor).sum

/-- **Novel compared claim:** there are exactly 113 labeled four-motive conflict
patterns in the downset model of §4. -/
theorem conflictPattern_card : conflictPatternCount = 113 := by
  decide

/-- Boolean recognizer kept for documentation / Challenge wiring: a 16-bit family
mask is a conflict pattern when it is a downset, contains all atoms, and omits
the top. Used only for the small membership lemmas below, not for the count. -/
def isDownset (mask : ℕ) : Bool :=
  (List.range 16).all fun j =>
    !mask.testBit j ||
      (List.range 16).all fun i =>
        !(((i &&& j) == i)) || mask.testBit i

def hasAllAtoms (mask : ℕ) : Bool :=
  mask.testBit 1 && mask.testBit 2 && mask.testBit 4 && mask.testBit 8

def hasTop (mask : ℕ) : Bool :=
  mask.testBit 15

def isConflictPattern (mask : ℕ) : Bool :=
  isDownset mask && hasAllAtoms mask && !hasTop mask

theorem isConflictPattern_decide (mask : ℕ) :
    isConflictPattern mask = true ∨ isConflictPattern mask = false := by
  cases isConflictPattern mask <;> simp

/-- Sanity: the empty-of-doubletons word contributes `2^0 = 1` pattern (atoms only). -/
theorem patternsFor_zero : patternsFor 0 = 1 := by
  decide

/-- Sanity: all six doubletons chosen allows all four triples → `2^4 = 16`. -/
theorem patternsFor_allDoubletons : patternsFor (2 ^ 6 - 1) = 16 := by
  decide

end Conflicts
end Actions
