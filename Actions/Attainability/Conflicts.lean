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
that there are exactly **113** such patterns.

The count comes in two layers:

* `conflictPattern_card` evaluates the factored sum over the `2^6 = 64`
  doubleton words by kernel `decide`;
* `card_conflictFamilies` states the result about actual families,
  `IsConflictFamily : Finset (Finset (Fin 4)) → Prop`, and reduces it to that
  sum by a structural bijection (a family corresponds to its doubletons
  together with a choice among the tripletons they permit).

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

/-! ## Conflict families as finsets of subsets of `Fin 4`

The factored count `conflictPatternCount` above is a number; this section says
what it counts. A conflict family is a `Finset (Finset (Fin 4))`, and
`card_conflictFamilies` shows there are exactly 113 of them, by a structural
bijection onto the doubleton × tripleton index set whose size is
`conflictPatternCount`. No enumeration of the `2 ^ 16` candidate families
takes place.
-/

/-- A *conflict family* on four labeled motives: a family of subsets of `Fin 4`
that is downward closed, contains every singleton, and omits the full four-set.

The empty set is a member of every conflict family. It is not listed as a
separate clause because it is forced: `∅ ⊆ {i}` and `{i}` is in the family
(`IsConflictFamily.empty_mem`). -/
def IsConflictFamily (F : Finset (Finset (Fin 4))) : Prop :=
  (∀ s ∈ F, ∀ t ⊆ s, t ∈ F) ∧ (∀ i : Fin 4, {i} ∈ F) ∧ Finset.univ ∉ F

instance IsConflictFamily.instDecidablePred : DecidablePred IsConflictFamily :=
  fun F => by unfold IsConflictFamily; infer_instance

namespace IsConflictFamily

variable {F : Finset (Finset (Fin 4))}

theorem mem_of_subset (hF : IsConflictFamily F) {s t : Finset (Fin 4)} (hs : s ∈ F)
    (hts : t ⊆ s) : t ∈ F :=
  hF.1 s hs t hts

theorem singleton_mem (hF : IsConflictFamily F) (i : Fin 4) : {i} ∈ F :=
  hF.2.1 i

theorem univ_notMem (hF : IsConflictFamily F) : Finset.univ ∉ F :=
  hF.2.2

/-- Every conflict family contains the empty set (downward closure below any
singleton). -/
theorem empty_mem (hF : IsConflictFamily F) : ∅ ∈ F :=
  hF.mem_of_subset (hF.singleton_mem 0) (Finset.empty_subset _)

/-- Members of a conflict family have at most three elements. -/
theorem card_lt_four (hF : IsConflictFamily F) {s : Finset (Fin 4)} (hs : s ∈ F) :
    s.card < 4 := by
  have hle : s.card ≤ 4 := by simpa using s.card_le_univ
  refine lt_of_le_of_ne hle fun h4 => hF.univ_notMem ?_
  have hs' : s = Finset.univ := Finset.eq_univ_of_card s (by simpa using h4)
  exact hs' ▸ hs

end IsConflictFamily

/-! ### Layers of the Boolean lattice on four atoms -/

/-- The six 2-subsets of `Fin 4`. -/
def pairSets : Finset (Finset (Fin 4)) :=
  Finset.powersetCard 2 Finset.univ

/-- The four 3-subsets of `Fin 4`. -/
def tripleSets : Finset (Finset (Fin 4)) :=
  Finset.powersetCard 3 Finset.univ

/-- The empty set and the four singletons: the part forced into every conflict
family. -/
def lowSets : Finset (Finset (Fin 4)) :=
  Finset.univ.filter fun s => s.card ≤ 1

/-- The tripletons that a doubleton family `D` permits: those all of whose
2-subsets lie in `D`. -/
def allowedTriples (D : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  tripleSets.filter fun t => ∀ p ∈ t.powersetCard 2, p ∈ D

/-- Build a family from a doubleton family `D` and a tripleton family `T`. -/
def assemble (D T : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  lowSets ∪ D ∪ T

/-- The doubletons of a family. -/
def pairPart (F : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  F.filter fun s => s.card = 2

/-- The tripletons of a family. -/
def triplePart (F : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  F.filter fun s => s.card = 3

theorem mem_pairSets {s : Finset (Fin 4)} : s ∈ pairSets ↔ s.card = 2 :=
  Finset.mem_powersetCard_univ

theorem mem_tripleSets {s : Finset (Fin 4)} : s ∈ tripleSets ↔ s.card = 3 :=
  Finset.mem_powersetCard_univ

theorem mem_allowedTriples {D : Finset (Finset (Fin 4))} {t : Finset (Fin 4)} :
    t ∈ allowedTriples D ↔ t.card = 3 ∧ ∀ p ⊆ t, p.card = 2 → p ∈ D := by
  simp [allowedTriples, mem_tripleSets, Finset.mem_powersetCard]

theorem mem_assemble {D T : Finset (Finset (Fin 4))} {s : Finset (Fin 4)} :
    s ∈ assemble D T ↔ s.card ≤ 1 ∨ s ∈ D ∨ s ∈ T := by
  simp [assemble, lowSets]

/-! ### The bijection `(D, T) ↦ assemble D T` -/

/-- Assembling a doubleton family with a permitted tripleton family gives a
conflict family. -/
theorem isConflictFamily_assemble {D T : Finset (Finset (Fin 4))} (hD : D ⊆ pairSets)
    (hT : T ⊆ allowedTriples D) : IsConflictFamily (assemble D T) := by
  have hD2 : ∀ s ∈ D, s.card = 2 := fun s hs => mem_pairSets.1 (hD hs)
  have hT3 : ∀ s ∈ T, s.card = 3 ∧ ∀ p ⊆ s, p.card = 2 → p ∈ D :=
    fun s hs => mem_allowedTriples.1 (hT hs)
  refine ⟨?_, ?_, ?_⟩
  · intro s hs t hts
    have hcard := Finset.card_le_card hts
    rw [mem_assemble] at hs ⊢
    rcases hs with hs | hs | hs
    · exact Or.inl (hcard.trans hs)
    · have h2 := hD2 s hs
      rcases Nat.lt_or_ge t.card 2 with hlt | hge
      · exact Or.inl (by omega)
      · have hts' : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
        exact Or.inr (Or.inl (hts' ▸ hs))
    · obtain ⟨h3, hp⟩ := hT3 s hs
      have hcases : t.card ≤ 1 ∨ t.card = 2 ∨ t.card = 3 := by omega
      rcases hcases with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hp t hts h))
      · have hts' : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
        exact Or.inr (Or.inr (hts' ▸ hs))
  · intro i
    exact mem_assemble.2 (Or.inl (by simp))
  · intro h
    rcases mem_assemble.1 h with h | h | h
    · simp at h
    · have h2 := hD2 _ h
      simp at h2
    · have h3 := (hT3 _ h).1
      simp at h3

theorem pairPart_subset (F : Finset (Finset (Fin 4))) : pairPart F ⊆ pairSets :=
  fun _ hs => mem_pairSets.2 (Finset.mem_filter.1 hs).2

/-- In a conflict family, every tripleton is permitted by the family's
doubletons. -/
theorem triplePart_subset {F : Finset (Finset (Fin 4))} (hF : IsConflictFamily F) :
    triplePart F ⊆ allowedTriples (pairPart F) := by
  intro t ht
  obtain ⟨htF, h3⟩ := Finset.mem_filter.1 ht
  exact mem_allowedTriples.2
    ⟨h3, fun p hp h2 => Finset.mem_filter.2 ⟨hF.mem_of_subset htF hp, h2⟩⟩

/-- A conflict family is recovered from its doubletons and tripletons. -/
theorem assemble_parts {F : Finset (Finset (Fin 4))} (hF : IsConflictFamily F) :
    assemble (pairPart F) (triplePart F) = F := by
  ext s
  simp only [mem_assemble, pairPart, triplePart, Finset.mem_filter]
  constructor
  · rintro (h | h | h)
    · rcases Nat.lt_or_ge s.card 1 with h0 | h1
      · have hs : s = ∅ := Finset.card_eq_zero.1 (by omega)
        exact hs ▸ hF.empty_mem
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (show s.card = 1 by omega)
        exact hF.singleton_mem i
    · exact h.1
    · exact h.1
  · intro hs
    have h4 := hF.card_lt_four hs
    have hcases : s.card ≤ 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
    rcases hcases with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hs, h⟩)
    · exact Or.inr (Or.inr ⟨hs, h⟩)

theorem pairPart_assemble {D T : Finset (Finset (Fin 4))} (hD : D ⊆ pairSets)
    (hT : T ⊆ allowedTriples D) : pairPart (assemble D T) = D := by
  ext s
  simp only [pairPart, Finset.mem_filter, mem_assemble]
  constructor
  · rintro ⟨h | h | h, h2⟩
    · omega
    · exact h
    · have h3 := (mem_allowedTriples.1 (hT h)).1
      omega
  · intro h
    exact ⟨Or.inr (Or.inl h), mem_pairSets.1 (hD h)⟩

theorem triplePart_assemble {D T : Finset (Finset (Fin 4))} (hD : D ⊆ pairSets)
    (hT : T ⊆ allowedTriples D) : triplePart (assemble D T) = T := by
  ext s
  simp only [triplePart, Finset.mem_filter, mem_assemble]
  constructor
  · rintro ⟨h | h | h, h3⟩
    · omega
    · have h2 := mem_pairSets.1 (hD h)
      omega
    · exact h
  · intro h
    exact ⟨Or.inr (Or.inr h), (mem_allowedTriples.1 (hT h)).1⟩

/-- **Structural count.** Conflict families are in bijection with pairs
`(D, T)` of a doubleton family `D` and a family `T` of tripletons permitted by
`D`; hence their number is the sum over `D` of `2 ^ (permitted tripletons)`. -/
theorem card_conflictFamilies_eq_sum :
    (Finset.univ.filter IsConflictFamily).card =
      ∑ D ∈ pairSets.powerset, 2 ^ (allowedTriples D).card := by
  have hbij : (pairSets.powerset.sigma fun D => (allowedTriples D).powerset).card =
      (Finset.univ.filter IsConflictFamily).card := by
    -- Membership in the two finsets is unfolded to its defining conditions
    -- before any hypothesis is introduced, so nothing ever evaluates them.
    refine Finset.card_nbij' (fun x => assemble x.1 x.2)
      (fun F => ⟨pairPart F, triplePart F⟩) ?_ ?_ ?_ ?_ <;>
      simp only [Set.MapsTo, Set.LeftInvOn, Set.RightInvOn, Finset.mem_coe,
        Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter, Finset.mem_univ,
        true_and]
    · exact fun x hx => isConflictFamily_assemble hx.1 hx.2
    · exact fun F hF => ⟨pairPart_subset F, triplePart_subset hF⟩
    · rintro ⟨D, T⟩ ⟨hD, hT⟩
      simp only [pairPart_assemble hD hT, triplePart_assemble hD hT]
    · exact fun F hF => assemble_parts hF
  rw [← hbij, Finset.card_sigma]
  simp [Finset.card_powerset]

/-! ### Matching the bitmask word encoding of `conflictPatternCount` -/

/-- The subset of `Fin 4` encoded by a 4-bit mask. -/
def ofMask (m : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter fun i => m.testBit i

/-- The doubleton family selected by a 6-bit doubleton word. -/
def pairsOfWord (w : ℕ) : Finset (Finset (Fin 4)) :=
  ((doubletons.filter (doubletonChosen w)).map ofMask).toFinset

/-- The six doubleton masks decode to exactly the 2-subsets. -/
theorem pairSets_eq : pairSets = (doubletons.map ofMask).toFinset := by
  decide

theorem nodup_doubletons_map : (doubletons.map ofMask).Nodup := by
  decide

/-- The four tripleton masks decode to exactly the 3-subsets. -/
theorem tripleSets_eq :
    tripleSets = (tripleRequirements.map fun r => ofMask r.1).toFinset := by
  decide

theorem nodup_tripleRequirements_map :
    (tripleRequirements.map fun r => ofMask r.1).Nodup := by
  decide

/-- Each entry of `tripleRequirements` lists exactly the 2-subsets of its
tripleton, and they are all doubleton masks. -/
theorem tripleRequirements_spec :
    ∀ r ∈ tripleRequirements,
      (ofMask r.1).powersetCard 2 = (r.2.map ofMask).toFinset ∧
        ∀ m ∈ r.2, m ∈ doubletons := by
  decide

theorem ofMask_mem_pairsOfWord {w m : ℕ} (hm : m ∈ doubletons) :
    ofMask m ∈ pairsOfWord w ↔ doubletonChosen w m = true := by
  simp only [pairsOfWord, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hc⟩, hEq⟩
    have ham : a = m := List.inj_on_of_nodup_map nodup_doubletons_map ha hm hEq
    exact ham ▸ hc
  · exact fun h => ⟨m, ⟨hm, h⟩, rfl⟩

theorem pairsOfWord_subset (w : ℕ) : pairsOfWord w ⊆ pairSets := by
  rw [pairSets_eq]
  intro s hs
  simp only [pairsOfWord, List.mem_toFinset, List.mem_map, List.mem_filter] at hs ⊢
  obtain ⟨a, ⟨ha, -⟩, rfl⟩ := hs
  exact ⟨a, ha, rfl⟩

/-- The tripletons permitted by the doubleton family of `w` are counted by
`allowedTripleCount w`. -/
theorem card_allowedTriples_pairsOfWord (w : ℕ) :
    (allowedTriples (pairsOfWord w)).card = allowedTripleCount w := by
  have key : allowedTriples (pairsOfWord w) =
      ((tripleRequirements.filter fun r => r.2.all (doubletonChosen w)).map
        fun r => ofMask r.1).toFinset := by
    ext t
    simp only [allowedTriples, tripleSets_eq, Finset.mem_filter, List.mem_toFinset,
      List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, h⟩
      obtain ⟨hpow, hdoub⟩ := tripleRequirements_spec r hr
      refine ⟨r, ⟨hr, List.all_eq_true.2 fun m hm => ?_⟩, rfl⟩
      refine (ofMask_mem_pairsOfWord (hdoub m hm)).1 (h _ ?_)
      rw [hpow]
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨m, hm, rfl⟩)
    · rintro ⟨r, ⟨hr, hall⟩, rfl⟩
      obtain ⟨hpow, hdoub⟩ := tripleRequirements_spec r hr
      refine ⟨⟨r, hr, rfl⟩, fun p hp => ?_⟩
      rw [hpow] at hp
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
      exact (ofMask_mem_pairsOfWord (hdoub m hm)).2 (List.all_eq_true.1 hall m hm)
  rw [key, List.toFinset_card_of_nodup
    (nodup_tripleRequirements_map.sublist (List.filter_sublist.map _)), List.length_map]
  rfl

/-- Bit `i` of a doubleton word is read off by the `i`-th doubleton mask. -/
theorem doubletonChosen_bit :
    ∀ i < 6, ∃ m ∈ doubletons, ∀ w, doubletonChosen w m = w.testBit i := by
  intro i hi
  interval_cases i
  · exact ⟨3, by decide, fun _ => rfl⟩
  · exact ⟨5, by decide, fun _ => rfl⟩
  · exact ⟨6, by decide, fun _ => rfl⟩
  · exact ⟨9, by decide, fun _ => rfl⟩
  · exact ⟨10, by decide, fun _ => rfl⟩
  · exact ⟨12, by decide, fun _ => rfl⟩

/-- Distinct doubleton words below `2 ^ 6` select distinct doubleton families. -/
theorem pairsOfWord_injOn : Set.InjOn pairsOfWord (Finset.range 64 : Set ℕ) := by
  intro w hw w' hw' h
  have hw6 : w < 2 ^ 6 := by simpa using hw
  have hw6' : w' < 2 ^ 6 := by simpa using hw'
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i 6 with hi | hi
  · obtain ⟨m, hm, hbit⟩ := doubletonChosen_bit i hi
    have hiff : doubletonChosen w m = true ↔ doubletonChosen w' m = true := by
      rw [← ofMask_mem_pairsOfWord hm, ← ofMask_mem_pairsOfWord hm, h]
    rw [← hbit w, ← hbit w']
    exact Bool.eq_iff_iff.2 hiff
  · have hpow : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    rw [Nat.testBit_lt_two_pow (hw6.trans_le hpow),
      Nat.testBit_lt_two_pow (hw6'.trans_le hpow)]

/-- The 64 doubleton words enumerate all doubleton families. -/
theorem image_pairsOfWord : (Finset.range 64).image pairsOfWord = pairSets.powerset := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.image_subset_iff.2 fun w _ => Finset.mem_powerset.2 (pairsOfWord_subset w)
  · rw [Finset.card_image_of_injOn pairsOfWord_injOn, Finset.card_powerset, pairSets,
      Finset.card_powersetCard]
    simp [Nat.choose]

/-- The structural sum over doubleton families is the factored bitmask count. -/
theorem sum_pairSets_powerset_eq :
    ∑ D ∈ pairSets.powerset, 2 ^ (allowedTriples D).card = conflictPatternCount := by
  rw [← image_pairsOfWord, Finset.sum_image pairsOfWord_injOn]
  simp only [card_allowedTriples_pairsOfWord]
  rw [← List.toFinset_range, List.sum_toFinset _ List.nodup_range]
  rfl

/-- The number of conflict families is the factored doubleton × tripleton
count. -/
theorem card_conflictFamilies_eq_conflictPatternCount :
    (Finset.univ.filter IsConflictFamily).card = conflictPatternCount := by
  rw [card_conflictFamilies_eq_sum, sum_pairSets_powerset_eq]

/-- **Nowakowska's 113.** There are exactly 113 conflict families on four
labeled motives: downward-closed families of subsets of `Fin 4` that contain
every singleton and omit the full set. The only numeric evaluation is the
64-term sum `conflictPattern_card`. -/
theorem card_conflictFamilies : (Finset.univ.filter IsConflictFamily).card = 113 := by
  rw [card_conflictFamilies_eq_conflictPatternCount, conflictPattern_card]

end Conflicts
end Actions
