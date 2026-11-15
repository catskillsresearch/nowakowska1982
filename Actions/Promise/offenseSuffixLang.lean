/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Actions.Promise.HatU
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.List.DropRight
import Mathlib.Tactic

@[expose] public section

/-!
# Regular infix envelope of factor-minimal \(\hat U\)

`offenseSuffixLang U` is the set of strings containing some factor-minimal
first offense `v ∈ HatU U` as a contiguous infix. (The name is historical:
before `HatU` became factor-minimal the envelope was a suffix extension.)

Under a finite offense horizon `HatU U` is finite, so the envelope is a finite
union of languages `containsInfix v`, each of which has finitely many left
quotients and is therefore regular by Myhill–Nerode.
-/

open scoped Computability

namespace Actions
namespace ActionSystem

variable (A : ActionSystem)

/-- Infix envelope of first offenses (historical name `offenseSuffixLang`). -/
def offenseSuffixLang (U : Set (List A.D)) : Language A.D :=
  { x | ∃ pref v suff, v ∈ A.HatU U ∧ x = pref ++ v ++ suff }

/-- Descriptive alias for `offenseSuffixLang`. -/
abbrev offenseInfixLang (U : Set (List A.D)) : Language A.D :=
  A.offenseSuffixLang U

namespace offenseSuffixLang

/-! ### Strings containing one fixed infix -/

/-- Strings containing a fixed list `v` as a contiguous infix. -/
def containsInfix (v : List A.D) : Language A.D :=
  { x | ∃ a b : List A.D, x = a ++ v ++ b }

theorem mem_containsInfix {v x : List A.D} :
    x ∈ containsInfix A v ↔ ∃ a b : List A.D, x = a ++ v ++ b := Iff.rfl

/-- Containing `v` is preserved by extending on either side. -/
theorem containsInfix_append {v x : List A.D}
    (hx : x ∈ containsInfix A v) (y z : List A.D) :
    y ++ x ++ z ∈ containsInfix A v := by
  rcases hx with ⟨a, b, rfl⟩
  exact ⟨y ++ a, b ++ z, by simp [List.append_assoc]⟩

private theorem rdrop_append_rtake (x : List A.D) (n : ℕ) :
    x.rdrop n ++ x.rtake n = x :=
  List.take_append_drop _ _

private theorem length_rtake_le (x : List A.D) (n : ℕ) :
    (x.rtake n).length ≤ n := by
  simp only [List.rtake, List.length_drop]
  omega

/-- Key lemma: if `x` does not yet contain `v`, then whether `x ++ y` contains
`v` depends only on the last `|v|` letters of `x`. -/
theorem append_mem_containsInfix_iff_rtake {v x : List A.D}
    (hx : x ∉ containsInfix A v) (y : List A.D) :
    x ++ y ∈ containsInfix A v ↔
      x.rtake v.length ++ y ∈ containsInfix A v := by
  constructor
  · rintro ⟨a, b, hab⟩
    rw [List.append_assoc] at hab
    -- Compare the cut `x | y` with the cut `a | v ++ b`.
    rcases List.append_eq_append_iff.mp hab with ⟨a', rfl, rfl⟩ | ⟨c, rfl, hc⟩
    · -- The occurrence of `v` starts at or after the end of `x`.
      exact ⟨x.rtake v.length ++ a', b, by simp [List.append_assoc]⟩
    · -- The occurrence starts inside `x = a ++ c`; compare `v | b` with `c | y`.
      rcases List.append_eq_append_iff.mp hc with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      · -- It also ends inside `x`, contradicting `hx`.
        exact (hx ⟨a, e, by simp [List.append_assoc]⟩).elim
      · -- It straddles the cut: `v = c ++ e`, and `c` is a suffix of `x` of
        -- length at most `|v|`, so it survives in `x.rtake |v|`.
        have hrtake : (a ++ c).rtake (c ++ e).length =
            a.drop (a.length - e.length) ++ c := by
          have hlen : (a ++ c).length - (c ++ e).length =
              a.length - e.length := by
            simp only [List.length_append]
            omega
          rw [List.rtake, hlen, List.drop_append_of_le_length (by omega)]
        exact ⟨a.drop (a.length - e.length), b, by
          rw [hrtake]; simp [List.append_assoc]⟩
  · intro h
    have h' := containsInfix_append A h (x.rdrop v.length) []
    rwa [List.append_nil, ← List.append_assoc, rdrop_append_rtake] at h'

/-- Once `x` contains `v`, every continuation does. -/
theorem leftQuotient_eq_top {v x : List A.D} (hx : x ∈ containsInfix A v) :
    (containsInfix A v).leftQuotient x = ⊤ := by
  ext y
  constructor
  · intro _; trivial
  · intro _
    have h := containsInfix_append A hx [] y
    rw [List.nil_append] at h
    exact (Language.mem_leftQuotient x y).mpr h

/-- If `x` does not contain `v`, its left quotient agrees with that of its
last `|v|` letters. -/
theorem leftQuotient_eq_rtake {v x : List A.D} (hx : x ∉ containsInfix A v) :
    (containsInfix A v).leftQuotient x =
      (containsInfix A v).leftQuotient (x.rtake v.length) := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_leftQuotient]
  exact append_mem_containsInfix_iff_rtake A hx y

/-- `containsInfix v` is regular: its left quotients are `⊤` or the quotient by
one of the finitely many strings of length at most `|v|`. -/
theorem containsInfix_isRegular [Finite A.D] (v : List A.D) :
    (containsInfix A v).IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  have hBound : { w : List A.D | w.length ≤ v.length }.Finite :=
    List.finite_length_le A.D v.length
  refine ((Set.finite_singleton (⊤ : Language A.D)).union
    (hBound.image (containsInfix A v).leftQuotient)).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ containsInfix A v
  · exact Or.inl (leftQuotient_eq_top A hx)
  · exact Or.inr ⟨x.rtake v.length, length_rtake_le A x v.length,
      (leftQuotient_eq_rtake A hx).symm⟩

/-! ### Finite unions of infix languages -/

/-- Strings containing some member of `s` as a contiguous infix. -/
def infixUnion (s : Set (List A.D)) : Language A.D :=
  { x | ∃ v ∈ s, x ∈ containsInfix A v }

theorem infixUnion_empty : infixUnion A ∅ = 0 := by
  ext x
  constructor
  · rintro ⟨v, hv, -⟩
    exact (Set.notMem_empty v hv).elim
  · intro hx
    exact (Language.notMem_zero x hx).elim

theorem infixUnion_insert (v : List A.D) (s : Set (List A.D)) :
    infixUnion A (insert v s) = containsInfix A v + infixUnion A s := by
  ext x
  rw [Language.mem_add]
  constructor
  · rintro ⟨w, hw, hx⟩
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact Or.inl hx
    · exact Or.inr ⟨w, hw, hx⟩
  · rintro (hx | ⟨w, hw, hx⟩)
    · exact ⟨v, Set.mem_insert _ _, hx⟩
    · exact ⟨w, Set.mem_insert_of_mem _ hw, hx⟩

private theorem isRegular_zero : (0 : Language A.D).IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient
    ((Set.finite_singleton (0 : Language A.D)).subset ?_)
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_singleton_iff]
  ext y
  rw [Language.mem_leftQuotient]
  exact ⟨fun h => (Language.notMem_zero _ h).elim,
    fun h => (Language.notMem_zero _ h).elim⟩

/-- A finite union of infix languages is regular. -/
theorem infixUnion_isRegular [Finite A.D] {s : Set (List A.D)}
    (hs : s.Finite) : (infixUnion A s).IsRegular := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      rw [infixUnion_empty]
      exact isRegular_zero A
  | @insert v s _ _ ih =>
      rw [infixUnion_insert]
      exact (containsInfix_isRegular A v).add ih

/-! ### The envelope -/

theorem eq_infixUnion (U : Set (List A.D)) :
    A.offenseSuffixLang U = infixUnion A (A.HatU U) := by
  ext x
  constructor
  · rintro ⟨pref, v, suff, hv, rfl⟩
    exact ⟨v, hv, pref, suff, rfl⟩
  · rintro ⟨v, hv, pref, suff, rfl⟩
    exact ⟨pref, v, suff, hv, rfl⟩

/-- The envelope is closed under extension on either side. -/
theorem infix_closed {U : Set (List A.D)} {x : List A.D}
    (hx : x ∈ A.offenseSuffixLang U) (y z : List A.D) :
    y ++ x ++ z ∈ A.offenseSuffixLang U := by
  rcases hx with ⟨pref, v, suff, hv, rfl⟩
  exact ⟨y ++ pref, v, suff ++ z, hv, by simp [List.append_assoc]⟩

/-- Under a finite offense horizon the infix envelope is regular. -/
theorem isRegular [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)} (hFin : A.FiniteOffenseHorizon U) :
    Language.IsRegular (A.offenseSuffixLang U) := by
  rcases hFin with ⟨M, hM⟩
  rw [eq_infixUnion]
  exact infixUnion_isRegular A (HatU.finite_of_horizon A hM)

end offenseSuffixLang

end ActionSystem
end Actions
