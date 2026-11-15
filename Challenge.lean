/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.DropRight
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic

/-!
# Palomar Challenge (statement of record)

Single-file Mathlib-only Challenge. Compared declarations match `Solution.lean`
via the sorry-free `Actions/` library. Framing: reconstruction/verification of
Nowakowska 1982/1973, plus Lean discharge of classical CF ∩ Regular.
-/
@[expose] public section

namespace Actions
end Actions
namespace Actions
namespace Conflicts
def doubletons : List ℕ := [3, 5, 6, 9, 10, 12]
def tripleRequirements : List (ℕ × List ℕ) :=
  [(7, [3, 5, 6]), (11, [3, 9, 10]), (13, [5, 9, 12]), (14, [6, 10, 12])]
def doubletonChosen (w : ℕ) (mask : ℕ) : Bool :=
  match doubletons.findIdx? (· == mask) with
  | some i => w.testBit i
  | none => false
def allowedTripleCount (w : ℕ) : ℕ :=
  (tripleRequirements.filter fun ⟨_, reqs⟩ =>
    reqs.all (doubletonChosen w)).length
def patternsFor (w : ℕ) : ℕ :=
  2 ^ allowedTripleCount w
def conflictPatternCount : ℕ :=
  ((List.range 64).map patternsFor).sum
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
def IsConflictFamily (F : Finset (Finset (Fin 4))) : Prop :=
  (∀ s ∈ F, ∀ t ⊆ s, t ∈ F) ∧ (∀ i : Fin 4, {i} ∈ F) ∧ Finset.univ ∉ F
instance IsConflictFamily.instDecidablePred : DecidablePred IsConflictFamily :=
  fun F => by unfold IsConflictFamily; infer_instance
namespace IsConflictFamily
variable {F : Finset (Finset (Fin 4))}
end IsConflictFamily
def pairSets : Finset (Finset (Fin 4)) :=
  Finset.powersetCard 2 Finset.univ
def tripleSets : Finset (Finset (Fin 4)) :=
  Finset.powersetCard 3 Finset.univ
def lowSets : Finset (Finset (Fin 4)) :=
  Finset.univ.filter fun s => s.card ≤ 1
def allowedTriples (D : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  tripleSets.filter fun t => ∀ p ∈ t.powersetCard 2, p ∈ D
def assemble (D T : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  lowSets ∪ D ∪ T
def pairPart (F : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  F.filter fun s => s.card = 2
def triplePart (F : Finset (Finset (Fin 4))) : Finset (Finset (Fin 4)) :=
  F.filter fun s => s.card = 3
def ofMask (m : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter fun i => m.testBit i
def pairsOfWord (w : ℕ) : Finset (Finset (Fin 4)) :=
  ((doubletons.filter (doubletonChosen w)).map ofMask).toFinset
theorem card_conflictFamilies : (Finset.univ.filter IsConflictFamily).card = 113 := by
  sorry
end Conflicts
end Actions
namespace Actions
namespace MotCalc
abbrev PropSet (X : Type*) := Set X
structure EpistemicModel (X : Type*) where
  P : PropSet X → ℝ
  vT : PropSet X
  vB : PropSet X
  vCr : PropSet X
  vD : PropSet X
  vT_subset_vB : vT ⊆ vB
  vT_subset_vCr : vT ⊆ vCr
  vT_subset_vD : vT ⊆ vD
  P_univ : P Set.univ = 1
  P_empty : P ∅ = 0
  P_inter_one : ∀ {p q}, P (p ∩ q) = 1 ↔ P p = 1 ∧ P q = 1
  /-- If \(P(p)=1\) and \(p\cap q=\emptyset\), then \(P(q)=0\). -/
  P_one_disjoint : ∀ {p q}, P p = 1 → p ∩ q = ∅ → P q = 0
namespace EpistemicModel
variable {X : Type*} (M : EpistemicModel X)
def Know (α : PropSet X) : Prop := M.P α = 1
def Certain (α : PropSet X) : Prop := M.vCr ⊆ α
def Think (α : PropSet X) : Prop := M.vT ⊆ α
def DontThink (α : PropSet X) : Prop := α ⊆ M.vTᶜ
def Believe (α : PropSet X) : Prop := M.vB ⊆ α
def DontBelieve (α : PropSet X) : Prop := α ⊆ M.vBᶜ
def Doubt (α : PropSet X) : Prop := α ⊆ M.vDᶜ
def DontKnowWhether (α β : PropSet X) : Prop :=
  α ∩ β = ∅ ∧ α ∪ β = Set.univ ∧ 0 < M.P α ∧ 0 < M.P β
end EpistemicModel
end MotCalc
end Actions
namespace Actions
structure ActionSystem where
  /-- Alphabet of elementary actions. -/
  D : Type*
  /-- Distinguished pause action. -/
  pause : D
  /-- Duration of an elementary action (positive for every action). -/
  φ : D → ℝ
  φ_pos : ∀ d, 0 < φ d
  /-- Duration of a pause is `1`. -/
  φ_pause : φ pause = 1
  /-- Outcomes of interest. -/
  S : Type*
  /-- Admissible strings (`L ⊆ D*`). -/
  L : Set (List D)
  /-- Causation: string `u` brings about outcome `s` at discrete time `t`.
  Time is specialized to `ℕ` (Nowakowska’s countable time moments). -/
  R : List D → S → ℕ → Prop
  /-- Only admissible strings stand in `R`. -/
  R_mem_L : ∀ {u s t}, R u s t → u ∈ L
namespace ActionSystem
variable (A : ActionSystem)
def pauseString (n : ℕ) : List A.D :=
  List.replicate n A.pause
abbrev TimeResult := A.S × ℕ
def Rinv (s : A.S) (t : ℕ) : Set (List A.D) :=
  { u | A.R u s t }
theorem Rinv_subset_L (s : A.S) (t : ℕ) :
    A.Rinv s t ⊆ A.L := by
  sorry
def Attainable (s : A.S) (t : ℕ) : Prop :=
  (A.Rinv s t).Nonempty
end ActionSystem
end Actions
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
namespace Actions
namespace MotCalc
structure PreferWantCan (X : Type*) where
  Prefer : PropSet X → PropSet X → Prop
  Want : PropSet X → Prop
  DontWant : PropSet X → Prop
  Can : PropSet X → Prop
  Cannot : PropSet X → Prop
  Ought : PropSet X → Prop
  Must : PropSet X → Prop
  prefer_asymm : ∀ p q, Prefer p q → ¬ Prefer q p
  want_not_dont : ∀ p, Want p → ¬ DontWant p
  can_not_cannot : ∀ p, Can p → ¬ Cannot p
  must_imp_ought : ∀ p, Must p → Ought p
  /-- Sampled cross-functor: prefer forces want of the preferred side. -/
  prefer_imp_want : ∀ p q, Prefer p q → Want p
end MotCalc
end Actions
namespace Actions
namespace MotCalc
structure GladModel (X : Type*) extends EpistemicModel X where
  vG : PropSet X
  vG_disjoint_vT : vG ∩ vT = ∅
namespace GladModel
def Glad {X} (M : GladModel X) (α : PropSet X) : Prop :=
  M.vT ⊆ α ∨ (M.vG ⊆ α ∧ M.P α = 1)
end GladModel
end MotCalc
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def NonParasitic (u : List A.D) : Prop :=
  ∃ w₁ w₂ : List A.D, w₁ ++ u ++ w₂ ∈ A.L
namespace NonParasitic
theorem of_mem_L {u : List A.D} (hu : u ∈ A.L) : A.NonParasitic u := by
  sorry
theorem append_left_right {u w₁ w₂ : List A.D}
    (h : w₁ ++ u ++ w₂ ∈ A.L) : A.NonParasitic u := by
  sorry
end NonParasitic
end ActionSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
abbrev GoalSet := List A.TimeResult
def RinvUnion (C : GoalSet A) : Set (List A.D) :=
  { u | ∃ st ∈ C, u ∈ A.Rinv st.1 st.2 }
def RinvInter (C : GoalSet A) : Set (List A.D) :=
  { u | ∀ st ∈ C, u ∈ A.Rinv st.1 st.2 }
def WeaklyAttainable (C : GoalSet A) : Prop :=
  (A.RinvUnion C).Nonempty
def StronglyAttainable (C : GoalSet A) : Prop :=
  (A.RinvInter C).Nonempty
theorem strongly_implies_weakly {C : GoalSet A} (hC : C ≠ [])
    (h : A.StronglyAttainable C) : A.WeaklyAttainable C := by
  sorry
def RinvNeg (s : A.S) (t : ℕ) : Set (List A.D) :=
  A.L \ A.Rinv s t
def MotiveConflict (C : GoalSet A) : Prop :=
  A.WeaklyAttainable C ∧ ¬ A.StronglyAttainable C
theorem weakly_iff_strongly_singleton (st : A.TimeResult) :
    A.WeaklyAttainable [st] ↔ A.StronglyAttainable [st] := by
  sorry
end ActionSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
noncomputable def minφ [Fintype A.D] [Nonempty A.D] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty A.φ
end ActionSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def EffortDominated (u u' : List A.D) : Prop :=
  ∃ hlen : u.length = u'.length,
    ∀ i (hi : i < u.length),
      u[i] = u'[i]'(hlen ▸ hi) ∨
        (u'[i]'(hlen ▸ hi) = A.pause ∧ u[i] ≠ A.pause)
namespace EffortDominated
theorem refl (u : List A.D) : A.EffortDominated u u := by
  sorry
end EffortDominated
end ActionSystem
end Actions
namespace Actions
structure ActionAutomaton where
  /-- Internal states. -/
  U : Type*
  /-- Stimuli. -/
  B : Type*
  /-- Null stimulus. -/
  Θ : B
  /-- Elementary actions. -/
  D : Type*
  /-- Pause action. -/
  pause : D
  /-- Admissible actions in a state/stimulus context (nonempty). -/
  τ : U → B → Set D
  τ_nonempty : ∀ u b, (τ u b).Nonempty
  /-- Transition map. -/
  π : U → B → D → U
namespace ActionAutomaton
variable (M : ActionAutomaton)
inductive Admissible : M.U → M.B → List M.D → Prop where
  | nil (u : M.U) (b : M.B) : Admissible u b []
  | cons {u : M.U} {b : M.B} {d : M.D} {ds : List M.D} {b' : M.B}
      (hd : d ∈ M.τ u b)
      (tail : Admissible (M.π u b d) b' ds) :
      Admissible u b (d :: ds)
def language (u₀ : M.U) (b₀ : M.B) : Set (List M.D) :=
  { ds | M.Admissible u₀ b₀ ds }
theorem nil_mem_language (u₀ : M.U) (b₀ : M.B) :
    ([] : List M.D) ∈ M.language u₀ b₀ := by
  sorry
theorem singleton_admissible {u : M.U} {b : M.B} {d : M.D}
    (hd : d ∈ M.τ u b) : M.Admissible u b [d] := by
  sorry
def nextState (u : M.U) (b : M.B) (d : M.D) : M.U :=
  M.π u b d
theorem nextState_eq (u : M.U) (b : M.B) (d : M.D) :
    M.nextState u b d = M.π u b d := by
  sorry
theorem admissible_cons_nextState {u : M.U} {b b' : M.B} {d : M.D}
    {ds : List M.D} (hd : d ∈ M.τ u b)
    (tail : M.Admissible (M.nextState u b d) b' ds) :
    M.Admissible u b (d :: ds) := by
  sorry
theorem mem_language_iff (u₀ : M.U) (b₀ : M.B) (ds : List M.D) :
    ds ∈ M.language u₀ b₀ ↔ M.Admissible u₀ b₀ ds := by
  sorry
inductive Reaches : M.U → M.B → List M.D → M.U → Prop where
  | nil (u : M.U) (b : M.B) : Reaches u b [] u
  | cons {u : M.U} {b : M.B} {d : M.D} {ds : List M.D} {b' : M.B} {s : M.U}
      (hd : d ∈ M.τ u b)
      (tail : Reaches (M.π u b d) b' ds s) :
      Reaches u b (d :: ds) s
theorem Reaches.admissible {u s : M.U} {b : M.B} {ds : List M.D}
    (h : M.Reaches u b ds s) : M.Admissible u b ds := by
  sorry
theorem mem_language_iff_exists_reaches (u₀ : M.U) (b₀ : M.B) (ds : List M.D) :
    ds ∈ M.language u₀ b₀ ↔ ∃ s, M.Reaches u₀ b₀ ds s := by
  sorry
inductive ReachableIn : M.U → M.B → ℕ → M.U → Prop where
  | zero (u : M.U) (b : M.B) : ReachableIn u b 0 u
  | succ {u : M.U} {b : M.B} {d : M.D} {b' : M.B} {n : ℕ} {s : M.U}
      (hd : d ∈ M.τ u b)
      (tail : ReachableIn (M.π u b d) b' n s) :
      ReachableIn u b (n + 1) s
end ActionAutomaton
end Actions
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
def rank3 (a b : Fin 3) (p q s : Fin 3) : Ranking3 := fun x =>
  if x = a then p else if x = b then q else s
namespace rank3
variable {a b c p q s : Fin 3}
end rank3
def swapSWF (F : SWF2) : SWF2 := fun π => F (π.2, π.1)
namespace swapSWF
variable {F : SWF2}
end swapSWF
def Decisive1 (F : SWF2) (a b : Fin 3) : Prop :=
  ∀ π : Profile2, π.1 a < π.1 b → π.2 b < π.2 a → F π a < F π b
namespace Decisive1
variable {F : SWF2}
end Decisive1
theorem arrow_dictator_of_unanimity_IIA (F : SWF2) :
    Unanimity F → IIA F → ∃ i : Fin 2, IsDictator F i := by
  sorry
end Arrow
end Actions
namespace Actions
namespace MotCalc
variable {X : Type*} (M : EpistemicModel X)
def SemImp (A B : Prop) : Prop := A → B
end MotCalc
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def RinvWanted (W : Set A.TimeResult) : Set (List A.D) :=
  { u | ∀ st ∈ W, u ∈ A.Rinv st.1 st.2 }
def RinvUnwanted (W' : Set A.TimeResult) : Set (List A.D) :=
  { u | ∃ st ∈ W', u ∈ A.Rinv st.1 st.2 }
namespace RinvWanted
theorem mem_iff {W : Set A.TimeResult} {u : List A.D} :
    u ∈ A.RinvWanted W ↔ ∀ st ∈ W, u ∈ A.Rinv st.1 st.2 := by
  sorry
theorem empty : A.RinvWanted (∅ : Set A.TimeResult) = Set.univ := by
  sorry
end RinvWanted
namespace RinvUnwanted
theorem mem_iff {W' : Set A.TimeResult} {u : List A.D} :
    u ∈ A.RinvUnwanted W' ↔ ∃ st ∈ W', u ∈ A.Rinv st.1 st.2 := by
  sorry
end RinvUnwanted
end ActionSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
noncomputable def stringDuration (u : List A.D) : ℝ :=
  (u.map A.φ).sum
theorem stringDuration_pauseString (n : ℕ) :
    A.stringDuration (A.pauseString n) = n := by
  sorry
namespace stringDuration
theorem nil_not_pos : ¬ (0 < A.stringDuration []) := by
  sorry
end stringDuration
end ActionSystem
end Actions
namespace Actions
namespace ActionAutomaton
variable (M : ActionAutomaton)
noncomputable def toActionSystem (u₀ : M.U) (b₀ : M.B) : ActionSystem where
  D := M.D
  pause := M.pause
  φ := fun _ => (1 : ℝ)
  φ_pos := fun _ => zero_lt_one
  φ_pause := rfl
  S := M.U
  L := M.language u₀ b₀
  R := fun u s t => M.Reaches u₀ b₀ u s ∧ t = u.length
  R_mem_L := fun h => (Reaches.admissible (M := M) h.1)
namespace toActionSystem
theorem mem_L_iff (u₀ : M.U) (b₀ : M.B) (ds : List M.D) :
    ds ∈ (M.toActionSystem u₀ b₀).L ↔ M.Admissible u₀ b₀ ds := by
  sorry
theorem Attainable_iff_reaches_length (u₀ : M.U) (b₀ : M.B) (s : M.U) (t : ℕ) :
    (M.toActionSystem u₀ b₀).Attainable s t ↔
      ∃ ds : List M.D, ds.length = t ∧ M.Reaches u₀ b₀ ds s := by
  sorry
end toActionSystem
end ActionAutomaton
end Actions
namespace Actions
namespace Arrow
def prefer (a b : Fin 3) : Ranking3 := fun x =>
  if x = a then (0 : Fin 3) else if x = b then (1 : Fin 3) else (2 : Fin 3)
end Arrow
end Actions
namespace Actions
namespace Arrow
def NeuroticAllOrNothing (F : SWF2) : Prop := by
  sorry
namespace NeuroticAllOrNothing
theorem of_not_IIA {F : SWF2} (h : ¬ IIA F) :
    NeuroticAllOrNothing F := by
  sorry
end NeuroticAllOrNothing
end Arrow
end Actions
namespace Actions
namespace Arrow
def BlindObedience (F : SWF2) : Prop := by
  sorry
namespace BlindObedience
theorem of_not_sovereignty {F : SWF2} (h : ¬ Sovereignty F) :
    BlindObedience F := by
  sorry
end BlindObedience
end Arrow
end Actions
namespace Actions
namespace MotCalc
variable {X : Type*}
structure SampledSemImp (X : Type*) (M : EpistemicModel X) : Prop where
  K_and : ∀ p q, SemImp (M.Know (p ∩ q)) (M.Know p ∧ M.Know q)
  Cr_and : ∀ p q, SemImp (M.Certain (p ∩ q)) (M.Certain p ∧ M.Certain q)
  T_and : ∀ p q, SemImp (M.Think (p ∩ q)) (M.Think p ∧ M.Think q)
  T_Tprime_not : ∀ p, SemImp (M.Think p) (M.DontThink (pᶜ))
  D_Tprime : ∀ p, SemImp (M.Doubt p) (M.DontThink p)
  Tprime_or : ∀ p q, SemImp (M.DontThink p ∧ M.DontThink q) (M.DontThink (p ∪ q))
  Kprime_not_K : ∀ p q, SemImp (M.DontKnowWhether p q) (¬ M.Know p)
  Bprime_T_not : ∀ p, SemImp (M.DontBelieve p) (M.Think (pᶜ))
  Cr_not_T_not : M.vT.Nonempty → ∀ p, SemImp (M.Certain p) (¬ M.Think (pᶜ))
  Tprime_not_T : M.vT.Nonempty → ∀ p, SemImp (M.DontThink p) (¬ M.Think p)
namespace SampledSemImp
theorem epistemicModel (M : EpistemicModel X) : SampledSemImp X M := by
  sorry
end SampledSemImp
end MotCalc
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def Prax (realizers : Set (List A.D)) : Set (List A.D) :=
  { u ∈ realizers |
      ¬ ∃ u' ∈ realizers, A.EffortDominated u u' ∧ u ≠ u' }
namespace Prax
noncomputable def Min (realizers : Set (List A.D)) : Set (List A.D) :=
  { u ∈ A.Prax realizers |
      ∀ u' ∈ A.Prax realizers, ¬ A.stringDuration u' < A.stringDuration u }
theorem subset (realizers : Set (List A.D)) :
    A.Prax realizers ⊆ realizers := by
  sorry
theorem Min_subset (realizers : Set (List A.D)) :
    Min A realizers ⊆ A.Prax realizers := by
  sorry
end Prax
end ActionSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def HatT (T : Set (List A.D)) : Set (List A.D) :=
  { x ∈ T |
      ∀ x₁ x₂, x = x₁ ++ x₂ → 0 < A.stringDuration x₂ → x₁ ∉ T }
namespace HatT
theorem subset (T : Set (List A.D)) : A.HatT T ⊆ T := by
  sorry
end HatT
noncomputable def horizon (T : Set (List A.D)) : WithTop ℝ :=
  sSup ((A.stringDuration ·) '' A.HatT T)
def FiniteHorizon (T : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatT T, A.stringDuration x ≤ M
end ActionSystem
end Actions
namespace Actions
structure MixedSystem where
  /-- Underlying action sixtuplet. -/
  toActionSystem : ActionSystem
  /-- Alphabet of motivational sentences. -/
  M : Type*
  /-- Duration of a sentence in pause-units (may be zero). -/
  φM : M → ℕ
  /-- Wanted time-results when `α` is uttered at discrete time `k`. -/
  W : M → ℕ → Set (toActionSystem.S × ℕ)
  /-- Unwanted *results* when `α` is uttered at time `k`. -/
  W'_results : M → ℕ → Set toActionSystem.S
  /-- Obligation: subsequent strings that ought to be chosen. -/
  O : M → ℕ → Set (List toActionSystem.D)
  /-- Prohibition: subsequent strings that should not be chosen. -/
  O' : M → ℕ → Set (List toActionSystem.D)
  /-- Assumption (7): same utterance is not self-contradictory on wants. -/
  W_disjoint_W' : ∀ α k s n,
    (s, n) ∈ W α k → s ∉ W'_results α k
  /-- Assumption (11): positive obligations are right-closed in `D*₊`. -/
  O_right_closed : ∀ α k {u v : List toActionSystem.D},
    u ∈ O α k → (∃ w₁ w₂, w₁ ++ u ++ v ++ w₂ ∈ toActionSystem.L) →
      u ++ v ∈ O α k
  /-- Assumption (12): prohibitions are two-sided closed in `D*₊`. -/
  O'_embed_closed : ∀ α k {u v w : List toActionSystem.D},
    v ∈ O' α k → (∃ w₁ w₂, w₁ ++ u ++ v ++ w ++ w₂ ∈ toActionSystem.L) →
      u ++ v ++ w ∈ O' α k
  /-- Assumption (13): every utterance asserts at least one of the four. -/
  utterance_nonempty : ∀ α k,
    (W α k).Nonempty ∨ (W'_results α k).Nonempty ∨
      (O α k).Nonempty ∨ (O' α k).Nonempty
namespace MixedSystem
variable (S : MixedSystem)
abbrev base : ActionSystem := S.toActionSystem
abbrev D := S.base.D
abbrev L := S.base.L
abbrev TimeResult := S.base.TimeResult
def W' (α : S.M) (k : ℕ) : Set S.TimeResult :=
  { p | p.1 ∈ S.W'_results α k }
theorem W_disjoint (α : S.M) (k : ℕ) :
    S.W α k ∩ S.W' α k = ∅ := by
  sorry
abbrev Letter := Sum S.D S.M
noncomputable def letterDuration : S.Letter → ℝ
  | Sum.inl d => S.base.φ d
  | Sum.inr α => (S.φM α : ℝ)
noncomputable def mixedDuration (x : List S.Letter) : ℝ :=
  (x.map S.letterDuration).sum
noncomputable def utteranceTime (u : List S.D) : ℕ :=
  Nat.floor (S.base.stringDuration u)
end MixedSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def HatU (U : Set (List A.D)) : Set (List A.D) :=
  { v ∈ U |
      ∀ x y z, v = x ++ y ++ z →
        0 < A.stringDuration x + A.stringDuration z → y ∉ U }
namespace HatU
theorem subset (U : Set (List A.D)) : A.HatU U ⊆ U := by
  sorry
end HatU
def FiniteOffenseHorizon (U : Set (List A.D)) : Prop :=
  ∃ M : ℝ, ∀ x ∈ A.HatU U, A.stringDuration x ≤ M
def OffensePrime (U : Set (List A.D)) : Prop :=
  ∀ {u v : List A.D}, u ++ v ∈ U → u ∈ U ∨ v ∈ U
end ActionSystem
end Actions
namespace Actions
namespace Arrow
def scale1Dictator : SWF2 := fun π => π.1
namespace scale1Dictator
theorem unanimity : Unanimity scale1Dictator := by
  sorry
theorem IIA : IIA scale1Dictator := by
  sorry
theorem not_lack : ¬ LackOfDictator scale1Dictator := by
  sorry
theorem sovereignty : Sovereignty scale1Dictator := by
  sorry
end scale1Dictator
end Arrow
end Actions
namespace Actions
namespace Arrow
def scale2Dictator : SWF2 := fun π => π.2
namespace scale2Dictator
theorem unanimity : Unanimity scale2Dictator := by
  sorry
theorem IIA : IIA scale2Dictator := by
  sorry
theorem not_lack : ¬ LackOfDictator scale2Dictator := by
  sorry
theorem sovereignty : Sovereignty scale2Dictator := by
  sorry
end scale2Dictator
end Arrow
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def promiseSuffixLang (T : Set (List A.D)) : Language A.D :=
  { x | ∃ u ∈ A.HatT T, ∃ v : List A.D, x = u ++ v }
end ActionSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
def piGo : ℕ → List S.Letter → List S.D
  | pending, [] => S.base.pauseString pending
  | pending, Sum.inl d :: rest =>
      S.base.pauseString pending ++ d :: piGo 0 rest
  | pending, Sum.inr α :: rest =>
      piGo (pending + S.φM α) rest
def pi (x : List S.Letter) : List S.D :=
  piGo S 0 x
namespace pi
theorem stringDuration_pi (x : List S.Letter) :
    S.base.stringDuration (S.pi x) = S.mixedDuration x := by
  sorry
end pi
end MixedSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def offenseSuffixLang (U : Set (List A.D)) : Language A.D :=
  { x | ∃ pref v suff, v ∈ A.HatU U ∧ x = pref ++ v ++ suff }
abbrev offenseInfixLang (U : Set (List A.D)) : Language A.D :=
  A.offenseSuffixLang U
namespace offenseSuffixLang
def containsInfix (v : List A.D) : Language A.D :=
  { x | ∃ a b : List A.D, x = a ++ v ++ b }
def infixUnion (s : Set (List A.D)) : Language A.D :=
  { x | ∃ v ∈ s, x ∈ containsInfix A v }
end offenseSuffixLang
end ActionSystem
end Actions
namespace Actions
namespace Arrow
def ArrowPostulates2 (F : SWF2) : Prop :=
  LackOfDictator F ∧ Unanimity F ∧ IIA F ∧ Sovereignty F
theorem arrow_impossibility (F : SWF2) : ¬ ArrowPostulates2 F := by
  sorry
end Arrow
end Actions
namespace Actions
namespace Arrow
def CompulsiveOrHedonistic (F : SWF2) : Prop := by
  sorry
namespace CompulsiveOrHedonistic
theorem of_not_lack {F : SWF2} (h : ¬ LackOfDictator F) :
    CompulsiveOrHedonistic F := by
  sorry
theorem of_dictator {F : SWF2} {i : Fin 2} (h : IsDictator F i) :
    CompulsiveOrHedonistic F := by
  sorry
end CompulsiveOrHedonistic
namespace scale1Dictator
theorem compulsive : CompulsiveOrHedonistic scale1Dictator := by
  sorry
end scale1Dictator
end Arrow
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def PromiseClosed (T : Set (List A.D)) : Prop :=
  ∀ {x y : List A.D}, x ++ y ∈ A.L → x ∈ T → x ++ y ∈ T
namespace PromiseClosed
theorem mono {T : Set (List A.D)}
    (ha : A.PromiseClosed T) {x y : List A.D}
    (hxy : x ++ y ∈ A.L) (hx : x ∈ T) : x ++ y ∈ T := by
  sorry
theorem isContextFree [Fintype A.D] [Nonempty A.D]
    {T : Set (List A.D)}
    (hSub : T ⊆ A.L) (ha : A.PromiseClosed T) (hFin : A.FiniteHorizon T)
    (hL : Language.IsContextFree (A.L : Language A.D)) :
    Language.IsContextFree (T : Language A.D) := by
  sorry
end PromiseClosed
end ActionSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
abbrev Lambda := S.M × ℕ
def ConsistentWith (x : List S.D) (αk : S.Lambda) : Prop :=
  x ∈ S.base.L ∧
    (S.W αk.1 αk.2 = ∅ ∨ x ∈ S.base.RinvWanted (S.W αk.1 αk.2)) ∧
    (S.W' αk.1 αk.2 = ∅ ∨ x ∉ S.base.RinvUnwanted (S.W' αk.1 αk.2)) ∧
    ∃ u v : List S.D,
      x = u ++ S.base.pauseString (S.φM αk.1) ++ v ∧
        S.utteranceTime u = αk.2 ∧
        (S.O αk.1 αk.2 = ∅ ∨ v ∈ S.O αk.1 αk.2) ∧
        (S.O' αk.1 αk.2 = ∅ ∨ v ∉ S.O' αk.1 αk.2)
def ConsistentWithSet (x : List S.D) (A : Set S.Lambda) : Prop :=
  ∀ αk ∈ A, S.ConsistentWith x αk
end MixedSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
def LM : Set (List S.Letter) :=
  { x | S.pi x ∈ S.base.L }
namespace LM
theorem mem_iff {x : List S.Letter} : x ∈ S.LM ↔ S.pi x ∈ S.base.L := by
  sorry
theorem of_pure_actions {u : List S.D} (hu : u ∈ S.base.L) :
    u.map Sum.inl ∈ S.LM := by
  sorry
end LM
def hasUtterance (x : List S.Letter) : Prop :=
  ∃ α : S.M, Sum.inr α ∈ x
def LM_minus_L : Set (List S.Letter) :=
  { x | x ∈ S.LM ∧ S.hasUtterance x }
end MixedSystem
end Actions
namespace Actions
namespace ActionSystem
variable (A : ActionSystem)
def OffenseClosed (U : Set (List A.D)) : Prop :=
  ∀ {x y z : List A.D}, x ++ y ++ z ∈ A.L → y ∈ U → x ++ y ++ z ∈ U
namespace OffenseClosed
theorem isContextFree [Fintype A.D] [Nonempty A.D]
    {U : Set (List A.D)}
    (hSub : U ⊆ A.L) (hb : A.OffenseClosed U) (hFin : A.FiniteOffenseHorizon U)
    (hL : Language.IsContextFree (A.L : Language A.D)) :
    Language.IsContextFree (U : Language A.D) := by
  sorry
end OffenseClosed
end ActionSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
structure VerbalOcc where
  α : S.M
  pref : List S.Letter
  suff : List S.Letter
namespace VerbalOcc
def reconstruct (occ : VerbalOcc (S := S)) : List S.Letter :=
  occ.pref ++ Sum.inr occ.α :: occ.suff
def piPrefix (occ : VerbalOcc (S := S)) : List S.D := S.pi occ.pref
def piSuffix (occ : VerbalOcc (S := S)) : List S.D := S.pi occ.suff
noncomputable def time (occ : VerbalOcc (S := S)) : ℕ :=
  S.utteranceTime (S.pi occ.pref)
noncomputable def W_at (occ : VerbalOcc (S := S)) := S.W occ.α (time S occ)
noncomputable def W'_at (occ : VerbalOcc (S := S)) := S.W' occ.α (time S occ)
noncomputable def O_at (occ : VerbalOcc (S := S)) := S.O occ.α (time S occ)
noncomputable def O'_at (occ : VerbalOcc (S := S)) := S.O' occ.α (time S occ)
end VerbalOcc
def verbalOccsAux : List S.Letter → List S.Letter → List (VerbalOcc (S := S))
  | _pref, [] => []
  | pref, Sum.inl d :: rs => verbalOccsAux (pref ++ [Sum.inl d]) rs
  | pref, Sum.inr α :: rs =>
      { α := α, pref := pref, suff := rs } ::
        verbalOccsAux (pref ++ [Sum.inr α]) rs
def verbalOccs (x : List S.Letter) : List (VerbalOcc (S := S)) :=
  verbalOccsAux S [] x
end MixedSystem
end Actions
namespace Actions
namespace Toy
inductive Act where
  | pause
  | work
  deriving DecidableEq, Repr
inductive Out where
  | done
  deriving DecidableEq, Repr
def toy : ActionSystem where
  D := Act
  pause := Act.pause
  φ := fun
    | Act.pause => 1
    | Act.work => 2
  φ_pos := fun
    | Act.pause => by norm_num
    | Act.work => by norm_num
  φ_pause := rfl
  S := Out
  L := Set.univ
  R := fun u s t => s = Out.done ∧ t = u.length ∧ Act.work ∈ u
  R_mem_L := fun _ => trivial
theorem toy_pause_duration : toy.φ Act.pause = 1 := by
  sorry
theorem toy_work_duration : toy.φ Act.work = 2 := by
  sorry
theorem work_attains : toy.Attainable Out.done 1 := by
  sorry
def twoGoals : toy.GoalSet :=
  [(Out.done, 1), (Out.done, 2)]
theorem twoGoals_conflict : toy.MotiveConflict twoGoals := by
  sorry
def promiseT : Set (List Act) :=
  { u | Act.work ∈ u }
theorem promiseT_closed : toy.PromiseClosed promiseT := by
  sorry
theorem work_mem_promiseT : [Act.work] ∈ promiseT := by
  sorry
theorem nil_not_mem_promiseT : ([] : List Act) ∉ promiseT := by
  sorry
theorem Prax_empty_example : toy.Prax (∅ : Set (List Act)) = ∅ := by
  sorry
theorem work_string_duration : toy.stringDuration [Act.work] = 2 := by
  sorry
def offenseU : Set (List Act) :=
  { u | Act.work ∈ u }
theorem HatU_offenseU : toy.HatU offenseU = {[Act.work]} := by
  sorry
theorem offenseU_finiteHorizon : toy.FiniteOffenseHorizon offenseU := by
  sorry
theorem offenseU_closed : toy.OffenseClosed offenseU := by
  sorry
end Toy
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
theorem O_promiseClosed (α : S.M) (k : ℕ) :
    S.base.PromiseClosed (S.O α k) := by
  sorry
theorem O'_offenseClosed (α : S.M) (k : ℕ) :
    S.base.OffenseClosed (S.O' α k) := by
  sorry
end MixedSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
def MotivationalConsistency (x : List S.Letter) : Prop :=
  x ∈ S.LM ∧
    S.hasUtterance x ∧
      ∀ occ ∈ S.verbalOccs x,
        (VerbalOcc.W_at S occ = ∅ ∨
          S.pi x ∈ S.base.RinvWanted (VerbalOcc.W_at S occ)) ∧
        (VerbalOcc.W'_at S occ = ∅ ∨
          S.pi x ∉ S.base.RinvUnwanted (VerbalOcc.W'_at S occ)) ∧
        (VerbalOcc.O_at S occ = ∅ ∨
          VerbalOcc.piSuffix S occ ∈ VerbalOcc.O_at S occ) ∧
        (VerbalOcc.O'_at S occ = ∅ ∨
          VerbalOcc.piSuffix S occ ∉ VerbalOcc.O'_at S occ)
namespace MotivationalConsistency
noncomputable def wantedUnion (x : List S.Letter) : Set S.TimeResult :=
  { st | ∃ occ ∈ S.verbalOccs x, st ∈ VerbalOcc.W_at S occ }
noncomputable def unwantedUnion (x : List S.Letter) : Set S.TimeResult :=
  { st | ∃ occ ∈ S.verbalOccs x, st ∈ VerbalOcc.W'_at S occ }
theorem wanted_unwanted_disjoint {x : List S.Letter}
    (h : S.MotivationalConsistency x) :
    wantedUnion S x ∩ unwantedUnion S x = ∅ := by
  sorry
end MotivationalConsistency
end MixedSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
def Realizes (x : List S.Letter) (alphas : List S.M) (times : List ℕ) : Prop :=
  (S.verbalOccs x).map (·.α) = alphas ∧
    (S.verbalOccs x).map (VerbalOcc.time S) = times
end MixedSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
def Psi (A : Set S.Lambda) : Set (List S.D) :=
  { u | u ∈ S.base.L ∧ S.ConsistentWithSet u A }
namespace Psi
theorem mem_iff {A : Set S.Lambda} {u : List S.D} :
    u ∈ S.Psi A ↔ u ∈ S.base.L ∧ S.ConsistentWithSet u A := by
  sorry
noncomputable def utterancesOf (x : List S.Letter) : Set S.Lambda :=
  { αk | ∃ occ ∈ S.verbalOccs x, αk = (occ.α, VerbalOcc.time S occ) }
theorem pi_mem_of_motivationalConsistency {x : List S.Letter}
    (h : S.MotivationalConsistency x) :
    S.pi x ∈ S.Psi (utterancesOf S x) := by
  sorry
end Psi
end MixedSystem
end Actions
namespace Actions
namespace MixedSystem
variable (S : MixedSystem)
def Satisfiable (alphas : List S.M) (times : List ℕ) : Prop :=
  ∃ x : List S.Letter,
    S.MotivationalConsistency x ∧ S.Realizes x alphas times
namespace Satisfiable
theorem of_motivationalConsistency {x : List S.Letter}
    (h : S.MotivationalConsistency x) :
    S.Satisfiable ((S.verbalOccs x).map (·.α))
      ((S.verbalOccs x).map (VerbalOcc.time S)) := by
  sorry
end Satisfiable
end MixedSystem
end Actions
namespace Language
variable {T : Type*}
theorem IsContextFree.inter_regular {L R : Language T}
    (hL : L.IsContextFree) (hR : R.IsRegular) : (L ⊓ R).IsContextFree := by
  sorry
end Language
