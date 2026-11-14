/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Motivational calculus — model and sampled semantic implications

Shallow formalization of Nowakowska 1973 §2.2.4 (epistemic model) plus a
sampled subset of §2.1.4 semantic implications, interpreted as set constraints
on a speaker world. Prefer/want/can appear as thin additional structures.
-/

namespace Actions
namespace MotCalc

abbrev PropSet (X : Type*) := Set X

/-- Epistemic part of the §2.2.4 model
\(\langle X, P, v_T, v_B, v_{Cr}, v_D \rangle\) with
\(v_T \subset v_B \cap v_{Cr} \cap v_D\). -/
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

structure GladModel (X : Type*) extends EpistemicModel X where
  vG : PropSet X
  vG_disjoint_vT : vG ∩ vT = ∅

/-- Reading of \(G\alpha\) used for rule (48): gladness forces think-containment
or (when the gladness seed sits in \(\alpha\)) knowledge. -/
def GladModel.Glad {X} (M : GladModel X) (α : PropSet X) : Prop :=
  M.vT ⊆ α ∨ (M.vG ⊆ α ∧ M.P α = 1)

end EpistemicModel

variable {X : Type*} (M : EpistemicModel X)

def SemImp (A B : Prop) : Prop := A → B

/-- (2)/(5): \(K(p \land q) \leftrightarrow Kp \land Kq\). -/
theorem semImp_K_and (p q : PropSet X) :
    M.Know (p ∩ q) ↔ M.Know p ∧ M.Know q :=
  M.P_inter_one

/-- (3)/(6): \(Cr(p \land q) \leftrightarrow Cr\,p \land Cr\,q\). -/
theorem semImp_Cr_and (p q : PropSet X) :
    M.Certain (p ∩ q) ↔ M.Certain p ∧ M.Certain q :=
  ⟨fun h => ⟨fun _ hx => (h hx).1, fun _ hx => (h hx).2⟩,
    fun ⟨hp, hq⟩ _ hx => ⟨hp hx, hq hx⟩⟩

/-- (4)/(7): \(T(p \land q) \leftrightarrow Tp \land Tq\). -/
theorem semImp_T_and (p q : PropSet X) :
    M.Think (p ∩ q) ↔ M.Think p ∧ M.Think q :=
  ⟨fun h => ⟨fun _ hx => (h hx).1, fun _ hx => (h hx).2⟩,
    fun ⟨hp, hq⟩ _ hx => ⟨hp hx, hq hx⟩⟩

/-- (23) with nonempty \(v_T\): \(T'p \xrightarrow{s} \sim Tp\). -/
theorem semImp_Tprime_not_T (p : PropSet X) (hv : M.vT.Nonempty)
    (h : M.DontThink p) : ¬ M.Think p := by
  intro hT
  rcases hv with ⟨x, hx⟩
  exact h (hT hx) hx

/-- (16) with nonempty \(v_T\): \(Cr\,p \xrightarrow{s} \sim T\,\sim p\). -/
theorem semImp_Cr_not_T_not (p : PropSet X) (hv : M.vT.Nonempty)
    (h : M.Certain p) : ¬ M.Think (pᶜ) := by
  intro hT
  rcases hv with ⟨x, hx⟩
  exact hT hx (h (M.vT_subset_vCr hx))

/-- (18): \(Tp \xrightarrow{s} T'\,\sim p\). -/
theorem semImp_T_Tprime_not (p : PropSet X) (h : M.Think p) :
    M.DontThink (pᶜ) := by
  intro x hx hxT
  exact hx (h hxT)

/-- (30): \(Dp \xrightarrow{s} T'p\). -/
theorem semImp_D_Tprime (p : PropSet X) (h : M.Doubt p) : M.DontThink p := by
  intro x hx hxT
  exact h hx (M.vT_subset_vD hxT)

/-- (22): \(T'p \land T'q \xrightarrow{s} T'(p \lor q)\). -/
theorem semImp_Tprime_or (p q : PropSet X)
    (hp : M.DontThink p) (hq : M.DontThink q) : M.DontThink (p ∪ q) := by
  intro x hx
  cases hx with
  | inl h => exact hp h
  | inr h => exact hq h

/-- (11): \(K'(p,q) \xrightarrow{s} \sim Kp\). -/
theorem semImp_Kprime_not_K (p q : PropSet X)
    (h : M.DontKnowWhether p q) : ¬ M.Know p := by
  intro hk
  rcases h with ⟨hdisj, _, _, hqpos⟩
  have : M.P q = 0 := M.P_one_disjoint hk hdisj
  linarith

/-- (26): \(B'p \xrightarrow{s} T\,\sim p\). -/
theorem semImp_Bprime_T_not (p : PropSet X) (h : M.DontBelieve p) :
    M.Think (pᶜ) := by
  intro x hx
  have : x ∈ M.vB := M.vT_subset_vB hx
  have : x ∉ p := fun hp => h hp this
  exact this

/-- (48)-style gladness: \(Gp \xrightarrow{s} Kp \lor Tp\). -/
theorem semImp_G_Know_or_Think (M : EpistemicModel.GladModel X)
    (p : PropSet X) (h : M.Glad p) : M.Know p ∨ M.Think p := by
  cases h with
  | inl hT => exact Or.inr hT
  | inr h => exact Or.inl h.2

/-- Bundle of sampled §2.1.4 rules validated by the epistemic model. -/
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

theorem epistemicModel_sampledSemImp (M : EpistemicModel X) :
    SampledSemImp X M where
  K_and p q := (semImp_K_and M p q).1
  Cr_and p q := (semImp_Cr_and M p q).1
  T_and p q := (semImp_T_and M p q).1
  T_Tprime_not p := semImp_T_Tprime_not M p
  D_Tprime p := semImp_D_Tprime M p
  Tprime_or p q := fun ⟨hp, hq⟩ => semImp_Tprime_or M p q hp hq
  Kprime_not_K p q := semImp_Kprime_not_K M p q
  Bprime_T_not p := semImp_Bprime_T_not M p
  Cr_not_T_not hv p := semImp_Cr_not_T_not M p hv
  Tprime_not_T hv p := semImp_Tprime_not_T M p hv

/-- Prefer / want / can sample (thin; cross-functor packaging). -/
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
