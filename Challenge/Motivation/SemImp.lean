/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Challenge.Motivation.EpistemicModel
public import Challenge.Motivation.GladModel
import Mathlib.Tactic

@[expose] public section

/-!
# Semantic implication and sampled §2.1.4 rules
-/

namespace Actions
namespace MotCalc

variable {X : Type*} (M : EpistemicModel X)

def SemImp (A B : Prop) : Prop := A → B

namespace SemImp

/-- (2)/(5): \(K(p \land q) \leftrightarrow Kp \land Kq\). -/
theorem K_and (p q : PropSet X) :
    M.Know (p ∩ q) ↔ M.Know p ∧ M.Know q :=
  M.P_inter_one

/-- (3)/(6): \(Cr(p \land q) \leftrightarrow Cr\,p \land Cr\,q\). -/
theorem Cr_and (p q : PropSet X) :
    M.Certain (p ∩ q) ↔ M.Certain p ∧ M.Certain q :=
  ⟨fun h => ⟨fun _ hx => (h hx).1, fun _ hx => (h hx).2⟩,
    fun ⟨hp, hq⟩ _ hx => ⟨hp hx, hq hx⟩⟩

/-- (4)/(7): \(T(p \land q) \leftrightarrow Tp \land Tq\). -/
theorem T_and (p q : PropSet X) :
    M.Think (p ∩ q) ↔ M.Think p ∧ M.Think q :=
  ⟨fun h => ⟨fun _ hx => (h hx).1, fun _ hx => (h hx).2⟩,
    fun ⟨hp, hq⟩ _ hx => ⟨hp hx, hq hx⟩⟩

/-- (23) with nonempty \(v_T\): \(T'p \xrightarrow{s} \sim Tp\). -/
theorem Tprime_not_T (p : PropSet X) (hv : M.vT.Nonempty)
    (h : M.DontThink p) : ¬ M.Think p := by
  intro hT
  rcases hv with ⟨x, hx⟩
  exact h (hT hx) hx

/-- (16) with nonempty \(v_T\): \(Cr\,p \xrightarrow{s} \sim T\,\sim p\). -/
theorem Cr_not_T_not (p : PropSet X) (hv : M.vT.Nonempty)
    (h : M.Certain p) : ¬ M.Think (pᶜ) := by
  intro hT
  rcases hv with ⟨x, hx⟩
  exact hT hx (h (M.vT_subset_vCr hx))

/-- (18): \(Tp \xrightarrow{s} T'\,\sim p\). -/
theorem T_Tprime_not (p : PropSet X) (h : M.Think p) :
    M.DontThink (pᶜ) := by
  intro x hx hxT
  exact hx (h hxT)

/-- (30): \(Dp \xrightarrow{s} T'p\). -/
theorem D_Tprime (p : PropSet X) (h : M.Doubt p) : M.DontThink p := by
  intro x hx hxT
  exact h hx (M.vT_subset_vD hxT)

/-- (22): \(T'p \land T'q \xrightarrow{s} T'(p \lor q)\). -/
theorem Tprime_or (p q : PropSet X)
    (hp : M.DontThink p) (hq : M.DontThink q) : M.DontThink (p ∪ q) := by
  intro x hx
  cases hx with
  | inl h => exact hp h
  | inr h => exact hq h

/-- (11): \(K'(p,q) \xrightarrow{s} \sim Kp\). -/
theorem Kprime_not_K (p q : PropSet X)
    (h : M.DontKnowWhether p q) : ¬ M.Know p := by
  intro hk
  rcases h with ⟨hdisj, _, _, hqpos⟩
  have : M.P q = 0 := M.P_one_disjoint hk hdisj
  linarith

/-- (26): \(B'p \xrightarrow{s} T\,\sim p\). -/
theorem Bprime_T_not (p : PropSet X) (h : M.DontBelieve p) :
    M.Think (pᶜ) := by
  intro x hx
  have : x ∈ M.vB := M.vT_subset_vB hx
  have : x ∉ p := fun hp => h hp this
  exact this

/-- (48)-style gladness: \(Gp \xrightarrow{s} Kp \lor Tp\). -/
theorem G_Know_or_Think (M : GladModel X)
    (p : PropSet X) (h : M.Glad p) : M.Know p ∨ M.Think p := by
  cases h with
  | inl hT => exact Or.inr hT
  | inr h => exact Or.inl h.2

end SemImp

end MotCalc
end Actions
