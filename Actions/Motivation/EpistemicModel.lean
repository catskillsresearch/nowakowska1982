/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Epistemic model (§2.2.4)

Speaker-world sixtuplet \(\langle X, P, v_T, v_B, v_{Cr}, v_D \rangle\).
-/

namespace Actions
namespace MotCalc

abbrev PropSet (X : Type*) := Set X

/-- Epistemic part of the §2.2.4 model with
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

end EpistemicModel

end MotCalc
end Actions
