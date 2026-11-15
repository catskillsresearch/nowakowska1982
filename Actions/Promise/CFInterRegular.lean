/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic

@[expose] public section

/-!
# Context-free ∩ regular is context-free (Bar-Hillel product construction)

Given a context-free grammar `g` over `T` and a DFA `M` over `T` with finitely
many states `σ`, we build the product grammar `BarHillel.interGrammar g M`
whose nonterminals are a fresh start symbol together with triples
`(A, p, q) : g.NT × σ × σ` ("`A` derives a word driving `M` from `p` to `q`").

The construction works on arbitrary grammar rules (no normal form): a rule
`A → X₁ … Xₖ` of `g` is lifted along every state path `p = q₀, q₁, …, qₖ = q`,
replacing a nonterminal `Xᵢ = B` by `(B, qᵢ₋₁, qᵢ)` and keeping a terminal
`Xᵢ = a` only when `M.step qᵢ₋₁ a = qᵢ`.

## Main results

* `Actions.BarHillel.language_interGrammar`:
  `(interGrammar g M).language = g.language ⊓ M.accepts`.
* `Language.IsContextFree.inter_regular`: if `L` is context-free and `R` is
  regular then `L ⊓ R` is context-free.
* `Language.IsContextFree.regular_inter`: the symmetric statement.
-/

open scoped Computability

namespace Actions
namespace BarHillel

variable {T : Type*} {σ : Type}

/-- Nonterminals of the product grammar: a fresh start symbol `none`, and
triples `some (A, p, q)` of a nonterminal of `g` and two DFA states. -/
abbrev NT (g : ContextFreeGrammar T) (σ : Type) : Type :=
  Option (g.NT × σ × σ)

variable (g : ContextFreeGrammar T) (M : DFA T σ)

/-- `Lifts g M p q u u'`: the sentential form `u'` of the product grammar is a
lift of the sentential form `u` of `g` along a state path of `M` from `p` to
`q`. Terminals are kept and advance the state by `M.step`; a nonterminal `A`
is annotated with the states before and after it. -/
inductive Lifts : σ → σ → List (Symbol T g.NT) → List (Symbol T (NT g σ)) → Prop
  | nil (p : σ) : Lifts p p [] []
  | terminal {p q : σ} (a : T) {u : List (Symbol T g.NT)}
      {u' : List (Symbol T (NT g σ))} (h : Lifts (M.step p a) q u u') :
      Lifts p q (Symbol.terminal a :: u) (Symbol.terminal a :: u')
  | nonterminal {p q : σ} (A : g.NT) (m : σ) {u : List (Symbol T g.NT)}
      {u' : List (Symbol T (NT g σ))} (h : Lifts m q u u') :
      Lifts p q (Symbol.nonterminal A :: u) (Symbol.nonterminal (some (A, p, m)) :: u')

variable {g M}

namespace Lifts

/-- Lifts concatenate along a shared intermediate state. -/
theorem append {p m q : σ} {x y : List (Symbol T g.NT)}
    {x' y' : List (Symbol T (NT g σ))}
    (h₁ : Lifts g M p m x x') (h₂ : Lifts g M m q y y') :
    Lifts g M p q (x ++ y) (x' ++ y') := by
  induction h₁ with
  | nil p => simpa using h₂
  | terminal a _ ih => exact .terminal a (ih h₂)
  | nonterminal A m _ ih => exact .nonterminal A m (ih h₂)

/-- Splitting a lift along a decomposition of the lifted (product) side. -/
theorem of_append_right {p q : σ} {u : List (Symbol T g.NT)}
    {x' y' : List (Symbol T (NT g σ))}
    (h : Lifts g M p q u (x' ++ y')) :
    ∃ x y m, u = x ++ y ∧ Lifts g M p m x x' ∧ Lifts g M m q y y' := by
  induction x' generalizing p u with
  | nil => exact ⟨[], u, p, rfl, .nil p, h⟩
  | cons s x' ih =>
    rw [List.cons_append] at h
    cases h with
    | terminal a h =>
      obtain ⟨x, y, m, rfl, hx, hy⟩ := ih h
      exact ⟨.terminal a :: x, y, m, rfl, .terminal a hx, hy⟩
    | nonterminal A m₀ h =>
      obtain ⟨x, y, m, rfl, hx, hy⟩ := ih h
      exact ⟨.nonterminal A :: x, y, m, rfl, .nonterminal A m₀ hx, hy⟩

/-- Splitting a lift along a decomposition of the base (`g`) side. -/
theorem of_append_left {p q : σ} {x y : List (Symbol T g.NT)}
    {v' : List (Symbol T (NT g σ))}
    (h : Lifts g M p q (x ++ y) v') :
    ∃ x' y' m, v' = x' ++ y' ∧ Lifts g M p m x x' ∧ Lifts g M m q y y' := by
  induction x generalizing p v' with
  | nil => exact ⟨[], v', p, rfl, .nil p, h⟩
  | cons s x ih =>
    rw [List.cons_append] at h
    cases h with
    | terminal a h =>
      obtain ⟨x', y', m, rfl, hx, hy⟩ := ih h
      exact ⟨.terminal a :: x', y', m, rfl, .terminal a hx, hy⟩
    | nonterminal A m₀ h =>
      obtain ⟨x', y', m, rfl, hx, hy⟩ := ih h
      exact ⟨.nonterminal (some (A, p, m₀)) :: x', y', m, rfl, .nonterminal A m₀ hx, hy⟩

/-- The canonical lift of a single nonterminal. -/
theorem singleton (A : g.NT) (p q : σ) :
    Lifts g M p q [.nonterminal A] [.nonterminal (some (A, p, q))] :=
  .nonterminal A q (.nil q)

/-- Only a matching triple lifts to a single product nonterminal. -/
theorem of_singleton_right {p q : σ} {u : List (Symbol T g.NT)} {n : NT g σ}
    (h : Lifts g M p q u [.nonterminal n]) :
    ∃ A, n = some (A, p, q) ∧ u = [.nonterminal A] := by
  cases h with
  | nonterminal A m h =>
    cases h
    exact ⟨A, rfl, rfl⟩

/-- A single nonterminal lifts only to its annotated triple. -/
theorem of_singleton_left {p q : σ} {A : g.NT} {u' : List (Symbol T (NT g σ))}
    (h : Lifts g M p q [.nonterminal A] u') :
    u' = [.nonterminal (some (A, p, q))] := by
  cases h with
  | nonterminal A m h =>
    cases h
    rfl

/-- A terminal word lifts to itself along the run of `M`. -/
theorem terminals (p : σ) (w : List T) :
    Lifts g M p (M.evalFrom p w) (w.map Symbol.terminal) (w.map Symbol.terminal) := by
  induction w generalizing p with
  | nil => exact .nil p
  | cons a w ih =>
    rw [List.map_cons, DFA.evalFrom_cons]
    exact .terminal a (ih _)

/-- Anything lifting to a terminal word is that word, and the state path is
the run of `M`. -/
theorem of_terminals_right {p q : σ} {v : List (Symbol T g.NT)} {w : List T}
    (h : Lifts g M p q v (w.map Symbol.terminal)) :
    v = w.map Symbol.terminal ∧ M.evalFrom p w = q := by
  induction w generalizing p v with
  | nil =>
    cases h
    exact ⟨rfl, rfl⟩
  | cons a w ih =>
    rw [List.map_cons] at h
    cases h with
    | terminal a h =>
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

/-- For a fixed base form and start state there are finitely many lifts. -/
theorem finite [Finite σ] (u : List (Symbol T g.NT)) (p : σ) :
    {x : σ × List (Symbol T (NT g σ)) | Lifts g M p x.1 u x.2}.Finite := by
  induction u generalizing p with
  | nil =>
    refine (Set.finite_singleton (p, [])).subset ?_
    rintro ⟨q, u'⟩ (h : Lifts g M p q [] u')
    cases h
    rfl
  | cons s u ih =>
    cases s with
    | terminal a =>
      refine ((ih (M.step p a)).image
        (fun x => (x.1, Symbol.terminal a :: x.2))).subset ?_
      rintro ⟨q, u'⟩ (h : Lifts g M p q _ u')
      cases h with
      | terminal _ h => exact ⟨(q, _), h, rfl⟩
    | nonterminal A =>
      refine (Set.finite_iUnion fun m : σ => (ih m).image
        (fun x => (x.1, Symbol.nonterminal (some (A, p, m)) :: x.2))).subset ?_
      rintro ⟨q, u'⟩ (h : Lifts g M p q _ u')
      cases h with
      | nonterminal _ m h => exact Set.mem_iUnion.2 ⟨m, (q, _), h, rfl⟩

end Lifts

variable (g M)

/-- Lifted copies of the rules of `g`: `(A, p, q) → u'` whenever `A → u` is a
rule of `g` and `u'` lifts `u` along a state path from `p` to `q`. -/
def liftedRules : Set (ContextFreeRule T (NT g σ)) :=
  {r' | ∃ r ∈ g.rules, ∃ p q : σ,
    r'.input = some (r.input, p, q) ∧ Lifts g M p q r.output r'.output}

/-- Start rules: the fresh start symbol rewrites to `(S, start, q)` for each
accepting state `q`. -/
def startRules : Set (ContextFreeRule T (NT g σ)) :=
  {r' | ∃ q ∈ M.accept,
    r' = ⟨none, [Symbol.nonterminal (some (g.initial, M.start, q))]⟩}

theorem finite_liftedRules [Finite σ] : (liftedRules g M).Finite := by
  have hsub : liftedRules g M ⊆ ⋃ r ∈ (g.rules : Set (ContextFreeRule T g.NT)),
      ⋃ p : σ, (fun x : σ × List (Symbol T (NT g σ)) =>
        (⟨some (r.input, p, x.1), x.2⟩ : ContextFreeRule T (NT g σ))) ''
          {x | Lifts g M p x.1 r.output x.2} := by
    rintro ⟨n, o⟩ ⟨r, hr, p, q, hn, ho⟩
    dsimp only at hn ho
    subst hn
    exact Set.mem_biUnion hr (Set.mem_iUnion.2 ⟨p, (q, o), ho, rfl⟩)
  exact (Set.Finite.biUnion g.rules.finite_toSet fun r _ =>
    Set.finite_iUnion fun p => (Lifts.finite r.output p).image _).subset hsub

theorem finite_startRules [Finite σ] : (startRules g M).Finite := by
  refine ((Set.toFinite M.accept).image (fun q : σ =>
    (⟨none, [Symbol.nonterminal (some (g.initial, M.start, q))]⟩ :
      ContextFreeRule T (NT g σ)))).subset ?_
  rintro r' ⟨q, hq, rfl⟩
  exact ⟨q, hq, rfl⟩

/-- The Bar-Hillel product of a context-free grammar and a finite DFA. -/
noncomputable def interGrammar [Finite σ] : ContextFreeGrammar T where
  NT := NT g σ
  initial := none
  rules := ((finite_liftedRules g M).union (finite_startRules g M)).toFinset

variable {g M}

theorem mem_rules_interGrammar [Finite σ] {r' : ContextFreeRule T (NT g σ)} :
    r' ∈ (interGrammar g M).rules ↔ r' ∈ liftedRules g M ∨ r' ∈ startRules g M := by
  change r' ∈ ((finite_liftedRules g M).union (finite_startRules g M)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset, Set.mem_union]

/-- A rule rewriting a single nonterminal has that nonterminal as its input
and yields exactly the rule's output. -/
theorem rewrites_singleton {N : Type*} {r : ContextFreeRule T N} {n : N}
    {v : List (Symbol T N)} (h : r.Rewrites [Symbol.nonterminal n] v) :
    r.input = n ∧ v = r.output := by
  obtain ⟨x, y, hxy, rfl⟩ := h.exists_parts
  cases x with
  | nil =>
    cases y with
    | nil => simpa [eq_comm] using hxy
    | cons b y => simp at hxy
  | cons a x => simp at hxy

namespace Lifts

/-- One product-grammar step projects to one `g` step. -/
theorem produces_sound [Finite σ] {p q : σ} {u : List (Symbol T g.NT)}
    {u' v' : List (Symbol T (NT g σ))} (h : Lifts g M p q u u')
    (hp : (interGrammar g M).Produces u' v') :
    ∃ v, Lifts g M p q v v' ∧ g.Produces u v := by
  obtain ⟨r', hr', hrw⟩ := hp
  obtain ⟨x', y', rfl, rfl⟩ := hrw.exists_parts
  obtain ⟨xm, y, m₂, rfl, hxm, hy⟩ := h.of_append_right
  obtain ⟨x, mid, m₁, rfl, hx, hmid⟩ := hxm.of_append_right
  obtain ⟨A, hA, rfl⟩ := hmid.of_singleton_right
  rcases mem_rules_interGrammar.1 hr' with ⟨r, hr, p₁, q₁, hin, hout⟩ | ⟨qf, -, rfl⟩
  · rw [hin] at hA
    obtain ⟨rfl, rfl, rfl⟩ : r.input = A ∧ p₁ = m₁ ∧ q₁ = m₂ := by simpa using hA
    exact ⟨x ++ r.output ++ y, (hx.append hout).append hy, r, hr,
      r.rewrites_of_exists_parts x y⟩
  · cases hA

/-- One `g` step lifts to one product-grammar step. -/
theorem produces_complete [Finite σ] {p q : σ} {u v : List (Symbol T g.NT)}
    {v' : List (Symbol T (NT g σ))} (h : Lifts g M p q v v')
    (hp : g.Produces u v) :
    ∃ u', Lifts g M p q u u' ∧ (interGrammar g M).Produces u' v' := by
  obtain ⟨r, hr, hrw⟩ := hp
  obtain ⟨x, y, rfl, rfl⟩ := hrw.exists_parts
  obtain ⟨xo', y', m₂, rfl, hxo, hy⟩ := h.of_append_left
  obtain ⟨x', o', m₁, rfl, hx, ho⟩ := hxo.of_append_left
  refine ⟨x' ++ [Symbol.nonterminal (some (r.input, m₁, m₂))] ++ y',
    (hx.append (Lifts.singleton r.input m₁ m₂)).append hy,
    ⟨some (r.input, m₁, m₂), o'⟩,
    mem_rules_interGrammar.2 (.inl ⟨r, hr, m₁, m₂, rfl, ho⟩), ?_⟩
  exact ContextFreeRule.rewrites_of_exists_parts ⟨some (r.input, m₁, m₂), o'⟩ x' y'

/-- Product-grammar derivations project to `g` derivations. -/
theorem derives_sound [Finite σ] {p q : σ} {u : List (Symbol T g.NT)}
    {u' v' : List (Symbol T (NT g σ))} (h : Lifts g M p q u u')
    (hd : (interGrammar g M).Derives u' v') :
    ∃ v, Lifts g M p q v v' ∧ g.Derives u v := by
  induction hd with
  | refl => exact ⟨u, h, .refl _⟩
  | tail _ hp ih =>
    obtain ⟨v, hv, hd⟩ := ih
    obtain ⟨w, hw, hp'⟩ := hv.produces_sound hp
    exact ⟨w, hw, hd.trans_produces hp'⟩

/-- `g` derivations lift to product-grammar derivations, for any lift of the
target form. -/
theorem derives_complete [Finite σ] {p q : σ} {u v : List (Symbol T g.NT)}
    {v' : List (Symbol T (NT g σ))} (h : Lifts g M p q v v')
    (hd : g.Derives u v) :
    ∃ u', Lifts g M p q u u' ∧ (interGrammar g M).Derives u' v' := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨v', h, .refl _⟩
  | head hp _ ih =>
    obtain ⟨c', hc, hd'⟩ := ih
    obtain ⟨a', ha, hp'⟩ := hc.produces_complete hp
    exact ⟨a', ha, hp'.trans_derives hd'⟩

end Lifts

variable (g M)

/-- The product grammar generates exactly the intersection. -/
theorem language_interGrammar [Finite σ] :
    (interGrammar g M).language = g.language ⊓ M.accepts := by
  ext w
  constructor
  · intro hw
    have hw : (interGrammar g M).Derives [Symbol.nonterminal none]
        (w.map Symbol.terminal) := hw
    rcases hw.eq_or_head with heq | ⟨v', hp, hd⟩
    · cases w <;> simp at heq
    · obtain ⟨r', hr', hrw⟩ := hp
      obtain ⟨hin, rfl⟩ := rewrites_singleton hrw
      rcases mem_rules_interGrammar.1 hr' with
        ⟨r, hr, p₁, q₁, hin', hout⟩ | ⟨qf, hqf, rfl⟩
      · rw [hin] at hin'
        cases hin'
      · obtain ⟨v, hv, hgd⟩ :=
          (Lifts.singleton (M := M) g.initial M.start qf).derives_sound hd
        obtain ⟨rfl, hq⟩ := hv.of_terminals_right
        refine ⟨hgd, ?_⟩
        change M.evalFrom M.start w ∈ M.accept
        rw [hq]
        exact hqf
  · rintro ⟨hg, hM⟩
    have hg : g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := hg
    obtain ⟨u', hu', hd⟩ := (Lifts.terminals (g := g) (M := M) M.start w).derives_complete hg
    obtain rfl := hu'.of_singleton_left
    refine Relation.ReflTransGen.head ⟨⟨none,
      [Symbol.nonterminal (some (g.initial, M.start, M.evalFrom M.start w))]⟩,
      mem_rules_interGrammar.2 (.inr ⟨_, hM, rfl⟩), ?_⟩ hd
    exact ContextFreeRule.Rewrites.input_output

/-! ### The full language over a finite alphabet -/

/-- Rules of the grammar `S → ε | a S` for the full language. -/
def topRules (T : Type*) : Set (ContextFreeRule T Unit) :=
  insert ⟨(), []⟩
    (Set.range fun a : T => ⟨(), [Symbol.terminal a, Symbol.nonterminal ()]⟩)

theorem finite_topRules (T : Type*) [Finite T] : (topRules T).Finite :=
  (Set.finite_range _).insert _

/-- The grammar `S → ε | a S` generating every word over a finite alphabet. -/
noncomputable def topGrammar (T : Type*) [Finite T] : ContextFreeGrammar T where
  NT := Unit
  initial := ()
  rules := (finite_topRules T).toFinset

theorem topGrammar_derives_append [Finite T] (w : List T) :
    (topGrammar T).Derives [Symbol.nonterminal ()]
      (w.map Symbol.terminal ++ [Symbol.nonterminal ()]) := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    have hstep : (topGrammar T).Produces [Symbol.nonterminal ()]
        [Symbol.terminal a, Symbol.nonterminal ()] :=
      ⟨⟨(), [Symbol.terminal a, Symbol.nonterminal ()]⟩,
        (Set.Finite.mem_toFinset _).2 (Set.mem_insert_of_mem _ ⟨a, rfl⟩),
        ContextFreeRule.Rewrites.input_output⟩
    exact hstep.trans_derives (ih.append_left [Symbol.terminal a])

theorem language_topGrammar [Finite T] : (topGrammar T).language = ⊤ := by
  refine eq_top_iff.2 fun w _ => ?_
  have hnil : (topGrammar T).Produces [Symbol.nonterminal ()] [] :=
    ⟨⟨(), []⟩, (Set.Finite.mem_toFinset _).2 (Set.mem_insert _ _),
      ContextFreeRule.Rewrites.input_output⟩
  have hstep := hnil.append_left (w.map Symbol.terminal)
  rw [List.append_nil] at hstep
  exact (topGrammar_derives_append w).trans_produces hstep

end BarHillel
end Actions

namespace Language

variable {T : Type*}

/-- The full language over a finite alphabet is context-free. -/
theorem isContextFree_top [Finite T] : (⊤ : Language T).IsContextFree :=
  ⟨Actions.BarHillel.topGrammar T, Actions.BarHillel.language_topGrammar⟩

/-- **Bar-Hillel**: context-free languages are closed under intersection with
regular languages. -/
theorem IsContextFree.inter_regular {L R : Language T}
    (hL : L.IsContextFree) (hR : R.IsRegular) : (L ⊓ R).IsContextFree := by
  obtain ⟨g, rfl⟩ := hL
  obtain ⟨σ, _, M, rfl⟩ := hR
  exact ⟨Actions.BarHillel.interGrammar g M, Actions.BarHillel.language_interGrammar g M⟩

/-- Symmetric form of `Language.IsContextFree.inter_regular`. -/
theorem IsContextFree.regular_inter {L R : Language T}
    (hR : R.IsRegular) (hL : L.IsContextFree) : (R ⊓ L).IsContextFree := by
  rw [inf_comm]
  exact hL.inter_regular hR

/-- Over a finite alphabet every regular language is context-free. (For an
infinite alphabet this fails: a grammar has finitely many rules, hence mentions
finitely many terminals, while e.g. the set of one-letter words is regular.) -/
theorem IsRegular.isContextFree [Finite T] {R : Language T}
    (hR : R.IsRegular) : R.IsContextFree := by
  have h := isContextFree_top.inter_regular hR
  rwa [top_inf_eq] at h

end Language
