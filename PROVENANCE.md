# Provenance

This repository is a standalone Lean 4 / Mathlib formalization of Maria
Nowakowska's *A Formal Theory of Actions: Syntax and Semantics of Behaviour*
(chapter dated 1982; published in Gasparski & Airaksinen, *Praxiological
Studies*, 1983), together with the parts of *Language of Motivation and
Language of Actions* (1973) that 1982 cites for omitted proofs and for the
motivational calculus (here: §§2.1.4, 2.2.4, 5.1–5.3). It is not a thin
wrapper and not a reimplementation of an independent formalization.

Maria Nowakowska did not participate in, review, or endorse this
formalization. The Lean development was produced by Lars Warren Ericson
with AI-agent assistance under his direction and review. The source papers
are cited as literature only and are not licensed under this repository's
Apache-2.0 terms (see `NOTICE`).

**This repository is registered with Palomar on its own**, for the Nowakowska
action-theory development alone, following the same Challenge / Solution /
`comparator.json` / `formalization.yaml` pattern as
[`catskillsresearch/scott1980`](https://github.com/catskillsresearch/scott1980)
and [`catskillsresearch/scott1964`](https://github.com/catskillsresearch/scott1964).
Registry entry:
[PALOMAR-2026-11-15-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-11-15-000006&version=1),
version 1.

## Framing

Primary story: **rigorous reconstruction / verification** of Nowakowska
1982/1973, turning impressionistic informal mathematics into
Comparator-locked Lean statements (cf. Suppes’ observation that some of her
expository mathematics is woolly). Secondary story: a Lean/Mathlib-facing
**discharge of classical CF ∩ Regular**, which she only cites externally.

Explicit non-claims: no new psychological theory; no novel Arrow theorem
beyond the finite 2×3 encoding; clinical labels are packaging of postulate
failures; the automaton bridge is infrastructure, not a standalone novelty.

## Compared claims

Packaging follows DomainTheory / scott1980: `comparator.json` names library
`Actions.*` (and one `Language.*`) declarations once; `Challenge.lean` is a
single Mathlib-only statement file (deliberate `sorry` holes); `Solution.lean`
imports the sorry-free `Actions/` library.

Headline compared claims:

1. **`card_conflictFamilies`** — machine-checked verification that there are
   exactly 113 four-motive conflict families (`IsConflictFamily` on
   `Finset (Finset (Fin 4))`), matching her stated 113 via a structural
   bijection to a factored count (not a new combinatorial theorem of ours).
2. **`toActionSystem.Attainable_iff_reaches_length`** — faithful automaton
   bridge: causation is reachability of runs at time `t = length` (supporting
   formalization, not novel dynamics).
3. **`arrow_impossibility` / `arrow_dictator_of_unanimity_IIA`** — standard
   Arrow impossibility in her finite two-scale / three-option score encoding
   (not a new social-choice theorem).
4. **`PromiseClosed.isContextFree` / `OffenseClosed.isContextFree`** —
   reconstruction of 1973 Thm 1 / Thm 4 with factor-minimal `HatU` and infix
   offense envelope; now **unconditional** on classical language hypotheses.
5. **`Language.IsContextFree.inter_regular`** — formalization contribution
   discharging the CF ∩ Regular lemma she left as a black box (beyond her
   text; still useful Mathlib-facing work).
6. **`pi.stringDuration_pi` / timed `Psi.pi_mem_of_motivationalConsistency`** —
   duration homomorphism and utterance-time coherence for verbal embedding.

Supporting sinks (Prax, MotCalc sample, scale-dictator packaging lemmas,
toy-world checks including offense witnesses) remain in `comparator.json`
but are not advertised as headline novelty.

## Library beyond Comparator

The sorry-free development lives under `Actions/`. Intermediate theorems that
still have successors remain library-only unless named in `comparator.json`.

No project-defined axioms are introduced. Compared proofs use only
`propext`, `Quot.sound`, and `Classical.choice`, as disclosed in
`comparator.json`.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
