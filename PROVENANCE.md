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

**This repository is submitted to Palomar on its own**, for the Nowakowska
action-theory development alone, following the same Challenge / Solution /
`comparator.json` / `formalization.yaml` pattern as
[`catskillsresearch/scott1980`](https://github.com/catskillsresearch/scott1980)
and [`catskillsresearch/scott1964`](https://github.com/catskillsresearch/scott1964).
Palomar registration ID is pending (`formalization.yaml` / `comparator.json`
still say TBD).

## Compared claims

Packaging follows DomainTheory / scott1980: `comparator.json` names library
`Actions.*` declarations once; `Challenge.lean` is a Mathlib-only / `Challenge.*`
mirror of that API; `Solution.lean` imports the sorry-free `Actions/` library.

The Comparator selects **every theorem that is a sink** in the theorems-only
dependency graph (`docs/dependency_graph_theorems.svg`: nodes with no
successor, including isolates), plus the automaton realization
`toActionSystem.L`, and three clinical definition abbreviations. Headline sinks
include:

1. **113 conflict patterns** (`conflictPattern_card`) — novel machine-checked
   count of labeled four-motive conflict types; the 1982 paper states 113
   without exhibiting the enumeration.
2. **Automaton realization** (`toActionSystem.L`) — novel machine-checked
   equality of the induced sixtuplet language with the automaton language;
   1982 §13 states the reading without a formal identification.
3. **Arrow dictatorial core** (`ArrowPostulates2.impossibility_dictatorial_core`)
   — pure scale dictators fail the packaged two-scale Arrow postulates;
   clinical abbreviations `CompulsiveOrHedonistic`, `BlindObedience`, and
   `NeuroticAllOrNothing` are disclosed library packaging, not new
   psychological theorems.
4. **MotCalc sample** (`SampledSemImp.epistemicModel`) — sampled §2.1.4
   semantic-implication rules validated on the §2.2.4 epistemic model; not a
   full 79-rule calculus.
5. **Positive promise CF** (`PromiseClosed.isContextFree`) — novel
   reconstruction of 1973 Theorem 1 / 1982 §7, with classical Ch. 3
   regular⇒CF and CF∩regular closures as named hypotheses.
6. **Offense CF** (`OffenseClosed.isContextFree`) — novel reconstruction of
   1973 Theorem 4 / 1982 §7 under the same Ch. 3 hypotheses.

Further sinks cover Prax / EffortDominated, verbal embedding and $\psi$,
promise bridges, scale-dictator / clinical packaging lemmas, automaton
plumbing, and the toy-world checks. Full Comparator name lists are in
`comparator.json`.

## Library beyond Comparator

The sorry-free development lives under `Actions/`. Intermediate theorems that
still have successors in the theorems-only graph remain library-only unless
named in `comparator.json`.

No project-defined axioms are introduced. Compared proofs use only
`propext`, `Quot.sound`, and `Classical.choice`, as disclosed in
`comparator.json`.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
