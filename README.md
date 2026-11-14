# nowakowska1982

Lean 4 / Mathlib formalization of Maria Nowakowska's **1982** *A Formal Theory
of Actions: Syntax and Semantics of Behaviour* (published 1983), with MotCalc
and promise-CF material from *Language of Motivation and Language of Actions*
(**1973**, §§2.1.4, 2.2.4, 5.1–5.3). Author: Lars Warren Ericson.

Standalone package. This repo is prepared for submission to
[Palomar](https://palomar-registry.org/about) on its own (see
`PROVENANCE.md`). **Palomar registration ID is pending.**

Toolchain: Lean / Mathlib **v4.36.0-rc2** (`lean-toolchain`, `lakefile.toml`).

Original Lean and author-written docs are Apache-2.0. Source PDFs and
transcriptions are **not** under that license; see `NOTICE` and
`sources/README.md`.

Maria Nowakowska did not review or endorse this formalization.

## Status

Sorry-free library under `Actions/` (sixtuplet, attainability, Prax, MotCalc
sample, verbal embedding / motivational consistency / satisfiability /
$\psi(A)$, promise closure, automaton reading, Arrow packaging, toy world).
`Challenge.lean` / `Solution.lean` / `comparator.json` expose the compared
family for Palomar Comparator: **all theorems-only dependency-graph sinks**
(no successor, including isolates; see `docs/dependency_graph_theorems.svg`),
plus `toActionSystem.L` and three clinical Arrow abbrevs.

### Compared claims (Comparator) — headline sinks

| Claim | Role |
| --- | --- |
| `conflictPattern_card` | Novel: 113 labeled four-motive conflict patterns |
| `toActionSystem.L` | Novel: automaton language = induced sixtuplet $L$ |
| `ArrowPostulates2.impossibility_dictatorial_core` | Dictatorial-core inconsistency (+ clinical abbrevs) |
| `SampledSemImp.epistemicModel` | MotCalc sample on §2.2.4 epistemic model |
| `PromiseClosed.isContextFree` | Novel reconstruction of 1973 Thm 1 / 1982 §7 |
| `OffenseClosed.isContextFree` | Novel reconstruction of 1973 Thm 4 / 1982 §7 |

Full name list (61 theorems × Challenge/Solution) is in `comparator.json`.
Ch. 3 regular⇒CF and CF∩regular closures are **named hypotheses** on the CF
theorems (not yet in Mathlib).

## Files (Palomar)

| File | Role |
| --- | --- |
| `Actions.pdf` / `arxiv.md` | Narrative report (note tree → TeX/PDF) |
| `Actions/` | Sorry-free formalization |
| `Challenge.lean` | Palomar statement / compared wrappers |
| `Solution.lean` | Palomar solution wrappers (same proofs) |
| `comparator.json` | Comparator theorem and definition names |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `PROVENANCE.md` | Standalone Palomar submission notes |
| `NOTICE` | Apache-2.0 carve-out for source PDFs / OCR |
| `sources/` | Primary PDFs and OCR transcriptions |

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Actions`, `Challenge`, and `Solution`.

Report PDF:

```bash
./scripts/build_arxiv_pdf.sh   # writes Actions.pdf / view.pdf / arxiv.pdf
```
