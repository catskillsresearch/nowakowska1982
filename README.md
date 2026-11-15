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

Sorry-free library under `Actions/`. Palomar packaging matches DomainTheory /
scott1980: `comparator.json` lists library names once; `Challenge.lean` is a
single Mathlib-only statement file; `Solution.lean` imports `Actions/`.

Framing: **reconstruction / verification** of Nowakowska 1982/1973, plus a
Lean proof of classical **CF ∩ Regular** that discharges hypotheses she left
external. Not a new psychological theory; Arrow is the standard impossibility
in her finite 2×3 encoding.

### Compared claims (Comparator) — headline sinks

| Claim | Role |
| --- | --- |
| `Actions.Conflicts.card_conflictFamilies` | Verification: 113 conflict families |
| `Actions.ActionAutomaton.toActionSystem.Attainable_iff_reaches_length` | Faithful reachability realization |
| `Actions.Arrow.arrow_impossibility` | Arrow impossibility in this 2×3 encoding |
| `Actions.ActionSystem.PromiseClosed.isContextFree` | Unconditional promise CF reconstruction |
| `Actions.ActionSystem.OffenseClosed.isContextFree` | Unconditional offense CF (factor-minimal `HatU`) |
| `Language.IsContextFree.inter_regular` | Lean discharge of CF ∩ Regular |
| `Actions.MixedSystem.pi.stringDuration_pi` | Duration homomorphism for `π` |

Full name list is in `comparator.json`.

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
lake build
lake build Challenge Solution
bash scripts/palomar_preflight.sh --no-policy-sync
```
