# Introduction

<!-- Exception: root Actions.svg lives here (not in Actions.md) so the overview
     diagram appears under Introduction rather than above the TOC. -->
@import "../Actions.svg" {code_block=false, caption="Actions: Theory of Actions"}

This report formalizes Maria Nowakowska's *A Formal Theory of Actions:
Syntax and Semantics of Behaviour* [@Nowakowska82], building on her earlier
treatments in [@Nowakowska73a; @Nowakowska73b]. The paper presents behaviour as a language of actions with a semantics of time-results, then studies attainability, motivational consistency, organization, and automata.

The Lean 4 library `Actions` (toolchain and Mathlib `v4.36.0-rc2`) checks
definitions, lemmas, and examples for the mathematical core of §§2, 4–7, and
13, drawing MotCalc and promise-CF proofs from scanned 1973 ranges
(§§2.1.4, 2.2.4, 5.1–5.3). Beside each Lean module, mathematical English describes
every definition and states and proves every theorem, with Lean names in
typewriter font in parentheses;
other prose without checked mathematics appears as short AI summaries only.
Compared claims centre on verification of the stated 113 conflict families, a
reachability reading of the §13 automaton bridge, Arrow impossibility in the
finite 2×3 encoding, and machine-checked promise/offense CF reconstructions
from 1973 §5.3.2–5.3.3 with CF ∩ Regular proved in Lean, together with
verbal-embedding duration coherence from §5.1–5.3.
