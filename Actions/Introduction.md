# Introduction

<!-- Exception: root Actions.svg lives here (not in Actions.md) so the overview
     diagram appears under Introduction rather than above the TOC. -->
@import "../Actions.svg" {code_block=false, caption="Theory of Actions"}

This report formalizes Maria Nowakowska's *A Formal Theory of Actions:
Syntax and Semantics of Behaviour* [@Nowakowska82], building on her earlier
treatments in [@Nowakowska73a; @Nowakowska73b]. The paper presents behaviour as a language of actions with a semantics of time-results, then studies attainability, motivational consistency, organization, and automata.

The Lean 4 library `Actions` (toolchain and Mathlib `v4.36.0-rc2`) checks
definitions, lemmas, and examples for the mathematical core of §§2, 4, 7, and
13. Brief mathematical English recaps sit beside the Lean; other prose without
checked mathematics appears as short AI summaries only.
