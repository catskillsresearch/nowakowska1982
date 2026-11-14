# Abstract

We give a Lean 4 / Mathlib formalization that synthesizes Maria Nowakowska's
*A Formal Theory of Actions* [@Nowakowska82] with the parts of *Language of
Motivation and Language of Actions* [@Nowakowska73a] that 1982 cites for
omitted proofs and for the motivational calculus (here: §§2.1.4, 2.2.4, 5.1–5.3).
The library covers the action-system sixtuplet, weak and strong attainability,
Prax / Prax-min, a sampled MotCalc speaker-world model, verbal embedding with
motivational consistency / satisfiability / $\psi(A)$, promise closure,
an automaton reading of the sixtuplet, and Arrow-style choice with clinical
corollary packaging, with a small checked example.

Where 1982 asserts results without a proof or enumeration, we supply
machine-checked arguments: the **113** four-motive conflict types (stated, not
enumerated); the automaton-to-sixtuplet realization (§13 sketch); and the
promise / offense context-free theorems (§7, proofs deferred to [5] = 1973
§5.3), reconstructed with classical Ch. 3 CF∩regular closures as named
hypotheses. MotCalc contributions check sampled §2.1.4 semantic implications
against the §2.2.4 epistemic model rather than new omitted theorems.
