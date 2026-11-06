# Comparator representation repair

The full official preflight at commit
`1d8b9b60e4cb62762fc20ef8781d11d845d09a92`
completed the build successfully (10,021 jobs), then failed structural
comparison at `CDRBicolour.Absorption.Corners.LowerNec`:
[run 42198414851](https://github.com/jtraverso/cdr-palomar-kernel/actions/runs/42198414851).
The automatic intake gate stopped; no submission was sent.

The single-module Challenge reused `CDRBicolour.Realises._proof_1` where
the solution's separate module referred to
`CDRBicolour.Absorption.Corners.LowerNec._proof_1`. The earlier local
surface diagnostic normalized proof terms and therefore did not detect
this structural discrepancy. It was not a full Comparator check.

The independent statement is separated into Basic, Colours, and Spectrum
modules, importing only pinned Mathlib and each other. They do not import
the solution. The three modules and the Challenge compiled locally. The
subsequent strict export comparison has no recorded outcome yet; this
note makes no claim of a corrected Comparator PASS.

All proved solution sources, dependencies, three theorem statements,
mathematical hypotheses, and the permitted axiom set are unchanged.
Basic is copied from the original statement layer, including its Mathlib
imports. The three intentional proof holes remain only in Challenge.

The original package audit and local-snapshot records refer to the initial
preparation snapshot and are retained as historical evidence. This repaired
commit requires its own full official preflight PASS before intake. The
workflow now also starts on relevant main-branch pushes, so the corrected
commit can be checked without access to the author's local machine.
