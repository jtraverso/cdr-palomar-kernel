# Comparator and isolated Challenge repairs

The initial full official preflight at commit
`1d8b9b60e4cb62762fc20ef8781d11d845d09a92` completed the build
(10,021 jobs) and then failed structural comparison at `LowerNec`.
The single-module Challenge reused `CDRBicolour.Realises._proof_1` where
the solution used `CDRBicolour.Absorption.Corners.LowerNec._proof_1`.
The earlier local surface diagnostic normalized proof terms and therefore
missed this structural discrepancy. It was not a full Comparator check.

Separating the independent definitions into three modules compiled locally,
but full preflight run 42221899230 rejected their imports during canonical
Challenge compilation. That compilation exposes only trusted core and
Mathlib dependencies. Its mechanical report is retained here. Both failed
preflights stopped the intake gate; neither sent a Palomar submission.

The current Challenge is again one self-contained file, importing only
pinned Mathlib. Three explicit positivity lemmas preserve the original
auxiliary declaration names and terms: each proves `NeZero (2 + 1)` using
`@Nat.instNeZeroSucc 2`, with the original zero instance and raw numeric
literal fixed explicitly in its type. Scoped instance selection chooses the appropriate
certificate for Realises, the consecutive colouring, and LowerNec. They are
proved facts, not extra axioms. The arithmetic definitions and all three
selected theorem statements retain their original mathematical content.

The unused independent statement modules and their library entry are
removed. No source in the proved solution or its mathematical dependencies
is changed. The Challenge compiles with only the pinned Mathlib dependency
paths, with no sibling project modules on its search path. Its three
intentional proof holes remain only the three selected Challenge theorems.

Local strict export comparison and the complete standard-axiom whitelist
check passed using Lake's own routines on the completed exports. The check
includes the official primitive-constant list. `STRICT_COMPARATOR_LOCAL.json`
and `.log` record the result and hashes; `local-diagnostic/StrictComparator.lean`
is the exact archived diagnostic program (its paths describe the local run).
This is diagnostic evidence only: no independent kernel or isolated build
was performed by that diagnostic. `ISOLATED_CHALLENGE_COMPILE.json` separately
records the successful compile restricted to Mathlib dependency paths. A new full official preflight PASS is
required for this exact commit before intake. The initial package audit and
local-snapshot files remain historical records of their named snapshots.
