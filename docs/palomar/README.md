# Shared submission for Papers I and II

This is a public technical copy of the verified preparation snapshot,
without private Git history. The official public preprint repository is
unchanged. No Palomar registration is asserted here.

## Local outcome

The local verification passed: 49 finite witnesses, exact preservation of the
1,203,132 unordered table entries, twenty matching statement declarations and
definitions, and twelve axiom queries with only `propext`, `Classical.choice`
and `Quot.sound`. These include all three selected results. The 1,185 contained
dependency source files match the local cache sources. The eight protected
mathematical source files remain unchanged from the published baseline.
See those reports under `local-snapshot/`. They are historical records of
the verified preparation snapshot, not claims about a later CI execution.
`PACKAGE_AUDIT.json` separately checks the byte-for-byte source transfer.
The verification reused unchanged dependency objects; it is not a fresh build
of every dependency and it is not the full Palomar mechanical preflight.

## Statement and proof surface

The root `comparator.json` selects `CDRPreprintsChallenge` and
`CDRPreprintsSolution` and the following three declarations:

1. `CDRBicolour.cdr_conjecture`: every admissible positive profile is realized.
2. `CDRBicolour.cdr_characterization`: realization is equivalent to admissibility.
3. `CDRBicolour.Absorption.Corners.cdr_type_spectrum`: an exact AAC count is
   realized if and only if the two arithmetic tests hold, after a single
   threshold chosen before the profile and the requested count.

The first two declarations are Paper II's main theorem. The third is Paper I's
main theorem. Additional prescriptions remain in the library but are not part
of this compared set. The original constructions and hypotheses are retained.

## Finite certificates

The public preprint's mathematical baseline is
`76431935a1d61dbd7d512f32c941e37de38f6ba0`. Its all-order declarations depend on
49 native decision certificates. This branch re-encodes the same off-diagonal
table entries as natural-number data and checks the table laws using kernel
reduction. The maximum order is 487. No existence hypothesis is substituted
for a certificate, and the statement of the CDR theorem is unchanged.

`tools/palomar_tables.py` reads the bundled `data/archived_tables.json`,
extracted from that immutable baseline. No private Git history is required. Small tables use natural-number arrays. The other certificates use
balanced comparisons or packed natural-number rows with a balanced row selector.
Individual row certificates bound kernel memory usage. The largest tables are
noncomputable data definitions: this suppresses executable code generation,
while their transparent mathematical values remain available to the kernel.
`CDRBicolour/Base/KernelTable.lean` converts Boolean row checks to the existing
`realises_of_table` constructor. Bounded-range lemmas assemble the rows
symbolically, without hundreds of dependent case splits. Packed entry lookup
uses natural-number bit shifting and remainder, both checked by the kernel.

For a row of order n, take w=(n−1).bit_length() and store
R_x=Σ_y T(x,y)·2^(w·y). An entry is extracted as
(R_x shifted right by w·y) modulo 2^w. The source comparison checks the
extracted entries against the archived table. Independently, the Lean proof
checks the laws of the extracted table before constructing the Steiner system.

The generated values are untrusted inputs to the proof: an incorrect table
cannot pass the formal table-law checks. The generator is not an axiom or an
oracle. The retained local certificate records include source and object hashes,
exit status, elapsed time and compiler output for all 49 successful checks
under `local-snapshot/kernel-certificates/`. Development attempts remain in
the private repository and are not part of this clean technical copy.

## Dependencies and reproducibility

The contained dependency sources come from the already published shared
archive, SHA-256
`20bdbe78c88b2ebdd44daa7fe15355ce121430b0bd6e85e13951edc60472f5c9`.
`DEPENDENCY_SOURCES.json` records their individual hashes. All 1,185 vendored
Lean files already had module headers and satisfy the 10,000-line limit.
The main project's diagnostic modules are adapted to the same header rule;
generator fragments are named `.lean.inc` to distinguish them from modules.

The local verification uses copied compiled objects for unchanged dependencies
and recompiles the changed proof certificates and affected assembly modules.
This is an incremental verification, not a fresh build of every dependency.
The Palomar mechanical preflight is a separate validation step.

The two source papers are independently identifiable through their DOIs:

- Paper I: https://doi.org/10.5281/zenodo.23987251
- Paper II: https://doi.org/10.5281/zenodo.23987256

## Submission gates

Before intake, obtain a passing full mechanical preflight at the exact
public commit and Comparator configuration. Local verification alone does
not satisfy that gate. The author's relationship is responsible author and maintainer.
Registration requires presenting the resulting review to the author and the
author's subsequent instruction to register.

The authoritative requirements are
https://palomar-registry.org/how-to-submit and
https://submit.palomar-registry.org/llms.txt.
