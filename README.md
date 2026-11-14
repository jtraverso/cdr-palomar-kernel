# CDR Paper III: prescribed block types and abundance

Lean source package for **Prescribed block types and abundance in bicolored
Steiner triple systems**, Juan Pablo Traverso Gianini, preprint 1.0.

Paper and companion: <https://doi.org/10.5281/zenodo.24201563>.
Official series repository:
<https://github.com/jtraverso/cdr-steiner-preprints/tree/main/preprints/PAPER_III>.

This technical branch contains the new proofs for CDR III and the interfaces
for one Palomar submission. Registered developments are pinned Lake
dependencies, rather than copies presented as new formalizations. The published
paper, its source freeze and CDR IV research remain unchanged.

## Compared results

| Paper result | Lean declaration | Scope |
|---|---|---|
| Theorem 1.1 | `CDRBicolour.KBicolor.kbicolour_completion_types_exact` | Exact interior type matrix and completion of a sparse prescribed packing, for fixed k >= 3. |
| Theorem 1.2 | `CDRBicolour.KBicolor.optimal_prescribed_type_count_of_three_le` | Uniform optimal leading coefficient 1/6 in the logarithmic count for each prescribed interior matrix. |
| Theorem 1.3 | `CDRBicolour.KBicolor.kbicolour_types_exact_many_pasch_counts` | Any fixed number of realizations with the same exact matrix and distinct Pasch counts. |
| Theorem 1.4 | `CDRBicolour.PaperIII.bicolourable_eventually_unconditional` | Eventual existence for every fixed k >= 4; in particular CDR Conjectures 3.5 and 3.6 for large orders. |

The first three results require the stated positive class and type margins.
They do not settle the general boundary spectrum. The counting theorem does
not estimate a second-order term; the Pasch theorem gives distinct counts,
not arbitrary prescribed values. The arithmetic threshold in Theorem 1.4 is
ineffective because its proved analytic input uses Siegel's theorem.

`CDRIIIChallenge.lean` is an independent Mathlib-only statement surface.
`CDRIIISolution.lean` imports the proved declarations and never imports the
Challenge. `cdr-iii-comparator.json` names all four theorems, with no replaceable
definition holes. The 25 concrete helper definitions are independently checked
against the published freeze with `pp.all`. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. The Challenge contains four intentional proof holes; Solution
proofs must contain none.

## Dependencies and verification

See [PROVENANCE.md](PROVENANCE.md) for immutable dependency commits and the two
new arithmetic adapters. The previous published freeze passed its source-bound
reconstruction and endpoint axiom audits. Those reports establish the published
freeze; they are not a verification report for this repackaged commit.

No complete local reconstruction is repeated for this submission. Local work
checks the statement surface and inspects the already compiled freeze. The
official Palomar full mechanical preflight must separately pass for the exact
new commit before intake. Its result and the later Palomar review must not be
inferred from the older freeze.

```text
lake build CDRIIIChallenge CDRIIISolution
```

The workflow `.github/workflows/palomar-preflight.yml` calls Palomar's complete
reusable workflow at a fixed pipeline commit. Registration is separate from
submission and requires the author's instruction after the private review.

Original Lean code uses Apache-2.0. Each external dependency retains its own
license and attribution. The manuscripts and original figures are CC BY 4.0.

