# The Colbourn–Dinitz–Rosa conjecture and the exact block-type spectrum

Lean sources for two papers by Juan Pablo Traverso Gianini:

- [Paper I: the exact block-type spectrum](https://doi.org/10.5281/zenodo.23987251),
  for all sufficiently large admissible profiles, via typed absorption.
- [Paper II: a proof of the Colbourn–Dinitz–Rosa conjecture](https://doi.org/10.5281/zenodo.23987256),
  characterizing realizable positive class sizes at every order.

The official publication repository is
[cdr-steiner-preprints](https://github.com/jtraverso/cdr-steiner-preprints).
This public technical repository prepares one shared Palomar submission.
It contains no private development history. Its certificate conversion and
submission files do not alter the published preprint freeze.

For positive integers a,b,c, with n=a+b+c, a strictly 3-bicolored Steiner triple
system with those class sizes exists exactly when n is 1 or 3 modulo 6,
a²+b²+c²−ab−ac−bc=n, and no two class sizes are both 2.
The spectrum theorem additionally characterizes each attainable AAC block count
by the explicit predicate `ExactNec` for all sufficiently large profiles.

## Compared results

| Paper | Declaration |
|---|---|
| II, sufficiency | `CDRBicolour.cdr_conjecture` |
| II, equivalence | `CDRBicolour.cdr_characterization` |
| I, exact spectrum | `CDRBicolour.Absorption.Corners.cdr_type_spectrum` |

`CDRPreprintsChallenge.lean` states the three results independently, importing
only Mathlib. `CDRPreprintsSolution.lean` imports their proofs.
`comparator.json` permits only `propext`, `Classical.choice`, and `Quot.sound`.
The current evidence and any remaining validation gates are described in
[the submission guide](docs/palomar/README.md).

Local verification passed: all 49 finite witnesses compile without native
decision certificates; all three selected results and all twelve queried
library endpoints use only the three standard axioms. The independent
statement surface matches twenty declarations and definitions. See
[the verification record](docs/palomar/local-snapshot/LOCAL_VERIFICATION.json).

## Build

The project pins Lean 4.35.0-rc3 and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. Mathematical dependency sources
are contained under `vendor/`; the manifest uses repository-relative paths.

```text
lake build CDRPreprintsChallenge CDRPreprintsSolution
lake env lean checks/AxiomsPalomar.lean
lake comparator --config comparator.json
```

The carried-forward local verification reused compiled dependencies; its
logs are not a substitute for Palomar's complete mechanical preflight.
The sandboxed Comparator command requires Linux; the pinned workflow is
provided in `.github/workflows/palomar-preflight.yml`.
Consult `docs/palomar` for the evidence and its precise scope. Recheck the
49 tables with `python tools/palomar_table_provenance.py`; this requires only
the public source and bundled data, with no private Git history.

## License

Lean code is Apache-2.0; see [LICENSE](LICENSE). Vendored sources retain their
upstream licenses and attribution. Published manuscripts and original figures
are CC BY 4.0 in the official publication repository.
