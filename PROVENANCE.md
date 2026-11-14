# Source provenance and scope

The source baseline is the published `CDRIII_Lean_v1.0.zip`, SHA-256
`08dcee5b5d67d00d1f561988e8c716c57c92d250ca54270f3d417429fb52e649`.
The baseline is preserved in the official CDR series repository and Zenodo
record <https://doi.org/10.5281/zenodo.24201563>.

## Registered code is imported

* `jtraverso/cdr-palomar-kernel` at
  `5d1e6fe301e5fc01c92f6145aa34fddfe9c2bd10`: CDR I-II and their auxiliary
  development; PALOMAR-2026-11-07-000002. Its contained dependencies supply,
  among other inputs, the already isolated CountingCone development.
* `jtraverso/physical-typed-absorption` at
  `9d36e80d75d81d9eabbfacd370dc4394b54e3d52`: theorems T and T+ of Triangle
  decompositions III and the Latin/Pasch library. The root dependency selects
  this exact registered version, including for imports reached through CDR I-II.
* `jtraverso/duke-schulze-pillot-ternary` at
  `21575ff924c98165ea1b451f7cbcc27c016ebd3e`: registered DSP v2, including the
  squarefree cap theorem. Its pinned dependencies provide Siegel's theorem,
  the Weil toolkit, Gauss-Legendre, and four-square caps/Jacobi.
* `jtraverso/gale-hoffman-feasibility` at
  `fa52c29c24edf7e9afdb487df3764affd43c51c7`: integral flow feasibility,
  with pinned Baranyai and Dross dependencies.

Every direct Git requirement has a full commit SHA and no `subDir`. Contained
path requirements of the registered CDR kernel stay within that pinned Git
checkout. No local drive path is a submitted dependency.

## What is new here

The `CDRBicolour.KBicolor` modules develop exact prescribed matrices, reserved
circulation exchanges, sparse completion, optimal counting and Latin replacements
that separate Pasch counts while keeping the exact matrix. The `PaperIII`
modules assemble fixed-k existence, flow and cap inputs. `BRIRatio` extends the
bounded inverse to arbitrary fixed positive class margins.

`KBicolor.ResidualLattice` and `KBicolor.ResidualHinge` are explicitly
generalizations of the three-class `CDRBicolour.Absorption` arguments imported
from the registered kernel. Their k-class predicates, quotient relations,
next-class choices and constants are new interfaces used by the new completion
proof. Their similarity to the earlier proofs is intentional reuse of that
argument, not a claim to have independently formalized the imported results.

Two short arithmetic integration modules remain:

* `CDRIIIArithmetic.Rotation`: quaternion rotations from the registered
  four-square cap statement. Its duplicate `FourSquaresDense` definition is
  replaced by an abbreviation of `FourSquaresCaps.FourSquaresDense`.
* `CDRIIIArithmetic.Dense`: combines the imported squarefree cap proof and
  imported four-square cap proof with the square-part reduction already supplied
  by DSP v2. It introduces no analytic assumption.

The old H1/H2 proof copies, `LeanLab/PNTPort`, the vendored `rml` tree, and the
three copied Latin modules are absent from this package. Resource-only changes
to imported absorption sources are also not copied. See
[evidence/SOURCE_EXTRACTION.json](evidence/SOURCE_EXTRACTION.json) for the
baseline-to-package file inventory. An omitted source may still be a genuine
dependency: it is supplied by a pinned upstream project instead of this tree.

