# Source provenance and scope

The source baseline is the published `CDRIII_Lean_v1.0.zip`, SHA-256
`08dcee5b5d67d00d1f561988e8c716c57c92d250ca54270f3d417429fb52e649`.
The baseline is preserved in the official CDR series repository and Zenodo
record <https://doi.org/10.5281/zenodo.24201563>.

## Registered proof sources are imported

The commits in the following list identify the registered proof-source baselines.
Actual Lake pins use configuration-only descendants in the table below. GitHub
comparisons verify that no `.lean` file changed in those descendants. The package
configuration narrows overly broad module claims so unrelated libraries can coexist.

* `jtraverso/cdr-palomar-kernel` at
  `5d1e6fe301e5fc01c92f6145aa34fddfe9c2bd10`: CDR I-II and their auxiliary
  development; PALOMAR-2026-11-07-000002.
* `jtraverso/physical-typed-absorption` at
  `9d36e80d75d81d9eabbfacd370dc4394b54e3d52`: theorems T and T+ of Triangle
  decompositions III and the Latin/Pasch library. Its mathematical sources are
  preserved exactly in the configuration revision selected at the root.
* `jtraverso/duke-schulze-pillot-ternary` at
  `21575ff924c98165ea1b451f7cbcc27c016ebd3e`: registered DSP v2, including the
  squarefree cap theorem. Its pinned dependencies provide Siegel's theorem,
  the Weil toolkit, Gauss-Legendre, and four-square caps/Jacobi.
* `jtraverso/gale-hoffman-feasibility` at
  `fa52c29c24edf7e9afdb487df3764affd43c51c7`: integral flow feasibility,
  with pinned Baranyai and Dross dependencies.

Every Git requirement has a full commit SHA and no `subDir`. The kernel's
transitive path requirements are overridden by the corresponding pinned Git
packages. The sole local path package, `compat/counting-cone`, contains only
import bridges to the registered `counting-steiner-triple-systems` source at
`52fda83038df7442c576e17edffba591db703cb8`. Its four modules contain no definitions
or proofs. A source comparison verifies that the isolated CountingCone bodies
are identical to those originals after reversing the import-prefix rename.
No path dependency lives under `.lake` or points to a local drive directory.
See [evidence/COUNTING_IMPORT_COMPATIBILITY.json](evidence/COUNTING_IMPORT_COMPATIBILITY.json).

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


## Configuration-only dependency revisions

| Repository | Registered proof-source base | Used configuration revision | Changed files |
|---|---|---|---|
| `jtraverso/vizing` | `33b2de836095cf92bc1dec33b6f8787e4036bbc6` | `995a73aa27196ac66f52a3054e6fd6dac3599479` | `lakefile.toml` |
| `jtraverso/dross-fractional-triangle-decomposition` | `7720b7b591e606d5a56f1d935d8be650dcbf6c6f` | `90e04502005b2f3dc7b8207809d08045db8b4068` | `lakefile.toml` |
| `jtraverso/counting-steiner-triple-systems` | `52fda83038df7442c576e17edffba591db703cb8` | `dc8f42dd87157cf9fafacfb382f5d154881105c8` | `lakefile.toml` |
| `jtraverso/physical-typed-absorption` | `9d36e80d75d81d9eabbfacd370dc4394b54e3d52` | `1536d1c75452a135d527d59217adc0408755448b` | `lakefile.toml` |
| `jtraverso/cdr-palomar-kernel` | `5d1e6fe301e5fc01c92f6145aa34fddfe9c2bd10` | `52ef4148441d9cdc5d523ca0c73d076ad66ed831` | `lake-manifest.json`, `lakefile.toml` |

These technical branches leave the registered commits and every repository's main
branch untouched. They are not new registrations of the imported mathematics.
See [the Git source-identity evidence](evidence/DEPENDENCY_CONFIGURATION_ADAPTERS.json).

New CDR III files use the unique `CDRIIILib` module prefix while preserving their
`CDRBicolour` declaration namespaces. All 146 original mathematical source bodies
are unchanged after removing comments and import directives; the relocation and
import map are recorded in [PROJECT_MODULE_RELOCATION.json](evidence/PROJECT_MODULE_RELOCATION.json).
