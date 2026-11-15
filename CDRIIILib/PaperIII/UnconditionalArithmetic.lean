/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.Defs
public import CDRIIIArithmetic.Dense

/-! # The exact arithmetic input of CDR Paper III, with its proof

The two predicates have the same quantifiers and coordinate inequalities.
The provider assembles the squarefree cap theorem (H1), four-square caps (H2),
and the square-part reduction. Its Siegel constant is ineffective.
-/

@[expose] public section

namespace CDRBicolour.PaperIII

/-- Every prescribed sufficiently large radius, including square factors. -/
theorem threeSquaresDense_verified : ThreeSquaresDense :=
  ThreeSquares.threeSquaresDense

end CDRBicolour.PaperIII
