/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.DukeSquarefreeProof
public import CDRIIIArithmetic.Rotation

/-! # Three squares in arbitrary fixed caps

The squarefree case is H1. For bounded squarefree parts, H2 supplies dense
quaternion rotations, and the established square-part reduction completes
the statement for every sufficiently large integer congruent to 3 modulo 8.
-/

@[expose] public section
namespace ThreeSquares

theorem threeSquaresDense : ThreeSquaresDense :=
  threeSquaresDense_of dukeSquarefree (quaternionRotationsDense_of FourSquaresCaps.fourSquaresDense)

end ThreeSquares
