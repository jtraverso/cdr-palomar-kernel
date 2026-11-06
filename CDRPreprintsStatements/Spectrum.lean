/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import CDRPreprintsStatements.Colours

/-! Independent arithmetic tests, in a separate module to preserve the generated
positivity certificates of the proved statement. No solution is imported. -/

@[expose] public section
noncomputable section
open Classical
namespace CDRBicolour

namespace Absorption.Corners
abbrev sz (a b c : ℕ) (X : Fin 3) : ℕ := ![a, b, c] X

/-- The lower-corner arithmetic test, with classes indexed cyclically in Fin 3. -/
def LowerNec (a b c t : ℕ) : Prop :=
  ∃ d q r : Fin 3 → ℕ, (∀ X, r X < sz a b c X) ∧
    (∀ X, (d X : ℤ) = sz a b c X - 1 - sz a b c (X + 1) + 2 * q X) ∧
    (∀ X, sz a b c X * d X + 2 * r X = 2 * (sz a b c (X + 2) * q (X + 2) + r (X + 2))) ∧
    (∀ X, ¬ (d X = 0 ∧ (r X = 1 ∨ r X = 2))) ∧ c * q 2 + r 2 = t

def ExactNec (a b c t : ℕ) : Prop :=
  2 * t ≤ a * (a - 1) ∧ LowerNec a b c t ∧ LowerNec a c b (a * (a - 1) / 2 - t)

/-- A system on the fixed consecutive color classes with exactly t AAC blocks. -/
def AACSpec (a b c t : ℕ) : Prop :=
  ∃ S : STS (Fin (a + b + c)), IsStrictBicolouring S (Prefix.col3 a b c) ∧
    BlockTypes.typeCount S (Prefix.col3 a b c) 0 2 = t


end Absorption.Corners
end CDRBicolour
