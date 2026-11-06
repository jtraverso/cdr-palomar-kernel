/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import CDRPreprintsStatements.Spectrum

/-!
# Class-size characterization and exact AAC spectrum

Paper II gives existence at every admissible positive profile. Paper I gives
exact AAC counts above one threshold chosen before the profile and count.
The independent statement modules import only pinned Mathlib and each other.
The three intentional proof holes belong only to this Challenge.
-/

@[expose] public section
namespace CDRBicolour

/-- Paper II, sufficiency at every order. -/
theorem cdr_conjecture : CDRConjecture := by
  sorry

/-- Paper II, Theorem 1: the full class-size characterization. -/
theorem cdr_characterization {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Realises a b c ↔ AdmissibleProfile a b c := by
  sorry

namespace Absorption.Corners

/-- Paper I, Theorem 1: the exact spectrum for every sufficiently large profile. -/
theorem cdr_type_spectrum : ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
    ∀ t : ℕ, AACSpec a b c t ↔ ExactNec a b c t := by
  sorry

end Absorption.Corners
end CDRBicolour
