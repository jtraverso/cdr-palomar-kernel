/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.Ring

/-!
# Colbourn–Dinitz–Rosa: class sizes and exact block-type spectrum

Paper II characterizes the positive class sizes of strictly 3-bicolored Steiner
triple systems at every order. Paper I characterizes the number of AAC blocks
for all sufficiently large admissible profiles. Its threshold is chosen before
the class sizes and before the requested count. The natural-number subtractions
in `ExactNec` are truncated subtractions, as in the published formal statements.

This independent statement surface imports only the pinned Mathlib.
The explicit positivity lemmas stabilize generated certificate names; each
is proved by the standard natural-number successor instance. The three
intentional proof holes below belong to the Challenge, never to the Solution.
-/

@[expose] public section
namespace CDRBicolour

/-- Three-element blocks covering each unordered pair exactly once. -/
structure STS (V : Type*) [DecidableEq V] where
  blocks : Finset (Finset V)
  card_eq_three : ∀ B ∈ blocks, B.card = 3
  existsUnique_block : ∀ x y : V, x ≠ y → ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

def IsStrictBicolouring {V : Type*} [DecidableEq V]
    (S : STS V) (col : V → Fin 3) : Prop :=
  ∀ B ∈ S.blocks, (B.image col).card = 2

def classSize {V : Type*} [Fintype V]
    (col : V → Fin 3) (i : Fin 3) : ℕ :=
  (Finset.univ.filter fun v => col v = i).card

def AdmissibleProfile (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
  ((a + b + c) % 6 = 1 ∨ (a + b + c) % 6 = 3) ∧
  ((a : ℤ) ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c = a + b + c) ∧
  ¬ (a = 2 ∧ b = 2) ∧ ¬ (a = 2 ∧ c = 2) ∧ ¬ (b = 2 ∧ c = 2)

/-- Positivity certificate with the original statement's stable declaration name. -/
theorem Realises._proof_1 : @NeZero ℕ (@Zero.ofOfNat0 ℕ (@instOfNatNat (nat_lit 0))) (2 + 1) := @Nat.instNeZeroSucc 2
attribute [local instance] Realises._proof_1

def Realises (a b c : ℕ) : Prop :=
  ∃ (S : STS (Fin (a + b + c))) (col : Fin (a + b + c) → Fin 3),
    IsStrictBicolouring S col ∧
      classSize col 0 = a ∧ classSize col 1 = b ∧ classSize col 2 = c

def CDRConjecture : Prop :=
  ∀ a b c : ℕ, AdmissibleProfile a b c → Realises a b c

/-- Paper II, sufficiency at every order. -/
theorem cdr_conjecture : CDRConjecture := by
  sorry

/-- Paper II, Theorem 1: the full class-size characterization. -/
theorem cdr_characterization {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Realises a b c ↔ AdmissibleProfile a b c := by
  sorry

namespace Prefix
/-- Positivity certificate with the original statement's stable declaration name. -/
theorem col3._proof_1 : @NeZero ℕ (@Zero.ofOfNat0 ℕ (@instOfNatNat (nat_lit 0))) (2 + 1) := @Nat.instNeZeroSucc 2
attribute [local instance] col3._proof_1

def col3 (a b c : ℕ) (v : Fin (a + b + c)) : Fin 3 :=
  if v.val < a then 0 else if v.val < a + b then 1 else 2
end Prefix

namespace BlockTypes
def cnt {V : Type*}
    (col : V → Fin 3) (j : Fin 3) (B : Finset V) : ℕ :=
  (B.filter fun y => col y = j).card

def typeCount {V : Type*} [DecidableEq V]
    (S : STS V) (col : V → Fin 3) (i j : Fin 3) : ℕ :=
  (S.blocks.filter fun B => cnt col i B = 2 ∧ cnt col j B = 1).card
end BlockTypes

namespace Absorption.Corners
abbrev sz (a b c : ℕ) (X : Fin 3) : ℕ := ![a, b, c] X

/-- Positivity certificate with the original statement's stable declaration name. -/
theorem LowerNec._proof_1 : @NeZero ℕ (@Zero.ofOfNat0 ℕ (@instOfNatNat (nat_lit 0))) (2 + 1) := @Nat.instNeZeroSucc 2
attribute [local instance] LowerNec._proof_1

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

/-- Paper I, Theorem 1: the exact spectrum for every sufficiently large profile. -/
theorem cdr_type_spectrum : ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
    ∀ t : ℕ, AACSpec a b c t ↔ ExactNec a b c t := by
  sorry

end Absorption.Corners
end CDRBicolour
