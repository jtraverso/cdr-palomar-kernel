/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.ResidualHinge

/-!
# Prescribed exact intersection (backlog item 2b): reduction to refined completions

**Target** (`PrescribedIntersection`): for every sufficiently large admissible profile and every
sparse packing `P` of bicoloured triangles, there are two strictly bicoloured STS with the
prescribed classes whose block sets intersect in **exactly** `P`.

**Mechanism.** Refine the labels by `β v = v mod 6` and split the bicoloured triangles by the
*parity class* `⌊(Σ β mod 6) / 3⌋ ∈ {0, 1}`.  If each parity class admits a completion
(`RefinedCompletion j`: every sparse packing `P` extends to a strictly bicoloured STS all of whose
other blocks have parity class `j`), then the two completions can only share blocks of `P`
(`prescribed_intersection_of_refined`).

The refined host (labels `Fin 3 × ZMod 6`, allowed = bicoloured with `Σ β ∈ {0,1,2}` resp.
`{3,4,5}`) has, at type level, the same lattice invariants as the CDR host (only `ℓ`), connected
non-bipartite vertex links, and a positive type-uniform seed with `n μ ∈ [2.9, 3.5]` on
admissible profiles (numerical checks, `docs/PLAN_2B_INTERSECCION.md`).  Proving
`RefinedCompletion j` means redoing H1–H4 for that host and applying Theorem T.
-/

@[expose] public section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-- The refining label `β v = v mod 6`. -/
def beta6 {n : ℕ} (v : Fin n) : ℕ := v.val % 6

/-- Parity class of a triangle: `⌊(Σ β mod 6) / 3⌋`, in `{0, 1}`. -/
def parClass {n : ℕ} (T : Finset (Fin n)) : ℕ := (∑ v ∈ T, beta6 v) % 6 / 3

theorem parClass_lt_two {n : ℕ} (T : Finset (Fin n)) : parClass T < 2 := by
  unfold parClass; omega

/-- **Refined completion in parity class `j`.** -/
def RefinedCompletion (j : ℕ) : Prop :=
  ∃ K n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
    ∀ (P : Finset (Finset (Fin (a + b + c)))) (Δ : ℕ),
      (∀ T ∈ P, IsAllowed (cdrHost a b c) cdrF T) →
      (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges →
      (∀ p, degL (P.biUnion triEdges) p ≤ Δ) → K * Δ ≤ a + b + c →
      ∃ S : STS (Fin (a + b + c)), P ⊆ S.blocks ∧ IsStrictBicolouring S (col3 a b c) ∧
        classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
        classSize (col3 a b c) 2 = c ∧ ∀ T ∈ S.blocks, T ∉ P → parClass T = j

/-- **Backlog item 2b**: two realisations meeting in exactly a prescribed sparse packing. -/
def PrescribedIntersection : Prop :=
  ∃ K n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
    ∀ (P : Finset (Finset (Fin (a + b + c)))) (Δ : ℕ),
      (∀ T ∈ P, IsAllowed (cdrHost a b c) cdrF T) →
      (P : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges →
      (∀ p, degL (P.biUnion triEdges) p ≤ Δ) → K * Δ ≤ a + b + c →
      ∃ S₁ S₂ : STS (Fin (a + b + c)),
        IsStrictBicolouring S₁ (col3 a b c) ∧ IsStrictBicolouring S₂ (col3 a b c) ∧
        classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
        classSize (col3 a b c) 2 = c ∧ S₁.blocks ∩ S₂.blocks = P

/-- **Reduction of 2b**: completions in the two parity classes meet exactly in `P`. -/
theorem prescribed_intersection_of_refined (h₀ : RefinedCompletion 0)
    (h₁ : RefinedCompletion 1) : PrescribedIntersection := by
  obtain ⟨K₀, n₀, H₀⟩ := h₀
  obtain ⟨K₁, n₁, H₁⟩ := h₁
  refine ⟨max K₀ K₁, max n₀ n₁, fun a b c h hn P Δ hP hPd hdeg hK => ?_⟩
  obtain ⟨S₁, hP₁, hc₁, ha, hb, hc, hj₁⟩ := H₀ a b c h (le_of_max_le_left hn) P Δ hP hPd hdeg
    ((Nat.mul_le_mul_right Δ (le_max_left K₀ K₁)).trans hK)
  obtain ⟨S₂, hP₂, hc₂, -, -, -, hj₂⟩ := H₁ a b c h (le_of_max_le_right hn) P Δ hP hPd hdeg
    ((Nat.mul_le_mul_right Δ (le_max_right K₀ K₁)).trans hK)
  refine ⟨S₁, S₂, hc₁, hc₂, ha, hb, hc, ?_⟩
  ext T
  simp only [mem_inter]
  constructor
  · rintro ⟨hT₁, hT₂⟩
    by_contra hTP
    have e₁ := hj₁ T hT₁ hTP
    have e₂ := hj₂ T hT₂ hTP
    omega
  · intro hT
    exact ⟨hP₁ hT, hP₂ hT⟩

end CDRBicolour.Absorption
