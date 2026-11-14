/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.Cross
public import CDRBicolour.KBicolor.Completion
public import CountingCone.Construction

/-!
# Counting Wilson families over a fixed residual decomposition

The residual host is independent of the free Latin squares. A decomposition of
this one host therefore completes every family, injectively. The lower bound is
`L(t) ^ (card A ^ 2 * |OT S|)` and the corresponding logarithmic bound.

The residual decomposition is an explicit hypothesis: constructing it uniformly
for the bounded patterns is the remaining absorption step for sharp counting.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Classical Finset TypedTriangle CDRBicolour.Absorption
open CDRBicolour.Absorption.Count.Wilson (OT)

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}

/-- Changing the Latin family preserves the entire set of covered edges. -/
theorem crossEdges_eq (hS : _root_.STS.IsSTS S) (Λ Λ' : LFam A S t) :
    (crossP h Λ).biUnion triEdges = (crossP h Λ').biUnion triEdges := by
  ext e
  induction e using Sym2.ind with
  | _ u v => rw [mem_crossEdges h hS, mem_crossEdges h hS]

theorem crossP_disjoint_residual (Λ : LFam A S t) {D : Finset (Finset (Fin n))}
    (hD : ∀ T ∈ D, IsAllowed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) T) :
    Disjoint (crossP h Λ) D := by
  rw [Finset.disjoint_left]
  intro T hT hTD
  obtain ⟨x, -, rfl⟩ := mem_image.mp hT
  have hd := disj_of_rHostK lab (hD _ hTD)
  apply Finset.disjoint_left.mp hd
  · exact CDRBicolour.Absorption.Count.Wilson.mem_tE.mpr
      ⟨(mem_blk h).mpr ⟨0, rfl⟩, (mem_blk h).mpr ⟨1, rfl⟩,
        pos_ne h Λ x (by decide)⟩
  · exact mem_biUnion.mpr ⟨blk h Λ x, mem_image.mpr ⟨x, mem_univ _, rfl⟩,
      CDRBicolour.Absorption.Count.Wilson.mem_tE.mpr
        ⟨(mem_blk h).mpr ⟨0, rfl⟩, (mem_blk h).mpr ⟨1, rfl⟩,
          pos_ne h Λ x (by decide)⟩⟩

/-- One decomposition of the common residual completes all Latin families injectively. -/
theorem card_LFam_le (hS : _root_.STS.IsSTS S) (Λ₀ : LFam A S t)
    {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (rHostK lab ((crossP h Λ₀).biUnion triEdges)) (bicF k)
      (edges (rHostK lab ((crossP h Λ₀).biUnion triEdges))) D) :
    Fintype.card (LFam A S t) ≤ kCount lab := by
  classical
  have hDΛ : ∀ Λ : LFam A S t,
      IsDecomposition (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
        (edges (rHostK lab ((crossP h Λ).biUnion triEdges))) D := by
    intro Λ
    rw [crossEdges_eq h hS Λ Λ₀]
    exact hD
  have hdisj : ∀ Λ : LFam A S t, Disjoint (crossP h Λ) D :=
    fun Λ => crossP_disjoint_residual h Λ (hDΛ Λ).1
  unfold kCount
  rw [← card_univ]
  refine card_le_card_of_injOn (fun Λ => D ∪ crossP h Λ)
    (fun Λ _ => ?_) (fun Λ _ Λ' _ he => ?_)
  · exact mem_kBlocks_of_decomp lab
      (union_decomp lab (crossP_allowed h Λ) (crossP_disj h hS Λ) (hDΛ Λ))
  · have hre : ∀ Λ : LFam A S t, (D ∪ crossP h Λ) \ D = crossP h Λ := by
      intro Λ
      rw [union_sdiff_left, sdiff_eq_self_of_disjoint (hdisj Λ)]
    have hcross := congrArg (fun X : Finset (Finset (Fin n)) => X \ D) he
    rw [hre, hre] at hcross
    exact crossP_inj h hS hcross

/-- There is one independent Latin square per pattern cell and oriented group block. -/
theorem card_LFam :
    Fintype.card (LFam A S t) =
      (_root_.STS.L t) ^ (Fintype.card A ^ 2 * #(OT S)) := by
  classical
  rw [Fintype.card_fun]
  congr 1
  · unfold _root_.STS.L
    rw [Nat.card_eq_fintype_card]
  · simp only [Ix, Fintype.card_prod, Fintype.card_coe]
    ring

/-- An explicit lower bound, conditional only on completing the common residual. -/
theorem latin_power_le_kCount (hS : _root_.STS.IsSTS S) (Λ₀ : LFam A S t)
    {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (rHostK lab ((crossP h Λ₀).biUnion triEdges)) (bicF k)
      (edges (rHostK lab ((crossP h Λ₀).biUnion triEdges))) D) :
    (_root_.STS.L t) ^ (Fintype.card A ^ 2 * #(OT S)) ≤ kCount lab := by
  rw [← card_LFam]
  exact card_LFam_le h hS Λ₀ hD

/-- Entropy of the free choices, with no loss from overcounting. -/
theorem log_kCount_ge (hS : _root_.STS.IsSTS S) (Λ₀ : LFam A S t) (ht : 1 ≤ t)
    {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (rHostK lab ((crossP h Λ₀).biUnion triEdges)) (bicF k)
      (edges (rHostK lab ((crossP h Λ₀).biUnion triEdges))) D) :
    (Fintype.card A ^ 2 * #(OT S) : ℕ) * (t : ℝ) ^ 2 * (Real.log t - 2) ≤
      Real.log (kCount lab) := by
  have hpow := latin_power_le_kCount h hS Λ₀ hD
  have hLpos : (0 : ℝ) < _root_.STS.L t := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (_root_.STS.L_pos t))
  have hle : ((_root_.STS.L t : ℝ) ^ (Fintype.card A ^ 2 * #(OT S))) ≤ kCount lab := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos hLpos _) hle
  rw [Real.log_pow] at hlog
  have hlower := _root_.STS.hL_one _root_.STS.van_der_waerden t ht
  have hmul := mul_le_mul_of_nonneg_left hlower
    (Nat.cast_nonneg (Fintype.card A ^ 2 * #(OT S)) :
      (0 : ℝ) ≤ (Fintype.card A ^ 2 * #(OT S) : ℕ))
  calc
    _ = (Fintype.card A ^ 2 * #(OT S) : ℕ) *
        ((t : ℝ) ^ 2 * (Real.log t - 2)) := by ring
    _ ≤ (Fintype.card A ^ 2 * #(OT S) : ℕ) * Real.log (_root_.STS.L t) := by
      simpa only [one_mul] using hmul
    _ ≤ Real.log (kCount lab) := hlog

end CDRBicolour.KBicolor.Wilson
