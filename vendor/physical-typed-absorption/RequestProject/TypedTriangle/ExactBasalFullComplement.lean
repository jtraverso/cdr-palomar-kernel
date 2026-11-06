/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExactChildSeed
public import RequestProject.TypedTriangle.G4GraphDeleteAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! A sparse basal edge set can be removed while retaining one host with
an exact diffuse seed, intrinsic physicality, common neighbours, and hinges.
The hinge order changes in this one-step statement. -/

open Finset Classical
noncomputable section
namespace TypedTriangle
open BasalIncidence

theorem exact_basal_full_complement {I : Type} (F : Set (Multiset I))
    (C α : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D : Finset (Finset V)) (d : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α → HingeCond H F α h →
        IsDecomposition H F (cover D) D →
        (∀ v, SparseEdge.degIn (cover D) v ≤ d) →
        (d : ℝ) ≤ ε * Fintype.card V →
        ∃ ψ : Finset V → ℝ,
          IsDiffuseSeed (subHost H (edges H \ cover D)) F (2*C) ψ ∧
          IsPhysical (subHost H (edges H \ cover D)) F
            (edges (subHost H (edges H \ cover D))) ∧
          CommonNbrCond (subHost H (edges H \ cover D)) F (α/2) ∧
          HingeCond (subHost H (edges H \ cover D)) F
            (S07V49.hingeConstB α 1 h) (2*h-3) := by
  obtain ⟨ε₁,hε₁,n₁,hMain⟩ :=
    exact_seed_and_physical_complement F C α h hC hα
  obtain ⟨ε₂,hε₂,n₂,hHinge⟩ :=
    StockEntry.g4_hinge_after_edge_set_deletion F α C 1 h hα
      (by linarith) (by norm_num) hh
  let ε := min ε₁ (min ε₂ (α/4))
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ (by positivity))
  refine ⟨ε,hε,max n₁ n₂,?_⟩
  intro V _ H φ D d hn hSeed hPhys hCommon hHinge0 hD hDeg hSmall
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hS₁ : (d : ℝ) ≤ ε₁ * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right
      (le_trans (min_le_left _ _) (le_refl _)) hN)
  have hS₂ : (d : ℝ) ≤ ε₂ * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) hN)
  have hSα : (d : ℝ) ≤ α/4 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) hN)
  obtain ⟨ψ,hψ,hPhysical⟩ := hMain H φ D d
    ((Nat.le_max_left _ _).trans hn) hSeed hPhys hCommon hHinge0
    hD hDeg hS₁
  have hWindow : (4*d : ℕ) ≤ α * Fintype.card V := by
    exact_mod_cast (show (4 : ℝ) * d ≤ α * Fintype.card V by linarith)
  have hCommon' : CommonNbrCond
      (subHost H (edges H \ cover D)) F (α/2) :=
    Residual.commonNbrCond_sdiff hCommon (cover D) d hDeg hWindow
  have hDE : cover D ⊆ edges H := CorePaid.basal_subset_edges ⟨D,hD⟩
  have hHinge' := hHinge H φ (cover D) d
    ((Nat.le_max_right _ _).trans hn)
    hSeed hCommon hHinge0 hDE hDeg hS₂
  exact ⟨ψ,hψ,hPhysical,hCommon',hHinge'⟩

#print axioms exact_basal_full_complement

end TypedTriangle
