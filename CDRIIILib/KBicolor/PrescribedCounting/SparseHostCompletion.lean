/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.Wilson.AbsorptionCore
public import RequestProject.TypedTriangle.SeedPersistence
public import RequestProject.TypedTriangle.PhysicalResidual
public import RequestProject.TypedTriangle.VortexEdgeHingeNoSeed

/-! # Completing a sparse prescribed packing in the actual host

The host may be a Wilson residual, rather than a complete graph. All four
hypotheses of T on the deleted host are derived from the original H1--H4.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle

theorem sparse_host_completion {I : Type} (F : Set (Multiset I)) (C α : ℝ) (h : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I),
      n₀ ≤ Fintype.card V →
      (∃ μ, IsDiffuseSeed H F C μ) → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h →
      ∀ (B : Finset (Sym2 V)) (Q : Finset (Finset V)) (d : ℕ),
      B ⊆ edges H → IsDecomposition H F B Q →
      (∀ v, SparseEdge.degIn (B) v ≤ d) →
      (d : ℝ) ≤ γ * Fintype.card V →
      ∃ D, IsDecomposition (residual H (B)) F
        (edges (residual H (B))) D := by
  obtain ⟨γ₁,hγ₁,n₁,h₁⟩ := seed_persistence_exact (F := F) hC hα h
  obtain ⟨γ₂,hγ₂,n₂,h₂⟩ := Residual.physical_residual_of_H2H3H4 α h hα
  obtain ⟨γ₃,hγ₃,n₃,h₃⟩ := Vortex.hinge_after_edge_set_deletion_no_seed_uniform α h hα hh
  let α' := min (α/2) (S07V49.hingeConstB α 1 h)
  have hα' : 0 < α' := lt_min (by positivity)
    (S07V49.hingeConstB_pos hα (by norm_num) (by omega))
  obtain ⟨nT,hT⟩ := Vortex.main_theorem_T F α' (2*C) (2*h-3) hα' (by linarith) (by omega)
  let γ := min γ₁ (min γ₂ (min γ₃ (α/4)))
  have hγ : 0 < γ := lt_min hγ₁ (lt_min hγ₂ (lt_min hγ₃ (by positivity)))
  refine ⟨γ,hγ,max nT (max n₁ (max n₂ n₃)),?_⟩
  intro V _ H hn hseed H2 H3 H4 B Q d hB hQ hdeg hd
  have hnT : nT ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnrest := (le_max_right _ _).trans hn
  have hn₁ : n₁ ≤ Fintype.card V := (le_max_left _ _).trans hnrest
  have hn₂ : n₂ ≤ Fintype.card V := (le_max_left _ _).trans ((le_max_right _ _).trans hnrest)
  have hn₃ : n₃ ≤ Fintype.card V := (le_max_right _ _).trans ((le_max_right _ _).trans hnrest)
  have hγ₁' : γ ≤ γ₁ := min_le_left _ _
  have hγ₂' : γ ≤ γ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hγ₃' : γ ≤ γ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγα : γ ≤ α/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  obtain ⟨μ,hμ⟩ := hseed
  obtain ⟨ψ,hψ,-⟩ := h₁ H μ (B) Q d hn₁ hμ H4 hB hQ
    (by simpa only [degIn,SparseEdge.degIn] using hdeg)
    (hd.trans (mul_le_mul_of_nonneg_right hγ₁' hn0))
  have H2' := h₂ H F hn₂ H3 H4 H2 B hB (isPhysical_of_isDecomposition hQ) (fun v =>
    (show (SparseEdge.degIn (B) v : ℝ) ≤ d by exact_mod_cast hdeg v).trans
      (hd.trans (mul_le_mul_of_nonneg_right hγ₂' hn0)))
  have H3' := Residual.commonNbrCond_sdiff H3 (B) d hdeg (by
    push_cast
    have hwin := hd.trans (mul_le_mul_of_nonneg_right hγα hn0)
    nlinarith)
  have H4' := h₃ H F hn₃ H3 H4 (B) d hB hdeg
    (hd.trans (mul_le_mul_of_nonneg_right hγ₃' hn0))
  exact hT _ hnT ⟨ψ,hψ⟩ H2' (commonNbr_mono H3' (min_le_left _ _))
    (hingeCond_mono H4' (min_le_right _ _))

end CDRBicolour.KBicolor.PrescribedCounting
