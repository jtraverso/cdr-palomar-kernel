/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SeedPersistence
public import RequestProject.TypedTriangle.BasalPackingIncidence
public import RequestProject.TypedTriangle.PhysicalResidual
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! An exact seed on the SAME complementary host when the protected child
edges already have a sparse triangle decomposition. This states the precise
condition needed to feed G4; it does not construct that child decomposition. -/

open Finset Classical
noncomputable section
namespace TypedTriangle
open BasalIncidence

theorem exact_seed_after_decomposable_child {I : Type} (F : Set (Multiset I))
    (C α : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D : Finset (Finset V)) (d : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → HingeCond H F α h →
        IsDecomposition H F (cover D) D →
        (∀ v, degIn (cover D) v ≤ d) →
        (d : ℝ) ≤ ε₀ * Fintype.card V →
        ∃ ψ : Finset V → ℝ,
          IsDiffuseSeed (subHost H (edges H \ cover D)) F (2*C) ψ ∧
          (∀ S, ψ S ≠ 0 → IsAllowed (subHost H (edges H \ cover D)) F S) := by
  obtain ⟨ε₀,hε₀,n₀,hseed⟩ := seed_persistence_exact (F := F) hC hα h
  refine ⟨ε₀,hε₀,n₀,?_⟩
  intro V _ H φ D d hn hφ hH4 hD hdeg hd
  have hSub : cover D ⊆ edges H := by
    rw [← hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  simpa only [residual] using hseed H φ (cover D) D d hn hφ hH4
    hSub hD hdeg hd

/-- A sparse decomposed child can be protected before the packing: the very
same complementary host inherits both an exact positive seed and H2 in its
own integer physical lattice. The H3/H4 loss is a separate obligation. -/
theorem exact_seed_and_physical_complement {I : Type} (F : Set (Multiset I))
    (C α : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D : Finset (Finset V)) (d : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α → HingeCond H F α h →
        IsDecomposition H F (cover D) D →
        (∀ v, degIn (cover D) v ≤ d) →
        (d : ℝ) ≤ ε * Fintype.card V →
        ∃ ψ : Finset V → ℝ,
          IsDiffuseSeed (subHost H (edges H \ cover D)) F (2*C) ψ ∧
          IsPhysical (subHost H (edges H \ cover D)) F
            (edges (subHost H (edges H \ cover D))) := by
  obtain ⟨εS,hεS,nS,hSeed⟩ :=
    exact_seed_after_decomposable_child F C α h hC hα
  obtain ⟨εP,hεP,nP,hPhysical⟩ :=
    Residual.physical_residual_of_H2H3H4 α h hα
  let ε := min εS εP
  have hε : 0 < ε := lt_min hεS hεP
  refine ⟨ε,hε,max nS nP,?_⟩
  intro V _ H φ D d hn hφ hH2 hH3 hH4 hD hdeg hd
  have hN : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hdS : (d:ℝ) ≤ εS*Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hN)
  have hdP : (d:ℝ) ≤ εP*Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hN)
  obtain ⟨ψ,hψ,_⟩ := hSeed H φ D d ((le_max_left _ _).trans hn)
    hφ hH4 hD hdeg hdS
  have hSub : cover D ⊆ edges H := by
    rw [← hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hdegR : ∀ v,
      (((cover D).filter (fun e => v ∈ e)).card : ℝ) ≤
        εP * Fintype.card V := by
    intro v
    exact (by exact_mod_cast hdeg v :
      (((cover D).filter (fun e => v ∈ e)).card : ℝ) ≤ d).trans hdP
  exact ⟨ψ,hψ,hPhysical H F ((le_max_right _ _).trans hn) hH3 hH4 hH2
    (cover D) hSub (isPhysical_of_isDecomposition hD) hdegR⟩

#print axioms exact_seed_after_decomposable_child
#print axioms exact_seed_and_physical_complement

end TypedTriangle
