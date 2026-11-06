/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SeedPersistence
public import RequestProject.TypedTriangle.NativeSeedNibble
public import RequestProject.TypedTriangle.PhysicalResidual
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Protect a genuinely basal sparse stock, construct its residual diffuse seed,
and nibble outside it. This constructs the packing; it does not construct a
universal absorbing stock or assert capacity for its final leftover. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.ProtectedNibble

/-- A sparse basal reserve can be protected throughout an actual packing.
H1, H2 and H4 refer to the original host. The residual seed is constructed,
and the leftover is in the original INTEGER physical lattice. -/
theorem packing_away_from_basal_reserve {I : Type} (F : Set (Multiset I))
    (C α η : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → HingeCond H F α h →
        IsDecomposition H F R D → (∀ v, degIn R v ≤ d) →
        (d : ℝ) ≤ ε * Fintype.card V →
        ∃ P : Finset (Finset V), TypedTriangle.IsPacking H F P ∧
          Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H \ R) \ P.biUnion triEdges) ∧
          (∀ v, ((((edges H \ R) \ P.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ)
            ≤ η * Fintype.card V) := by
  obtain ⟨ε,hε,nS,hS⟩ := seed_persistence_exact (F := F) hC hα h
  obtain ⟨nP,hP⟩ := NativeNibble.packing_of_diffuse_seed (2*C) η (by linarith) hη hη1
  refine ⟨ε,hε,max nS nP,?_⟩
  intro V _ H φ R D d hn hφ hH2 hH4 hD hdeg hd
  have hRsub : R ⊆ edges H := by
    rw [← hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  obtain ⟨ψ,hψ,-⟩ := hS H φ R D d ((le_max_left _ _).trans hn)
    hφ hH4 hRsub hD hdeg hd
  obtain ⟨P,-,hp,hsmall⟩ := hP (residual H R) F ψ ((le_max_right _ _).trans hn) hψ
  have hpH : TypedTriangle.IsPacking H F P := by
    refine ⟨?_,hp.2⟩
    intro T hT
    exact isAllowed_mono (subHost_le H _) rfl (hp.1 T hT)
  have hJ : edges (residual H R) = edges H \ R :=
    Residual.edges_subHost_eq sdiff_subset
  have hPsub : P.biUnion triEdges ⊆ edges H \ R := by
    rw [← hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hp.1 T hT) heT
  have hdis : Disjoint (P.biUnion triEdges) R := by
    apply disjoint_left.mpr
    intro e he hR
    exact (mem_sdiff.mp (hPsub he)).2 hR
  have hphys : IsPhysical H F ((edges H \ R) \ P.biUnion triEdges) :=
    isPhysical_sdiff (isPhysical_sdiff_of_decomposition hH2 hD hRsub)
      (isPhysical_of_isDecomposition hpH.isDecomposition) hPsub
  refine ⟨P,hpH,hdis,hphys,?_⟩
  simpa only [hJ] using hsmall

end TypedTriangle.ProtectedNibble
