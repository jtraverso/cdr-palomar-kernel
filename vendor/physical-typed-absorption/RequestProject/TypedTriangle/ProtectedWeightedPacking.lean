/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeWeightedPacking
public import RequestProject.TypedTriangle.ProtectedSeedNibble
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ProtectedNibble

/-- Construct an exact seed and a monitored packing outside an actual basal
reserve. The residual stays in the original integer physical lattice. The tests
are chosen after the residual seed; no signed test or matching is assumed. -/
theorem weighted_packing_away_from_basal_reserve {I : Type} (F : Set (Multiset I))
    (C α c η : ℝ) (h q : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hc : 0 < c) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      IsPhysical H F (edges H) → HingeCond H F α h →
      IsDecomposition H F R D → (∀ v, degIn R v ≤ d) →
      (d:ℝ) ≤ ε*Fintype.card V →
      ∃ ψ : Finset V → ℝ, IsDiffuseSeed (residual H R) F (2*C) ψ ∧
        ∀ (κ : Type) [Fintype κ] (W : κ → Finset V → ℝ),
          (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
          (∀ k T, IsAllowed (residual H R) F T → 0 ≤ W k T ∧ W k T ≤ 1) →
          (∀ k, c*Fintype.card V ≤ ∑ T ∈ allowed (residual H R) F, ψ T*W k T) →
          ∃ P : Finset (Finset V), IsPacking H F P ∧
            Disjoint (P.biUnion triEdges) R ∧
            IsPhysical H F ((edges H \ R) \ P.biUnion triEdges) ∧
            ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed (residual H R) F, ψ T*W k T)| ≤
              η*(∑ T ∈ allowed (residual H R) F, ψ T*W k T) := by
  obtain ⟨ε,hε,nS,hSeed⟩ := seed_persistence_exact (F:=F) hC hα h
  obtain ⟨nP,hPack⟩ := NativeNibble.weighted_packing_of_diffuse_seed (2*C) c η q (by linarith) hc hη
  refine ⟨ε,hε,max nS nP,?_⟩
  intro V _ H φ R D d hn hφ hH2 hH4 hD hdeg hd
  have hRsub : R ⊆ edges H := by
    rw [←hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  obtain ⟨ψ,hψ,-⟩ := hSeed H φ R D d ((le_max_left _ _).trans hn) hφ hH4 hRsub hD hdeg hd
  refine ⟨ψ,hψ,?_⟩
  intro κ _ W hκ hW hmass
  obtain ⟨P,hPsub,hP,hWeights⟩ := hPack (residual H R) F ψ ((le_max_right _ _).trans hn) hψ κ W hκ hW hmass
  have hPH : IsPacking H F P := by
    refine ⟨?_,hP.2⟩
    intro T hT
    exact isAllowed_mono (subHost_le H _) rfl (hP.1 T hT)
  have hJ : edges (residual H R) = edges H \ R := Residual.edges_subHost_eq sdiff_subset
  have hPE : P.biUnion triEdges ⊆ edges H \ R := by
    rw [←hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hDis : Disjoint (P.biUnion triEdges) R := disjoint_left.mpr fun e he hR => (mem_sdiff.mp (hPE he)).2 hR
  have hPhys : IsPhysical H F ((edges H \ R) \ P.biUnion triEdges) :=
    isPhysical_sdiff (isPhysical_sdiff_of_decomposition hH2 hD hRsub)
      (isPhysical_of_isDecomposition hPH.isDecomposition) hPE
  exact ⟨P,hPH,hDis,hPhys,hWeights⟩
end TypedTriangle.ProtectedNibble
