/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeLocalizedSignedPacking
public import RequestProject.TypedTriangle.SeedMoment
public import RequestProject.TypedTriangle.ReserveCommonNbr
public import RequestProject.TypedTriangle.ProtectedSeedNibble
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ProtectedNibble
open LocalizedCover

/-- The SAME protected packing has small leftover degree and localized
physical moments bounded by tau*n*|Z|, including small or empty Z. Neither a
test-mass provider nor a quadratic error at every stratum is an input. -/
theorem localized_physical_moment_packing {I : Type} (F : Set (Multiset I))
    (C α η τ L : ℝ) (h q : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η)
    (hτ : 0 < τ) (hL : 0 < L) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ ε*Fintype.card V →
      ∀ (κ : Type) [Fintype κ] (bad : κ → Finset V) (lam : κ → Sym2 V → ℝ),
        (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (lam k) T| ≤ 3*L*(T∩bad k).card) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          ∀ k, |edgeSum (lam k) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*Fintype.card V*(bad k).card := by
  obtain ⟨εS,hεS,nS,hSeed⟩ := seed_persistence_exact (F:=F) hC hα h
  obtain ⟨nP,hPack⟩ := WeightedStar.localized_signed_packing_of_H1H3
    (2*C) (α/2) η τ L q (by linarith) (by positivity) hη hτ hL
  let ε := min εS (α/4)
  have hε : 0 < ε := lt_min hεS (by positivity)
  refine ⟨ε,hε,max nS nP,?_⟩
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ _ bad lam hκ htri
  have hRsub : R ⊆ edges H := by
    rw [←hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hn0 : (0:ℝ) ≤ Fintype.card V := by positivity
  have hdS : (d:ℝ) ≤ εS*Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hd3 : (d:ℝ) ≤ α/4*Fintype.card V :=
    hd.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hres3 := residual_commonNbrCond h3 R d hdeg hd3
  obtain ⟨ψ,hψ,-⟩ := hSeed H φ R D d ((le_max_left _ _).trans hn) hφ h4 hRsub hD hdeg hdS
  obtain ⟨P,hPsub,hP,hSparse,hQuota⟩ := hPack (residual H R) F ψ
    ((le_max_right _ _).trans hn) hψ hres3 κ bad (fun k => triSum (lam k)) hκ
    (fun k T hT => htri k T (isAllowed_mono (subHost_le H _) rfl hT))
  have hPH : IsPacking H F P := ⟨fun T hT =>
    isAllowed_mono (subHost_le H _) rfl (hP.1 T hT),hP.2⟩
  have hJ : edges (residual H R) = edges H\R := Residual.edges_subHost_eq sdiff_subset
  have hPE : P.biUnion triEdges ⊆ edges H\R := by
    rw [←hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hDis : Disjoint (P.biUnion triEdges) R :=
    disjoint_left.mpr fun e he hR => (mem_sdiff.mp (hPE he)).2 hR
  have hPhys := isPhysical_sdiff (isPhysical_sdiff_of_decomposition h2 hD hRsub)
    (isPhysical_of_isDecomposition hPH.isDecomposition) hPE
  refine ⟨P,hPH,hDis,hPhys,?_,?_⟩
  · simpa only [hJ] using hSparse
  · intro k
    have hh := remainder_moment_of_quota hψ P hPH (by rw [hJ]; exact hPE) (lam k)
      (τ*Fintype.card V*(bad k).card) (hQuota k)
    simpa only [hJ] using hh

end TypedTriangle.ProtectedNibble
