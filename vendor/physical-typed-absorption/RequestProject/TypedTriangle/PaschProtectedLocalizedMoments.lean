module
public import RequestProject.TypedTriangle.PaschLocalizedPacking
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorCore
public import RequestProject.TypedTriangle.SeedMoment
public import RequestProject.TypedTriangle.ReserveCommonNbr
public import RequestProject.TypedTriangle.ProtectedSeedNibble
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open ProtectedNibble
open LocalizedCover

/-- The SAME protected packing has small leftover degree and localized
physical moments bounded by tau*n*|Z| and a Pasch quota for the LITERAL
constructed residual seed. Its exactness and pointwise comparison with the
original seed are retained for the subsequent fractional-target transfer. -/
theorem protected_localized_packing_with_residual_pasch {I : Type} (F : Set (Multiset I))
    (C α η τ L σ : ℝ) (h q : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η)
    (hτ : 0 < τ) (hL : 0 < L) (hσ : 0 < σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ ε*Fintype.card V →
      ∀ (κ : Type) [Fintype κ] (bad : κ → Finset V) (lam : κ → Sym2 V → ℝ),
        (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (lam k) T| ≤ 3*L*(T∩bad k).card) →
        ∃ (ψ : Finset V → ℝ) (P : Finset (Finset V)),
          IsDiffuseSeed (residual H R) F (2*C) ψ ∧
          (∀ T, ψ T ≠ 0 → IsAllowed (residual H R) F T) ∧
          (∀ T, IsAllowed (residual H R) F T →
            |ψ T-φ T| ≤ ExplicitSeed.seedPointwiseCost α C h*d/(Fintype.card V:ℝ)^2) ∧
          IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          (∀ k, |edgeSum (lam k) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*Fintype.card V*(bad k).card) ∧
          |(count P:ℝ)-target ψ (allowed (residual H R) F)| ≤ σ*(Fintype.card V:ℝ)^2 := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let εS := ExplicitSeed.seedExactBudget C α h
  let nS := ExplicitSeed.seedExactOrder C
  have hεS : 0 < εS := by
    change 0 < RawReference.Explicit.seedBudget (1/C) C α h
    exact RawReference.Explicit.seedBudget_pos h (by positivity)
      (by rw [div_le_iff₀ hC0]; nlinarith only [hC]) hα
  obtain ⟨nP,hPack⟩ := localized_signed_packing_with_pasch
    (2*C) (α/2) η τ L σ q (by linarith only [hC]) (by positivity) hη hτ hL hσ
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
  obtain ⟨ψ,hψ,hSupp,hClose⟩ := ExplicitSeed.seed_persistence_exact_with_pointwise_bound_explicit (F:=F) hC hα h H φ R D d ((le_max_left _ _).trans hn) hφ h4 hRsub hD hdeg hdS
  obtain ⟨P,hPsub,hP,hSparse,hQuota,hPasch⟩ := hPack (residual H R) F ψ
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
  refine ⟨ψ,P,hψ,hSupp,hClose,hPH,hDis,hPhys,?_,?_,hPasch⟩
  · simpa only [hJ] using hSparse
  · intro k
    have hh := remainder_moment_of_quota hψ P hPH (by rw [hJ]; exact hPE) (lam k)
      (τ*Fintype.card V*(bad k).card) (hQuota k)
    simpa only [hJ] using hh

#print axioms protected_localized_packing_with_residual_pasch
end TypedTriangle.Pasch
