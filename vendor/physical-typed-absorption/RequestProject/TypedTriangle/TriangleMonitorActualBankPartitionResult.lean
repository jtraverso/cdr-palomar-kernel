/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4SampledReferenceComplement
public import RequestProject.TypedTriangle.TriangleMonitorFixedWindowPartitionResult
public import RequestProject.TypedTriangle.TriangleMonitorSeedPersistence
public import RequestProject.TypedTriangle.TriangleMonitorSeedComparison
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000
set_option autoImplicit false

namespace TypedTriangle.Vortex
open CatalogNative BasalIncidence S07V42 StockEntry

/-- The original H1--H4 and the actual basal resource union produce the
monitored native packing result. No H1/H2/geometric premise on the deleted
complement, and no `G34NativeResult`, is assumed. The sparse-union budget
is exposed so that the resource constructor can discharge it quantitatively. -/
theorem native_partition_result_after_actual_bank_reference_with_triangle_monitors {I : Type}
    (F : Set (Multiset I)) (C α ζ : ℝ) (h qStat : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h) (hζ : 0 < ζ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (κ ηPack τ Λ qCore ρ τSel : ℝ) (t : ℕ),
        0 < κ → 0 < ηPack → 0 < τ → 0 < Λ → Odd t → 3 ≤ t →
      ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (W Wcore : Finset V) (D DT : Finset (Finset V))
        (R T Bank : Finset (Sym2 V))
        (E₀ : Finset (Sym2 {x // x ∈ W}))
        (D₀ : Finset (Finset {x // x ∈ W})) (dU : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) →
        CommonNbrCond H F α → HingeCond H F α h →
        S07V45.CorePathContract H.G H.lab F Wcore t →
        IsDecomposition H F (cover D) D → Basal H F R →
        IsDecomposition H F T DT → Basal H F Bank →
        Disjoint (cover D) T → Disjoint R (cover D ∪ T) →
        Disjoint Bank ((cover D ∪ R) ∪ T) →
        IsDecomposition
          (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
            Host {x // x ∈ W} I) F E₀ D₀ →
        let U := ((cover D ∪ R) ∪ T) ∪ Bank
        Disjoint (SampledResource.lift W E₀) U →
        Basal H F (U ∪ SampledResource.lift W E₀) →
        (∀ v, SparseEdge.degIn U v ≤ dU) →
        ((dU + W.card : ℕ) : ℝ) ≤ ε * Fintype.card V →
        (∀ u v, H.G.Adj u v →
          κ * Fintype.card V ≤ (good H F D u v).card) →
        (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
          ∃ Ps Y : Finset (Sym2 V), R ∪ L = Ps ∪ Y ∧
            Disjoint Ps Y ∧ Basal H F Ps ∧
            (∀ e ∈ Y, ∀ v ∈ e, v ∈ Wcore) ∧
            (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
            IsPhysical H F Y) →
        (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤
          qCore / 64 * Fintype.card V) →
        (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤ ρ * Fintype.card V) →
        (∀ v, (SelSimul.edeg R v : ℝ) ≤ τSel * Fintype.card V) →
        ∀ (ν : Type) [Fintype ν] (w : ν → Finset V → ℝ),
        (Fintype.card ν:ℝ) ≤ (Fintype.card V:ℝ)^qStat →
        (∀ k A, IsAllowed H F A → |w k A| ≤ 1) →
        G34NativePartitionResultRetainingPacking H F Wcore D R (U ∪ SampledResource.lift W E₀)
          qCore ρ ηPack τ Λ τSel (OriginalTriangleMonitorData H F φ w (ηPack+ζ) (τ+ζ)) := by
  obtain ⟨εExact,hεExact,nExact,hExact⟩ :=
    exact_complement_after_sampled_reference F C α h hC hα hh
  obtain ⟨εSeed,hεSeed,nSeed,hSeedClose⟩ :=
    seed_persistence_exact_with_pointwise_bound (F := F) hC hα h
  let K := (16*C+4)*provL α (2*C) h
  have hK : 0 ≤ K := mul_nonneg (by linarith) (provL_nonneg hα (by linarith) h)
  let ε := min εExact (min εSeed (min ζ (ζ/(K+2))))
  have hε : 0 < ε := lt_min hεExact (lt_min hεSeed (lt_min hζ (div_pos hζ (by linarith))))
  have hεExactCap : ε ≤ εExact := min_le_left _ _
  have hεSeedCap : ε ≤ εSeed := (min_le_right _ _).trans (min_le_left _ _)
  have hεζ : ε ≤ ζ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεK : (K+1)*ε ≤ ζ := by
    have hh : ε ≤ ζ/(K+2) := (min_le_right εExact (min εSeed (min ζ (ζ/(K+2))))).trans
      ((min_le_right εSeed (min ζ (ζ/(K+2)))).trans (min_le_right ζ (ζ/(K+2))))
    have hh' := (le_div_iff₀ (by linarith : (0:ℝ)<K+2)).mp hh
    nlinarith only [hh',hε]
  refine ⟨ε,hε,?_⟩
  intro κ ηPack τ Λ qCore ρ τSel t hκ hη hτ hΛ ht ht3
  let α' := min (α / 2) (S07V49.hingeConstB α 1 h)
  have hα' : 0 < α' := lt_min (by positivity)
    (S07V49.hingeConstB_pos hα (by norm_num) (by omega))
  obtain ⟨nFixed,hFixed⟩ :=
    g34_native_partition_result_on_fixed_prepared_window_with_triangle_monitors F (2*C) α' κ ηPack τ Λ
      qCore ρ τSel (2*h-3) t qStat (by linarith) hα' hκ hη hτ hΛ ht ht3
  refine ⟨max nExact (max nFixed (max nSeed 1)),?_⟩
  intro V _ H φ W Wcore D DT R T Bank E₀ D₀ dU hn hSeed hPhys h3 h4
    hPath hD hR hT hBank hDT hRdis hBankdis hEDec U hAvoid hBasal
    hUdeg hSmall hSupply hMode hDq hDcap hRdeg ν _ w hν hw
  have hE : E₀ ⊆ edges
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I) := by
    intro e he
    obtain ⟨S,hS,heS⟩ := hEDec.exists_mem he
    exact triEdges_subset_edges (hEDec.1 S hS) heS
  have hnExact : nExact ≤ Fintype.card V := by omega
  have hnFixed : nFixed ≤ Fintype.card V := by omega
  have hnSeed : nSeed ≤ Fintype.card V := by omega
  have hnPos : 0 < Fintype.card V := by omega
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hnPos
  have hSmallExact := hSmall.trans (mul_le_mul_of_nonneg_right hεExactCap hnR.le)
  obtain ⟨ψOld,hSeedOld,hPhysJ,h3J,h4J⟩ :=
    hExact H φ W U E₀ dU hnExact
      hSeed hPhys h3 h4 hBasal hE hUdeg hSmallExact
  let B := U∪SampledResource.lift W E₀
  have hBsub : B ⊆ edges H := CorePaid.basal_subset_edges hBasal
  obtain ⟨DB,hDB⟩ := hBasal
  have hDegree : ∀ v, degIn B v ≤ dU+W.card := by
    intro v
    have hv := SampledResource.full_reserved_degree_le H W U E₀ dU hUdeg hE v
    simpa only [B,SparseEdge.degIn,degIn] using hv
  have hdSeed : ((dU+W.card:ℕ):ℝ) ≤ εSeed*Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right hεSeedCap hnR.le)
  obtain ⟨ψ,hSeedJ,hSupp,hClose⟩ := hSeedClose H φ B DB (dU+W.card)
    hnSeed hSeed h4 hBsub hDB hDegree hdSeed
  have hDegreeR : ∀ v, (degIn B v:ℝ) ≤ ε*Fintype.card V := by
    intro v
    exact (show (degIn B v:ℝ) ≤ ((dU+W.card:ℕ):ℝ) by exact_mod_cast hDegree v).trans hSmall
  have hBcard := TriangleMonitors.edge_card_le_of_degree_bound B ε hDegreeR
  have hCloseScaled : ∀ A, IsAllowed (residual H B) F A →
      |ψ A-φ A| ≤ (K*ε)/Fintype.card V := by
    intro A hA
    have hh := hClose A hA
    change |ψ A-φ A| ≤ K*((dU+W.card:ℕ):ℝ)/(Fintype.card V:ℝ)^2 at hh
    apply hh.trans
    apply (div_le_div_iff₀ (pow_pos hnR _) hnR).mpr
    have hm := mul_le_mul_of_nonneg_left hSmall hK
    have hm' := mul_le_mul_of_nonneg_right hm hnR.le
    nlinarith only [hm']
  have h3J' : CommonNbrCond
      (subHost H (edges H \ (U ∪ SampledResource.lift W E₀))) F α' :=
    commonNbrCond_mono h3J (min_le_left _ _)
  have h4J' : HingeCond
      (subHost H (edges H \ (U ∪ SampledResource.lift W E₀))) F α' (2*h-3) :=
    hingeCond_mono h4J (min_le_right _ _)
  have hLift : Basal H F (SampledResource.lift W E₀) :=
    SampledResource.basal_lift H F W ⟨D₀,hEDec⟩
  have hResult := hFixed H ψ Wcore D DT R T Bank (SampledResource.lift W E₀)
    hnFixed hPath hSeedJ hPhysJ h3J' h4J'
    hPhys hD hR hT hBank hLift hDT hRdis hBankdis hAvoid
    hSupply hMode hDq hDcap hRdeg ν w hν hw
  apply hResult.map_data
  intro P₀ hData
  obtain ⟨hP₀,hAllow,hSparse,hQuota⟩ := hData
  refine ⟨hP₀,?_,?_⟩
  · have hdFull := TriangleMonitors.original_complement_degree B P₀ ε ηPack hDegreeR hSparse
    intro v
    exact (hdFull v).trans (mul_le_mul_of_nonneg_right (by linarith only [hεζ]) hnR.le)
  · intro k
    have hComp := TriangleMonitors.triangle_seed_statistic_comparison
      (by linarith : 0<C) hSeed B hBsub (K*ε) (mul_nonneg hK hε.le)
      hnPos hCloseScaled (w k) (hw k)
    have hComp' : |(∑ A ∈ allowed (residual H B) F, ψ A*w k A)-
        (∑ A ∈ allowed H F, φ A*w k A)| ≤ ζ*(Fintype.card V:ℝ)^2 := by
      have hScalar := mul_le_mul_of_nonneg_right hεK (sq_nonneg (Fintype.card V:ℝ))
      nlinarith only [hComp,hBcard,hScalar]
    have hTri := abs_add_le ((∑ A ∈ P₀, w k A)-(∑ A ∈ allowed (residual H B) F, ψ A*w k A))
      ((∑ A ∈ allowed (residual H B) F, ψ A*w k A)-(∑ A ∈ allowed H F, φ A*w k A))
    have hQuota' := hQuota k
    change |(∑ A ∈ P₀, w k A)-(∑ A ∈ allowed (residual H B) F, ψ A*w k A)| ≤
      τ*(Fintype.card V:ℝ)^2 at hQuota'
    have hSimpl : ((∑ A ∈ P₀, w k A)-(∑ A ∈ allowed (residual H B) F, ψ A*w k A))+
      ((∑ A ∈ allowed (residual H B) F, ψ A*w k A)-(∑ A ∈ allowed H F, φ A*w k A)) =
        (∑ A ∈ P₀, w k A)-(∑ A ∈ allowed H F, φ A*w k A) := by ring
    rw [hSimpl] at hTri
    nlinarith only [hTri,hQuota',hComp']

#print axioms native_partition_result_after_actual_bank_reference_with_triangle_monitors

end TypedTriangle.Vortex
