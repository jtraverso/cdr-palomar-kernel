/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4SampledReferenceComplement
public import RequestProject.TypedTriangle.VortexFixedWindowG34PartitionResult
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
theorem native_partition_result_after_actual_bank_reference {I : Type}
    (F : Set (Multiset I)) (C α : ℝ) (h : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h) :
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
        G34NativePartitionResult H F Wcore D R (U ∪ SampledResource.lift W E₀) qCore ρ ηPack τ Λ τSel := by
  obtain ⟨ε,hε,nExact,hExact⟩ :=
    exact_complement_after_sampled_reference F C α h hC hα hh
  refine ⟨ε,hε,?_⟩
  intro κ ηPack τ Λ qCore ρ τSel t hκ hη hτ hΛ ht ht3
  let α' := min (α / 2) (S07V49.hingeConstB α 1 h)
  have hα' : 0 < α' := lt_min (by positivity)
    (S07V49.hingeConstB_pos hα (by norm_num) (by omega))
  obtain ⟨nFixed,hFixed⟩ :=
    g34_native_partition_result_on_fixed_prepared_window F (2*C) α' κ ηPack τ Λ
      qCore ρ τSel (2*h-3) t (by linarith) hα' hκ hη hτ hΛ ht ht3
  refine ⟨max nExact nFixed,?_⟩
  intro V _ H φ W Wcore D DT R T Bank E₀ D₀ dU hn hSeed hPhys h3 h4
    hPath hD hR hT hBank hDT hRdis hBankdis hEDec U hAvoid hBasal
    hUdeg hSmall hSupply hMode hDq hDcap hRdeg
  have hE : E₀ ⊆ edges
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I) := by
    intro e he
    obtain ⟨S,hS,heS⟩ := hEDec.exists_mem he
    exact triEdges_subset_edges (hEDec.1 S hS) heS
  obtain ⟨ψ,hSeedJ,hPhysJ,h3J,h4J⟩ :=
    hExact H φ W U E₀ dU ((le_max_left _ _).trans hn)
      hSeed hPhys h3 h4 hBasal hE hUdeg hSmall
  have h3J' : CommonNbrCond
      (subHost H (edges H \ (U ∪ SampledResource.lift W E₀))) F α' :=
    commonNbrCond_mono h3J (min_le_left _ _)
  have h4J' : HingeCond
      (subHost H (edges H \ (U ∪ SampledResource.lift W E₀))) F α' (2*h-3) :=
    hingeCond_mono h4J (min_le_right _ _)
  have hLift : Basal H F (SampledResource.lift W E₀) :=
    SampledResource.basal_lift H F W ⟨D₀,hEDec⟩
  exact hFixed H ψ Wcore D DT R T Bank (SampledResource.lift W E₀)
    ((le_max_right _ _).trans hn) hPath hSeedJ hPhysJ h3J' h4J'
    hPhys hD hR hT hBank hLift hDT hRdis hBankdis hAvoid
    hSupply hMode hDq hDcap hRdeg

#print axioms native_partition_result_after_actual_bank_reference

end TypedTriangle.Vortex
