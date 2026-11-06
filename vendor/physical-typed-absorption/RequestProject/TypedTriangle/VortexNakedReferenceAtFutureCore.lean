/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalNakedReferenceSchedule
public import RequestProject.S07V31.TerminalAbsorber
public import RequestProject.TypedTriangle.SampledBasalLift
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

/-- On a prescribed window, build the reference from its naked approximate
weights, preserving the future core while avoiding the actual outer bank.
The naked weights need not be a fractional decomposition. -/
theorem naked_reference_at_preserving_future_core {I : Type}
    (F : Set (Multiset I)) (a b α ρ η ε γ : ℝ) (h n₀ : ℕ)
    (hReference : NakedReferenceAt F a b α ρ η ε γ h n₀) :
        ∀ {V : Type} [Fintype V] (H : Host V I) (W : Finset V),
          letI : DecidableEq {x // x ∈ W} := Classical.decEq _
          let J : Host {x // x ∈ W} I :=
            ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
          ∀ (μ : Finset {x // x ∈ W} → ℝ)
            (U : Finset {x // x ∈ W}) (B : Finset (Sym2 V)) (dB : ℕ),
            n₀ ≤ W.card → CommonNbrCond J F α → HingeCond J F α h →
            (∀ T, IsAllowed J F T → a / W.card ≤ μ T ∧ μ T ≤ b / W.card) →
            (∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ε) →
            (U.card : ℝ) ≤ ρ * W.card →
            Disjoint (SampledResource.lift W (edges J ∩ triEdges U)) B →
            Basal H F B → (∀ v, degIn B v ≤ dB) →
            (dB : ℝ) ≤ γ * W.card →
            ∃ E₀ D₀, edges J ∩ triEdges U ⊆ E₀ ∧ E₀ ⊆ edges J ∧
              IsDecomposition J F E₀ D₀ ∧
              Disjoint (SampledResource.lift W E₀) B ∧
              Basal H F (B ∪ SampledResource.lift W E₀) ∧
              (∀ v, (degIn (edges J \ E₀) v : ℝ) ≤ η * W.card) ∧
              (subHost J E₀).G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) =
                J.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) := by
  intro V _ H W
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  dsimp only
  intro μ U B dB hn h3 h4 hμ hLoad hU hProtect hB hBdeg hBcap
  let J : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  have hPullDis : Disjoint (edges J ∩ triEdges U) (SampledResource.pull W B) := by
    apply Finset.disjoint_left.mpr
    intro e he hp
    exact Finset.disjoint_left.mp hProtect (Finset.mem_image.mpr ⟨e,he,rfl⟩)
      (Finset.mem_preimage.mp hp)
  have hPullDeg : ∀ v, degIn (SampledResource.pull W B) v ≤ dB := by
    intro v
    have hp : degIn (SampledResource.pull W B) v ≤ degIn B v.val := by
      unfold degIn
      apply card_le_card_of_injOn (SampledResource.edgeLift W)
      · intro e he
        obtain ⟨heB,hve⟩ := mem_filter.mp he
        exact mem_filter.mpr ⟨mem_preimage.mp heB,Sym2.mem_map.mpr ⟨v,hve,rfl⟩⟩
      · exact (SampledResource.edgeLift_injective W).injOn
    exact hp.trans (hBdeg v.val)
  have hFutureDegree : ∀ v, degIn (edges J ∩ triEdges U) v ≤ U.card := by
    intro v
    have hsub := Finset.card_le_card (Finset.filter_subset_filter
      (p := fun e : Sym2 {x // x ∈ W} => v ∈ e)
      (show edges J ∩ triEdges U ⊆ triEdges U from inter_subset_right))
    exact hsub.trans (S07V31.degIn_triEdges_le U v)
  obtain ⟨E₀,D₀,hFuture,hEdges,hDec,hAvoid,hHole⟩ :=
    hReference J μ (edges J ∩ triEdges U) (SampledResource.pull W B) U.card dB
      (by simpa only [Fintype.card_coe] using hn) h3 h4
      (by simpa only [Fintype.card_coe] using hμ) hLoad
      inter_subset_left hPullDis hFutureDegree
      (by simpa only [Fintype.card_coe] using hU) hPullDeg
      (by simpa only [Fintype.card_coe] using hBcap)
  have hGraph : (subHost J E₀).G.comap
      (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) =
      J.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change (subHost J E₀).G.Adj x.val y.val ↔ J.G.Adj x.val y.val
    constructor
    · intro hxy
      exact subHost_le J E₀ hxy
    · intro hxy
      have he : s(x.val,y.val) ∈ E₀ := hFuture (mem_inter.mpr
        ⟨by simpa [edges] using hxy,mem_triEdges.mpr ⟨x.property,y.property,hxy.ne⟩⟩)
      exact ⟨⟨he,hxy.ne⟩,hxy⟩
  have hAvoidLift := SampledResource.lift_disjoint_of_pull_disjoint W E₀ B hAvoid
  have hLiftBasal : Basal H F (SampledResource.lift W E₀) :=
    SampledResource.basal_lift H F W ⟨D₀,hDec⟩
  exact ⟨E₀,D₀,hFuture,hEdges,hDec,hAvoidLift,
    Basal.union hB hLiftBasal hAvoidLift.symm,
    by simpa only [Fintype.card_coe] using hHole,hGraph⟩

#print axioms naked_reference_at_preserving_future_core

end TypedTriangle.Vortex
