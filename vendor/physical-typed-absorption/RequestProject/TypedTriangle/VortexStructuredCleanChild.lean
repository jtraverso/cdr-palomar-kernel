/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRelativeCleanPaidChild
public import RequestProject.TypedTriangle.G4SameReferencePayment
public import RequestProject.TypedTriangle.G4PaidReferenceEdgePull
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex
open CatalogNative

private theorem degree_sdiff_le_change_decEq {X : Type}
    (S E : Finset (Sym2 X)) (v : X) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 X))
    (hBound : (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) S E) v : ℝ) ≤ b) :
    (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) S E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hBound

/-- The structured bank's actual paid vector can live on a smaller core.
It gives an exact 2C seed on the full reference window, preserves the same
clean hinge order, and retains every prescribed edge of the reference. -/
theorem structured_reference_clean_child
    (α β K ηSpec C ζ ξ : ℝ) (h Nbase Ns nPaid nGeometry : ℕ)
    (hC : 1 ≤ C) (hζ : 0 ≤ ζ) (hζSpec : ζ ≤ ηSpec) (hξ : 0 ≤ ξ)
    (hCap : PaidReferenceCap α h ηSpec nGeometry)
    (hspec : PaidSmoothAt α β K ηSpec h Nbase Ns nPaid)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (W0 W : Finset V) (hW0W : W0 ⊆ W)
    (μ : Finset {x : V // x ∈ W} → ℝ)
    (E0 : Finset (Sym2 {x : V // x ∈ W}))
    (D0 : Finset (Finset {x : V // x ∈ W})) (Ytot : Finset (Sym2 V))
    (hn : max 1 (max nPaid nGeometry) ≤ W.card) :
    let J : Host {x : V // x ∈ W} I :=
      ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    Dispersal.PreparedCore J.G J.lab F α h (max Nbase Ns) β →
    CommonNbrCond J F α → CleanHingeCond J F α h →
    (∀ T, IsAllowed J F T →
      (3 / (4 * C)) / W.card ≤ μ T ∧ μ T ≤ (5 * C / 4) / W.card) →
    (∀ e ∈ edges J, |bdry J F μ e - 1| ≤ ξ) →
    IsDecomposition J F E0 D0 → Ytot ⊆ edges H →
    SparseEdge.ind Ytot ∈ S07V42.LamCore H.G H.lab F W0 →
    Disjoint (SampledResource.lift W E0) Ytot →
    (∀ v, (SparseEdge.degIn (edges J \ E0) v : ℝ) ≤ ζ * W.card) →
    ζ ≤ α / (10 * (2 : ℝ) ^ h.choose 2) →
    K * (ξ + (5 * C / 2) * ⌊ζ * W.card⌋₊ / W.card) ≤ 1 / (4 * C) →
    let Jchild := subHost J (E0 ∪ SampledResource.pull W Ytot)
    ∃ ψ : Finset {x : V // x ∈ W} → ℝ,
      IsDiffuseSeed Jchild F (2 * C) ψ ∧
      (∀ T, |ψ T - μ T| ≤ K *
        (ξ + (5 * C / 2) * ⌊ζ * W.card⌋₊ / W.card) / W.card) ∧
      IsPhysical Jchild F (edges Jchild) ∧
      CommonNbrCond Jchild F (α / 2) ∧ CleanHingeCond Jchild F (α / 2) h ∧
      E0 ⊆ edges Jchild := by
  dsimp only
  intro P h3 hClean hμ hLoad hD hYE hLam hAvoid hHole hCleanBudget hBudget
  let J : Host {x : V // x ∈ W} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  have hLamFull : SparseEdge.ind Ytot ∈ S07V42.LamCore H.G H.lab F W :=
    (S07V37.lattice_mono (S07V42.indG_mono H.G hW0W) H.lab F) hLam
  have hY := paid_pull_subset_sampled_edges H W Ytot hYE
  have hYPhys : IsPhysical J F (SampledResource.pull W Ytot) :=
    pulled_paid_child_is_physical H F W Ytot hLamFull
  have hDis := pulled_paid_child_avoids_reference W E0 Ytot hAvoid
  have hWeights : ∀ T, IsAllowed J F T →
      ((1 - (1 / 4 : ℝ)) / C) / Fintype.card {x : V // x ∈ W} ≤ μ T ∧
      μ T ≤ ((1 + (1 / 4 : ℝ)) * C) / Fintype.card {x : V // x ∈ W} := by
    intro T hT
    simp only [Fintype.card_coe]
    convert hμ T hT using 1 <;> ring
  have hResult := relative_paid_child_with_clean_geometry α β K ηSpec C (1 / 4) ζ ξ
    h Nbase Ns nPaid nGeometry hC (by norm_num) le_rfl hζ hζSpec hξ hCap hspec
    J F μ (by simpa only [Fintype.card_coe] using hn) P h3 hClean hWeights hLoad
    E0 (SampledResource.pull W Ytot) D0 hD hY hYPhys hDis
    (by
      intro v
      exact degree_sdiff_le_change_decEq (edges J) E0 v
        (ζ * Fintype.card {x : V // x ∈ W})
        (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b))
        (@Sym2.instDecidableEq _ (Classical.decEq _))
        (by simpa only [Fintype.card_coe] using hHole v))
    hCleanBudget
    (by
      simp only [Fintype.card_coe]
      convert hBudget using 1 <;> ring)
  have hFactor : (1 + 4 * (1 / 4 : ℝ)) * C = 2 * C := by ring
  have hCorrection : 2 * ((1 + (1 / 4 : ℝ)) * C) = 5 * C / 2 := by ring
  obtain ⟨ψ,hψ,hClose,hPhysical,h3Child,hCleanChild⟩ := hResult
  have hE : E0 ⊆ edges J := by
    intro e he
    obtain ⟨T,hT,heT⟩ := hD.exists_mem he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hKeep : E0 ⊆ edges (subHost J (E0 ∪ SampledResource.pull W Ytot)) := by
    rw [Residual.edges_subHost_eq (union_subset hE hY)]
    exact subset_union_left
  refine ⟨ψ,?_,?_,?_,?_,?_,hKeep⟩
  · simpa only [hFactor,subHost,coe_union] using hψ
  · simpa only [hCorrection,Fintype.card_coe] using hClose
  · simpa only [subHost,coe_union] using hPhysical
  · simpa only [subHost,coe_union] using h3Child
  · simpa only [subHost,coe_union] using hCleanChild

#print axioms structured_reference_clean_child
end TypedTriangle.Vortex
