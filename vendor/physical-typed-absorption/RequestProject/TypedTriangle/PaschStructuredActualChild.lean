module
public import RequestProject.TypedTriangle.VortexStructuredCleanChild
public import RequestProject.TypedTriangle.VortexRawPathsFutureProtection
public import RequestProject.TypedTriangle.PaschRawPathsReservedChildRetainingDecomposition
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open CatalogNative IntrinsicRawPathsPreparedVortex

private theorem degree_sdiff_change_decEq {X : Type}
    (S E : Finset (Sym2 X)) (v : X) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 X))
    (hBound : (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) S E) v : ℝ) ≤ b) :
    (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) S E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hBound

private theorem lift_pull_of_supported_payload {X : Type} [Fintype X]
    (G : SimpleGraph X) (W0 W : Finset X) (Y : Finset (Sym2 X))
    (hW : W0 ⊆ W) (hY : Y ⊆ S07V43.childEdges G W0) :
    SampledResource.lift W (SampledResource.pull W Y) = Y := by
  apply Finset.Subset.antisymm
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    exact mem_preimage.mp hg
  · intro f hf
    induction f using Sym2.ind with
    | _ u v =>
      have hc : (S07V42.indG G W0).Adj u v := SparseEdge.mem_edges.mp (hY hf)
      let uW : {x // x ∈ W} := ⟨u,hW hc.2.1⟩
      let vW : {x // x ∈ W} := ⟨v,hW hc.2.2⟩
      exact mem_image.mpr ⟨s(uW,vW),mem_preimage.mpr hf,rfl⟩

/-- The actual structured reference and actual literal paid decomposition
produce the reserved outer child, without rerunning the bank or packing. -/
theorem structured_reference_reserved_actual_child
    {X Y I : Type} [Fintype X] [Fintype Y] {F : Set (Multiset I)}
    {α₀ q Craw : ℝ} {βRaw : ℕ → ℝ} {h N M d T m : ℕ} {a εRoute t : ℝ}
    {Hraw : Host Y I} {μraw : Finset Y → ℝ}
    (tail : IntrinsicRawPathsPreparedVortex F α₀ q Craw βRaw h N M d T m a εRoute t Hraw μraw)
    (α β K ηSpec C ζ ξ ζState : ℝ) (Nbase Ns nPaid nGeometry : ℕ)
    (hC : 1 ≤ C) (hζ : 0 ≤ ζ) (hζSpec : ζ ≤ ηSpec) (hξ : 0 ≤ ξ)
    (hζState : ζ ≤ ζState)
    (hCap : PaidReferenceCap α h ηSpec nGeometry)
    (hspec : PaidSmoothAt α β K ηSpec h Nbase Ns nPaid)
    (Hactual : Host X I) (ι : Survivors tail.head.trim ↪ X)
    (hRawAdj : ∀ u v, tail.preparedHost.G.Adj u v ↔ Hactual.G.Adj (ι u) (ι v))
    (hRawLab : ∀ u, tail.preparedHost.lab u = Hactual.lab (ι u)) :
    let e := embeddingWindowEquiv ι
    let Wfull := embeddingWindow ι
    letI : DecidableEq {y // y ∈ Wfull} := Classical.decEq _
    let JW := embeddingWindowHost ι Hactual
    ∀ (W0 : Finset X), W0 ⊆ Wfull →
    ∀ (μ : Finset {y // y ∈ Wfull} → ℝ)
      (E0 : Finset (Sym2 {y // y ∈ Wfull}))
      (D0 : Finset (Finset {y // y ∈ Wfull})) (Ytot : Finset (Sym2 X))
      (R : Finset (Sym2 X)) (Dpaid Uambient : Finset (Finset X)),
      max 1 (max nPaid nGeometry) ≤ Wfull.card →
      Dispersal.PreparedCore JW.G JW.lab F α h (max Nbase Ns) β →
      CommonNbrCond JW F α → CleanHingeCond JW F α h →
      (∀ Q, IsAllowed JW F Q →
        (3/(4*C))/Wfull.card ≤ μ Q ∧ μ Q ≤ (5*C/4)/Wfull.card) →
      (∀ f ∈ edges JW, |bdry JW F μ f-1| ≤ ξ) →
      IsDecomposition JW F E0 D0 → Ytot ⊆ edges Hactual →
      SparseEdge.ind Ytot ∈ S07V42.LamCore Hactual.G Hactual.lab F W0 →
      Ytot ⊆ S07V43.childEdges Hactual.G W0 →
      Disjoint (SampledResource.lift Wfull E0) Ytot →
      (∀ v, (SparseEdge.degIn (edges JW \ E0) v : ℝ) ≤ ζ*Wfull.card) →
      ζ ≤ α/(10*(2 : ℝ)^h.choose 2) →
      K*(ξ+(5*C/2)*⌊ζ*Wfull.card⌋₊/Wfull.card) ≤ 1/(4*C) →
      edges JW ∩ triEdges (tail.nextRawWindow.map e.toEmbedding) ⊆ E0 →
      R ⊆ edges Hactual →
      Disjoint R (SampledResource.lift Wfull E0 ∪ Ytot) →
      IsDecomposition Hactual F
        (edges Hactual \ (R ∪ (SampledResource.lift Wfull E0 ∪ Ytot))) Dpaid →
      Dpaid ⊆ Uambient →
      ∃ child : ActualState tail (2*C) (α/2) ζState,
      ∃ P : Finset (Sym2 X), Basal Hactual F P ∧
        Disjoint P (R ∪ embeddedEdges ι (edges child.host)) ∧
        Disjoint R (embeddedEdges ι (edges child.host)) ∧
        edges Hactual = (P ∪ R) ∪ embeddedEdges ι (edges child.host) ∧
        IsDecomposition Hactual F P Dpaid ∧ Dpaid ⊆ Uambient ∧
        P = edges Hactual \ (R ∪ (SampledResource.lift Wfull E0 ∪ Ytot)) ∧
        embeddedEdges ι (edges child.host) = SampledResource.lift Wfull E0 ∪ Ytot := by
  intro e Wfull
  letI : DecidableEq {y // y ∈ Wfull} := Classical.decEq _
  intro JW W0 hW0 μ E0 D0 Ytot R Dpaid Uambient
    hn hP h3 hClean hμ hLoad hD0 hYE hLam hYCore hAvoid hHole hCleanBudget hBudget
    hFuture hR hReserved hDpaid hUniverse
  let Jchild := subHost JW (E0 ∪ SampledResource.pull Wfull Ytot)
  obtain ⟨ψ,hSeed,hClose,hPhysical,h3Child,hCleanChild,hKeep⟩ :=
    structured_reference_clean_child α β K ηSpec C ζ ξ h Nbase Ns nPaid nGeometry
      hC hζ hζSpec hξ hCap hspec Hactual F W0 Wfull hW0 μ E0 D0 Ytot hn
      hP h3 hClean hμ hLoad hD0 hYE hLam hAvoid
      (by
        intro v
        exact degree_sdiff_change_decEq (edges JW) E0 v (ζ*Wfull.card)
          (@Sym2.instDecidableEq _ (Classical.decEq _))
          (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b)) (hHole v))
      hCleanBudget hBudget
  have hKeepChild : E0 ⊆ edges Jchild := by
    simpa only [Jchild,JW,embeddingWindowHost,subHost,Finset.coe_union] using hKeep
  have hE : E0 ⊆ edges JW := by
    intro f hf
    obtain ⟨Q,hQ,hfQ⟩ := hD0.exists_mem hf
    exact triEdges_subset_edges (hD0.1 Q hQ) hfQ
  have hPull := paid_pull_subset_sampled_edges Hactual Wfull Ytot hYE
  have hLiftPull := lift_pull_of_supported_payload Hactual.G W0 Wfull Ytot hW0 hYCore
  have hLift : SampledResource.lift Wfull (edges Jchild) =
      SampledResource.lift Wfull E0 ∪ Ytot := by
    rw [Residual.edges_subHost_eq (union_subset hE hPull)]
    change (E0 ∪ SampledResource.pull Wfull Ytot).image (SampledResource.edgeLift Wfull) = _
    rw [image_union]
    change SampledResource.lift Wfull E0 ∪
      SampledResource.lift Wfull (SampledResource.pull Wfull Ytot) = _
    rw [hLiftPull]
  have hUniformHole : ∀ v,
      (SparseEdge.degIn (edges JW \ edges Jchild) v : ℝ) ≤
        ζState*Fintype.card {y // y ∈ Wfull} := by
    intro v
    have hSub : edges JW \ edges Jchild ⊆ edges JW \ E0 := by
      intro f hf
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp hf).1,fun h => (mem_sdiff.mp hf).2 (hKeepChild h)⟩
    have hDeg : (SparseEdge.degIn (edges JW \ edges Jchild) v : ℝ) ≤
        SparseEdge.degIn (edges JW \ E0) v := by
      exact_mod_cast card_le_card (filter_subset_filter (p := fun f => v ∈ f) hSub)
    have hScale := mul_le_mul_of_nonneg_right hζState (Nat.cast_nonneg Wfull.card)
    simpa only [Fintype.card_coe] using hDeg.trans ((hHole v).trans hScale)
  have hNext : tail.nextPreparedEdges.image (Sym2.map e) ⊆ edges Jchild := by
    apply nextPreparedEdges_mapped_subset_child tail e JW Jchild hRawAdj
    exact hFuture.trans hKeepChild
  have hPaid : IsDecomposition Hactual F
      (edges Hactual \ (R ∪ SampledResource.lift Wfull (edges Jchild))) Dpaid := by
    rw [hLift]
    exact hDpaid
  obtain ⟨child,P,hBasal,hDis,hRes,hPartition,hDec,hU,hPeq,hCanon⟩ :=
    raw_paths_reserved_actual_child_retaining_decomposition tail Hactual ι
      (2*C) (α/2) ζState R hR hRawAdj hRawLab Jchild ψ (subHost_le JW _) rfl
      (by simpa only [Jchild,JW,embeddingWindowHost,subHost,Finset.coe_union] using hSeed)
      (by simpa only [Jchild,JW,embeddingWindowHost,subHost,Finset.coe_union] using hPhysical)
      (by simpa only [Jchild,JW,embeddingWindowHost,subHost,Finset.coe_union] using h3Child)
      (by simpa only [Jchild,JW,embeddingWindowHost,subHost,Finset.coe_union] using hCleanChild)
      hUniformHole hNext Dpaid Uambient hPaid hUniverse (by rw [hLift]; exact hReserved)
  refine ⟨child,P,hBasal,hDis,hRes,hPartition,hDec,hU,?_,hCanon.symm.trans hLift⟩
  rw [hPeq,hLift]

/-- The same construction for an inner layer, whose reserved edge set is empty. -/
theorem structured_reference_actual_child
    {X Y I : Type} [Fintype X] [Fintype Y] {F : Set (Multiset I)}
    {α₀ q Craw : ℝ} {βRaw : ℕ → ℝ} {h N M d T m : ℕ} {a εRoute t : ℝ}
    {Hraw : Host Y I} {μraw : Finset Y → ℝ}
    (tail : IntrinsicRawPathsPreparedVortex F α₀ q Craw βRaw h N M d T m a εRoute t Hraw μraw)
    (α β K ηSpec C ζ ξ ζState : ℝ) (Nbase Ns nPaid nGeometry : ℕ)
    (hC : 1 ≤ C) (hζ : 0 ≤ ζ) (hζSpec : ζ ≤ ηSpec) (hξ : 0 ≤ ξ)
    (hζState : ζ ≤ ζState)
    (hCap : PaidReferenceCap α h ηSpec nGeometry)
    (hspec : PaidSmoothAt α β K ηSpec h Nbase Ns nPaid)
    (Hactual : Host X I) (ι : Survivors tail.head.trim ↪ X)
    (hRawAdj : ∀ u v, tail.preparedHost.G.Adj u v ↔ Hactual.G.Adj (ι u) (ι v))
    (hRawLab : ∀ u, tail.preparedHost.lab u = Hactual.lab (ι u)) :
    let e := embeddingWindowEquiv ι
    let Wfull := embeddingWindow ι
    letI : DecidableEq {y // y ∈ Wfull} := Classical.decEq _
    let JW := embeddingWindowHost ι Hactual
    ∀ (W0 : Finset X), W0 ⊆ Wfull →
    ∀ (μ : Finset {y // y ∈ Wfull} → ℝ)
      (E0 : Finset (Sym2 {y // y ∈ Wfull}))
      (D0 : Finset (Finset {y // y ∈ Wfull})) (Ytot : Finset (Sym2 X))
      (Dpaid Uambient : Finset (Finset X)),
      max 1 (max nPaid nGeometry) ≤ Wfull.card →
      Dispersal.PreparedCore JW.G JW.lab F α h (max Nbase Ns) β →
      CommonNbrCond JW F α → CleanHingeCond JW F α h →
      (∀ Q, IsAllowed JW F Q →
        (3/(4*C))/Wfull.card ≤ μ Q ∧ μ Q ≤ (5*C/4)/Wfull.card) →
      (∀ f ∈ edges JW, |bdry JW F μ f-1| ≤ ξ) →
      IsDecomposition JW F E0 D0 → Ytot ⊆ edges Hactual →
      SparseEdge.ind Ytot ∈ S07V42.LamCore Hactual.G Hactual.lab F W0 →
      Ytot ⊆ S07V43.childEdges Hactual.G W0 →
      Disjoint (SampledResource.lift Wfull E0) Ytot →
      (∀ v, (SparseEdge.degIn (edges JW \ E0) v : ℝ) ≤ ζ*Wfull.card) →
      ζ ≤ α/(10*(2 : ℝ)^h.choose 2) →
      K*(ξ+(5*C/2)*⌊ζ*Wfull.card⌋₊/Wfull.card) ≤ 1/(4*C) →
      edges JW ∩ triEdges (tail.nextRawWindow.map e.toEmbedding) ⊆ E0 →
      IsDecomposition Hactual F
        (edges Hactual \ (SampledResource.lift Wfull E0 ∪ Ytot)) Dpaid →
      Dpaid ⊆ Uambient →
      ∃ child : ActualState tail (2*C) (α/2) ζState,
      ∃ P : Finset (Sym2 X), Basal Hactual F P ∧
        Disjoint P (embeddedEdges ι (edges child.host)) ∧
        edges Hactual = P ∪ embeddedEdges ι (edges child.host) ∧
        IsDecomposition Hactual F P Dpaid ∧ Dpaid ⊆ Uambient ∧
        P = edges Hactual \ (SampledResource.lift Wfull E0 ∪ Ytot) ∧
        embeddedEdges ι (edges child.host) = SampledResource.lift Wfull E0 ∪ Ytot := by
  intro e Wfull
  letI : DecidableEq {y // y ∈ Wfull} := Classical.decEq _
  intro JW W0 hW0 μ E0 D0 Ytot Dpaid Uambient
    hn hP h3 hClean hμ hLoad hD0 hYE hLam hYCore hAvoid hHole hCleanBudget hBudget
    hFuture hDpaid hUniverse
  obtain ⟨child,P,hBasal,hDis,hRes,hPartition,hDec,hU,hPeq,hCanon⟩ :=
    structured_reference_reserved_actual_child tail α β K ηSpec C ζ ξ ζState
      Nbase Ns nPaid nGeometry hC hζ hζSpec hξ hζState hCap hspec Hactual ι hRawAdj hRawLab
      W0 hW0 μ E0 D0 Ytot ∅ Dpaid Uambient hn hP h3 hClean hμ hLoad hD0 hYE hLam hYCore
      hAvoid hHole hCleanBudget hBudget hFuture (empty_subset _) (by simp)
      (by simpa only [empty_union] using hDpaid) hUniverse
  refine ⟨child,P,hBasal,?_,?_,hDec,hU,?_,hCanon⟩
  · simpa only [empty_union] using hDis
  · simpa only [union_empty] using hPartition
  · simpa only [empty_union] using hPeq

#print axioms structured_reference_reserved_actual_child
#print axioms structured_reference_actual_child
end TypedTriangle.Vortex
