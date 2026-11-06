module
public import RequestProject.TypedTriangle.ExplicitStructuredActivatedLayer
public import RequestProject.TypedTriangle.VortexStructuredCleanPaidLayerState
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open CatalogNative CorePaid BasalIncidence SelSimul S07V40 S07V42 S07V43 S07V44 S07V47

def cleanLayerThreshold (α C βBank γRef q αPool εRoute : ℝ)
    (h t nRef nPaid nGeometry : ℕ) : ℕ :=
  max (layerThreshold α (2*C) βBank γRef q αPool εRoute h t nRef)
    ⌈2*((max 1 (max nPaid nGeometry):ℕ):ℝ)/q⌉₊

private theorem degree_sdiff_le_change_decEq {X : Type}
    (S E : Finset (Sym2 X)) (v : X) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 X))
    (hBound : (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) S E) v : ℝ) ≤ b) :
    (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) S E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hBound

private theorem lift_pull_of_core_support {V : Type} [Fintype V]
    (H : SimpleGraph V) (W0 W : Finset V) (Y : Finset (Sym2 V))
    (hW : W0 ⊆ W) (hY : Y ⊆ childEdges H W0) :
    SampledResource.lift W (SampledResource.pull W Y) = Y := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact mem_preimage.mp hf
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hc : (indG H W0).Adj u v := SparseEdge.mem_edges.mp (hY he)
      let uW : {x // x ∈ W} := ⟨u,hW hc.2.1⟩
      let vW : {x // x ∈ W} := ⟨v,hW hc.2.2⟩
      exact mem_image.mpr ⟨s(uW,vW),mem_preimage.mpr he,rfl⟩

theorem structured_clean_paid_layer_state_explicit {I : Type}
    (F : Set (Multiset I)) (α C βBank αRaw : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hβBank : 0 < βBank)
    (hβα : βBank ≤ α) (hh : 6 ≤ h) :
    let εOuter := complementBudget (2*C) α h
    let γStock := resourceStockBudget α (2*C)
    let ηBank := CatalogNative.Explicit.bankProtectionBudget α βBank h
      ∀ (β K ηSpec a b ρFuture ζ εRef γRef : ℝ)
        (nRef Nbase Ns nPaid nGeometry : ℕ),
      0 < γRef → a ≤ 3/(4*C) → 5*C/4 ≤ b → 0 ≤ ζ → ζ ≤ ηSpec →
      ζ ≤ αRaw/(10*(2:ℝ)^h.choose 2) →
      PaidReferenceCap αRaw h ηSpec nGeometry →
      PaidSmoothAt αRaw β K ηSpec h Nbase Ns nPaid →
      NakedReferenceAt F a b αRaw ρFuture ζ εRef γRef h nRef →
      ∀ q : ℝ, 0 < q → 4*q ≤ εOuter →
      ∀ (αPool εRoute : ℝ) (t : ℕ),
        0 < αPool → 0 < εRoute → Odd t → 3 ≤ t →
        let θT := layerTerminalBudget α (2*C) βBank γRef q αPool εRoute h t
        let n₀ := cleanLayerThreshold α C βBank γRef q αPool εRoute h t nRef nPaid nGeometry
        ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
          (W : Finset V) (A : Finset (Survivors (univ \ W)))
          (U : Finset {x // x ∈ W}) (T : Finset (Sym2 V))
          (DT : Finset (Finset V)) (dT dS : ℕ) (μ : Finset {x // x ∈ W} → ℝ) (ξ : ℝ),
          let W0 := W \ liftVertexSet (univ \ W) A
          letI : DecidableEq {x // x ∈ W} := Classical.decEq _
          let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
          let S := SampledResource.lift W (edges JW ∩ triEdges U)
          n₀ ≤ Fintype.card V → IsDiffuseSeed H F (2*C) φ → IsPhysical H F (edges H) →
          CommonNbrCond H F α → HingeCond H F α h →
          q*Fintype.card V/2 ≤ W.card → (W.card:ℝ) < 2*q*Fintype.card V →
          (q/2)*Fintype.card V/2 ≤ W0.card →
          (∀ u v : V, u ≠ v → ∀ k : I,
            ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
            (q/2)*αPool*Fintype.card V/2 ≤ ((commonNbrs H k u v) ∩ W0).card) →
          S07V27.RouteProp H.G H.lab F t εRoute W0 →
          CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F βBank →
          HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F βBank h →
          Dispersal.PreparedCore JW.G JW.lab F αRaw h (max Nbase Ns) β →
          CommonNbrCond JW F αRaw → CleanHingeCond JW F αRaw h →
          (∀ Q, IsAllowed JW F Q → (3/(4*C))/W.card ≤ μ Q ∧
            μ Q ≤ (5*C/4)/W.card) →
          0 ≤ ξ → ξ ≤ εRef →
          (∀ e ∈ edges JW, |bdry JW F μ e-1| ≤ ξ) →
          K*(ξ+(5*C/2)*⌊ζ*W.card⌋₊/W.card) ≤ 1/(4*C) →
          (U.card:ℝ) ≤ ρFuture*W.card →
          Disjoint W0 (U.image Subtype.val) →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ γStock*Fintype.card V →
          (dS:ℝ) ≤ (ηBank/2)*W0.card →
          IsDecomposition H F T DT → Disjoint T S →
          (∀ v, degIn T v ≤ dT) → (dT:ℝ) ≤ θT*Fintype.card V →
          ∃ (E₀ : Finset (Sym2 {x // x ∈ W}))
            (D₀ : Finset (Finset {x // x ∈ W})) (Ytot : Finset (Sym2 V)),
            IsDecomposition JW F E₀ D₀ ∧ edges JW ∩ triEdges U ⊆ E₀ ∧
            let Jchild := subHost JW (E₀ ∪ SampledResource.pull W Ytot)
            ∃ ψ : Finset {x // x ∈ W} → ℝ,
              IsDiffuseSeed Jchild F (2*C) ψ ∧
              (∀ Q, |ψ Q-μ Q| ≤ K*(ξ+(5*C/2)*⌊ζ*W.card⌋₊/W.card)/W.card) ∧
              IsPhysical Jchild F (edges Jchild) ∧
              CommonNbrCond Jchild F (αRaw/2) ∧ CleanHingeCond Jchild F (αRaw/2) h ∧
              E₀ ⊆ edges Jchild ∧
              (∀ v, (SparseEdge.degIn (edges JW \ edges Jchild) v : ℝ) ≤ ζ*W.card) ∧
              Jchild.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) =
                JW.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) ∧
              SampledResource.lift W (edges Jchild) = SampledResource.lift W E₀ ∪ Ytot ∧
              Basal H F (edges H \ (T ∪ SampledResource.lift W (edges Jchild))) ∧
              Disjoint T (SampledResource.lift W (edges Jchild)) := by
  intro earlyOuter earlyStock earlyBank
  intro β K ηSpec a b ρFuture ζ εRef γRef nRef Nbase Ns nPaid nGeometry
    hγRef hLower hUpper hζ hζSpec hζClean hCap hPaid hReference
  intro q hq hqε αPool εRoute t hαPool hεRoute ht ht3
  let nLayer := layerThreshold α (2*C) βBank γRef q αPool εRoute h t nRef
  let nChild := max 1 (max nPaid nGeometry)
  intro θTarget nTarget
  intro V _ H φ W A U T DT dT dS μ ξ W0
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  dsimp only
  let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let S := SampledResource.lift W (edges JW ∩ triEdges U)
  intro hn hSeed hPhys h3 h4 hWlo hWhi hWcore hPool hRoute h3A h4A
    hPc h3W hClean hμ hξ hξRef hLoad hBudget hU hWU hSd hScap hSMacro hT hTS hTd hTcap
  change max nLayer ⌈2*(nChild:ℝ)/q⌉₊ ≤ Fintype.card V at hn
  have hnLayer : nLayer ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnChild : nChild ≤ W.card := by
    have hce : (⌈2*(nChild:ℝ)/q⌉₊:ℝ) ≤ Fintype.card V := by
      exact_mod_cast (le_max_right _ _).trans hn
    have ht := (div_le_iff₀ hq).mp (Nat.le_ceil (2*(nChild:ℝ)/q))
    have hs := mul_le_mul_of_nonneg_right hce hq.le
    exact_mod_cast (show (nChild:ℝ) ≤ W.card by nlinarith only [hWlo,ht,hs])
  have hWeights : ∀ Q, IsAllowed JW F Q → a/W.card ≤ μ Q ∧ μ Q ≤ b/W.card := by
    intro Q hQ
    exact ⟨(div_le_div_of_nonneg_right hLower (Nat.cast_nonneg W.card)).trans (hμ Q hQ).1,
      (hμ Q hQ).2.trans (div_le_div_of_nonneg_right hUpper (Nat.cast_nonneg W.card))⟩
  have hRefLoad : ∀ e ∈ edges JW, |bdry JW F μ e-1| ≤ εRef :=
    fun e he => (hLoad e he).trans hξRef
  obtain ⟨E₀,D₀,Ytot,hEDec,hFuture,hHole,hYE,hYCore,hLam,hAvoid,hOuter,hTerminal⟩ :=
    structured_activated_naked_layer_before_reference_explicit F α (2*C) βBank αRaw h
      hα (by linarith) hβBank hβα hh a b ρFuture ζ εRef γRef nRef hγRef hReference q hq hqε
      αPool εRoute t hαPool hεRoute ht ht3 H φ W A U T DT dT dS μ hnLayer hSeed hPhys h3 h4 hWlo hWhi hWcore
      hPool hRoute h3A h4A h3W hClean.hingeCond hWeights hRefLoad hU hWU hSd hScap
      hSMacro hT hTS hTd hTcap
  obtain ⟨ψ,hψ,hClose,hPhysical,h3Child,hCleanChild,hEkeep⟩ :=
    structured_reference_clean_child αRaw β K ηSpec C ζ ξ h Nbase Ns nPaid nGeometry
      hC hζ hζSpec hξ hCap hPaid H F W0 W Finset.sdiff_subset μ E₀ D₀ Ytot hnChild
      hPc h3W hClean hμ hLoad hEDec hYE hLam hAvoid
      (by
        intro v
        exact degree_sdiff_le_change_decEq (edges JW) E₀ v (ζ*W.card)
          (@Sym2.instDecidableEq _ (Classical.decEq _))
          (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b)) (hHole v))
      hζClean hBudget
  let Jchild := subHost JW (E₀ ∪ SampledResource.pull W Ytot)
  have hFutureGraph : Jchild.G.comap
      (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) =
      JW.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change Jchild.G.Adj x.val y.val ↔ JW.G.Adj x.val y.val
    constructor
    · intro hxy
      exact subHost_le JW _ hxy
    · intro hxy
      have he : s(x.val,y.val) ∈ E₀ := hFuture (mem_inter.mpr
        ⟨by simpa [edges,JW] using hxy,mem_triEdges.mpr ⟨x.property,y.property,hxy.ne⟩⟩)
      exact ⟨⟨mem_union_left _ he,hxy.ne⟩,hxy⟩
  have hEedges : E₀ ⊆ edges JW := by
    intro e he
    obtain ⟨Q,hQ,heQ⟩ := hEDec.exists_mem he
    exact triEdges_subset_edges (hEDec.1 Q hQ) heQ
  have hYpull : SampledResource.pull W Ytot ⊆ edges JW :=
    CatalogNative.paid_pull_subset_sampled_edges H W Ytot hYE
  have hLiftPull := lift_pull_of_core_support H.G W0 W Ytot Finset.sdiff_subset hYCore
  have hChildAmbient : SampledResource.lift W (edges Jchild) =
      SampledResource.lift W E₀ ∪ Ytot := by
    rw [Residual.edges_subHost_eq (Finset.union_subset hEedges hYpull)]
    change (E₀ ∪ SampledResource.pull W Ytot).image (SampledResource.edgeLift W) = _
    rw [Finset.image_union]
    change SampledResource.lift W E₀ ∪
      SampledResource.lift W (SampledResource.pull W Ytot) = _
    rw [hLiftPull]
  refine ⟨E₀,D₀,Ytot,hEDec,hFuture,ψ,?_,hClose,?_,?_,?_,?_,?_,hFutureGraph,hChildAmbient,?_,?_⟩
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hψ
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hPhysical
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using h3Child
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hCleanChild
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hEkeep
  · intro v
    have hsub : edges JW \ edges Jchild ⊆ edges JW \ E₀ := by
      intro e he
      refine mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,?_⟩
      intro heE
      apply (mem_sdiff.mp he).2
      simpa only [Jchild,JW,subHost,Finset.coe_union] using hEkeep heE
    have hdeg : SparseEdge.degIn (edges JW \ edges Jchild) v ≤
        SparseEdge.degIn (edges JW \ E₀) v :=
      Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    have hraw : (SparseEdge.degIn (edges JW \ E₀) v : ℝ) ≤ ζ*W.card := by
      exact degree_sdiff_le_change_decEq (edges JW) E₀ v (ζ*W.card)
        (@Sym2.instDecidableEq _ (Classical.decEq _))
        (fun a b => a.instDecidableEq b) (hHole v)
    exact (Nat.cast_le.mpr hdeg).trans hraw
  · rw [hChildAmbient]
    exact hOuter
  · rw [hChildAmbient]
    exact hTerminal
#print axioms structured_clean_paid_layer_state_explicit
end TypedTriangle.Vortex.Explicit
