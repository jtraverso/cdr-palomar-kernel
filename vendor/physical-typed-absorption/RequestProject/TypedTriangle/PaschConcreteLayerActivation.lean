module
public import RequestProject.TypedTriangle.PaschConcreteLayerCore
public import RequestProject.TypedTriangle.PaschSamePackingStockTransition
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.ConcreteLayer
open S07V40 S07V42 S07V43 S07V44 S07V46 ProtectedBank AmbientBank
open RichBank.Actual CatalogNative LocalizedCover BasalIncidence

/-- Consume the actual P0/Ccover/withdrawal witnesses. The allocated bank mode
and the final paid decomposition are literal; no packing constructor occurs. -/
theorem activate_same_packing_paid_partition
    {X V I : Type} [Fintype X] [Fintype V]
    (H : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    {d c E Rc P q Ecell z N Ub A M K L t : ℕ} {pay : ℝ}
    (C0 : CoreCompression H.G H.lab F W d c E) (ι : X ↪ V)
    (hLab : ∀x,H.lab x=Hambient.lab (ι x))
    (F0 : Finset (Sym2 V)) (R0 : Finset (Finset V))
    (es : List (RichBank.Entry V (Cat d Rc) P))
    (hInv : RichBank.Seeded.RunInv Hambient F
      (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) Ub pay R0 N es)
    (D P0 Ccover Dps : Finset (Finset X)) (R T Eref J0 Ps Y : Finset (Sym2 X))
    (hD : IsDecomposition H F (cover D) D) (hR : Basal H F R)
    (hRStock : Disjoint R (cover D))
    (hRtail : Disjoint R T)
    (hRB : Disjoint R (pullEdges ι (RichBank.usedEdges es)))
    (hTB : Disjoint T (pullEdges ι (RichBank.usedEdges es)))
    (hProtected : liftEdges ι (cover D∪R) ⊆ F0)
    (hAvoid : Disjoint Eref (((cover D∪R)∪T)∪pullEdges ι (RichBank.usedEdges es)))
    (hJ0 : J0=edges H\((((R∪T)∪pullEdges ι (RichBank.usedEdges es))∪Eref)∪P0.biUnion triEdges))
    (hC : IsPacking H F Ccover) (hQ : IsPacking H F (P0∪Ccover))
    (hQR : Disjoint ((P0∪Ccover).biUnion triEdges)
      (((R∪T)∪pullEdges ι (RichBank.usedEdges es))∪Eref))
    (hStockJ : cover D ⊆ J0) (hCJ : Ccover.biUnion triEdges ⊆ J0)
    (hRes : edges H\(((((R∪T)∪pullEdges ι (RichBank.usedEdges es))∪Eref)∪
      (P0∪Ccover).biUnion triEdges)) ⊆ cover D)
    (hMove : R∪(edges H\(((((R∪T)∪pullEdges ι (RichBank.usedEdges es))∪Eref)∪
      (P0∪Ccover).biUnion triEdges)))=Ps∪Y)
    (hPY : Disjoint Ps Y) (hDps : IsDecomposition H F Ps Dps)
    (hYInside : ∀e∈Y,∀x∈e,x∈W) (hYPhys : IsPhysical H F Y)
    (hPath : S07V45.CorePathContract H.G H.lab F W t) (ht : Odd t) (ht3 : 3 ≤ t)
    (hq : 0 < q)
    (hChain : ChainBound (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) L)
    (hRunCap : 2*Ecell*(childSetting C0 Rc P q Ecell z).Bstar*N ≤ q*z)
    (hGen : ∀Z : Finset X,Z.card ≤ z → CatalogGen C0 Rc Z)
    (Mon : ∀Z : Finset X,CatalogGen C0 Rc Z → PhysicalMonitors C0 Rc Z A M K)
    (Fm : FullMonitor C0 Rc A M K)
    (loc : ℕ → Fin K → Sym2 X → ℝ) (full : Fin K → Sym2 X → ℝ)
    (hLocRep : ∀ℓ j (x : MCore H.G H.lab F W)
      (hg : CatalogGen C0 Rc (pullVertices ι (RichBank.Actual.Zstrat
        (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) es N (ℓ+1)))),
      ∑e,loc ℓ j e*((x.1 e:ℤ):ℝ)=physMonReal C0 (Dset C0 Rc
        (pullVertices ι (RichBank.Actual.Zstrat
          (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) es N (ℓ+1))))
        (Mon _ hg).psi j x)
    (hFullRep : ∀j (x : MCore H.G H.lab F W),∑e,full j e*((x.1 e:ℤ):ℝ)=physMonReal C0 ∅ Fm.psi j x)
    (Λ ηCover τMom ρ τSel γ η : ℝ) (hΛ : 0 ≤ Λ) (hγ : 0 < γ) (hη : 0 ≤ η)
    (hLocTri : ∀ℓ j T,IsAllowed H F T → |triSum (loc ℓ j) T| ≤
      3*Λ*(T∩pullVertices ι (RichBank.Actual.Zstrat
        (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) es N (ℓ+1))).card)
    (hFullTri : ∀j T,IsAllowed H F T → |triSum (full j) T| ≤ 3*Λ*T.card)
    (hLocMom : ∀ℓ ≤ L,∀j,|edgeSum (loc ℓ j) (J0\cover D)| ≤
      τMom*Fintype.card X*(pullVertices ι (RichBank.Actual.Zstrat
        (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) es N (ℓ+1))).card)
    (hFullMom : ∀j,|edgeSum (full j) (J0\cover D)| ≤ τMom*(Fintype.card X:ℝ)^2)
    (hStockDeg : ∀x,((cover D).filter (fun e => x∈e)).card ≤ ρ*Fintype.card X)
    (hRDeg : ∀x,((R.filter (fun e => x∈e)).card:ℝ) ≤ τSel*Fintype.card X)
    (hCdeg : ∀x,(((Ccover.biUnion triEdges).filter (fun e => x∈e)).card:ℝ) ≤ ηCover*Fintype.card X)
    (hQn : γ*Fintype.card X ≤ q)
    (hCapacity : η*((2*Ecell*(childSetting C0 Rc P q Ecell z).Bstar:ℕ):ℝ)/γ ≤ 1)
    (hP : 2*gammaL A M L ≤ P)
    (hKB : (K:ℝ)*(τMom+(3*Λ/2)*(ηCover+2*ρ+2*τSel)) ≤ η)
    (hN : (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))).K
      (saturatedPrefix (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) es N) ≠ ⊥ →
      1+η*(Fintype.card X:ℝ)^2 ≤ 2*N)
    (Rfixed : Finset (Finset V)) (payCover : ℝ)
    (hFixedBank : RichBank.modes es ⊆ Rfixed)
    (hQCost : (count (Rfixed∪mapConfiguration ι ((P0∪Ccover)∪Dps)):ℝ) ≤ count Rfixed+payCover) :
    ∃ (Ytot Yb : Finset (Sym2 X)) (Dclocal : Finset (Finset X)),
      Ytot=Y∪Yb ∧ Ytot ⊆ edges H ∧ Ytot ⊆ childEdges H.G W ∧
      SparseEdge.ind Ytot ∈ LamCore H.G H.lab F W ∧ Disjoint Eref Ytot ∧
      Disjoint T (Eref∪Ytot) ∧
      IsDecomposition H F (edges H\(T∪(Eref∪Ytot))) (((P0∪Ccover)∪Dps)∪Dclocal) ∧
      P0 ⊆ (((P0∪Ccover)∪Dps)∪Dclocal) ∧
      mapConfiguration ι Dclocal ⊆ RichBank.modes es ∧
      (count (Rfixed∪mapConfiguration ι (((P0∪Ccover)∪Dps)∪Dclocal)):ℝ) ≤ count Rfixed+payCover := by
  let Sloc := protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0)
  let S := liftSetting ι Sloc
  let Bank := pullEdges ι (RichBank.usedEdges es)
  let Rtail := ((R∪T)∪Bank)∪Eref
  let Q := P0∪Ccover
  have hFinal : edges H\(Rtail∪Q.biUnion triEdges)=J0\Ccover.biUnion triEdges := by
    rw [hJ0]
    dsimp only [Rtail,Q,Bank]
    rw [union_biUnion]
    ext e
    simp only [mem_sdiff,mem_union]
    tauto
  have hLeft : J0\Ccover.biUnion triEdges ⊆ cover D := by rw [←hFinal]; exact hRes
  have hMoveC : R∪(J0\Ccover.biUnion triEdges)=Ps∪Y := by rw [←hFinal]; exact hMove
  have hYDR : Y ⊆ cover D∪R := by
    intro e he
    have hh : e∈R∪(J0\Ccover.biUnion triEdges) := by rw [hMoveC]; exact mem_union_right _ he
    rcases mem_union.mp hh with hr | hl
    · exact mem_union_right _ hr
    · exact mem_union_left _ (hLeft hl)
  have hYE : Y ⊆ edges H := hYDR.trans (union_subset (CorePaid.basal_subset_edges ⟨D,hD⟩) (CorePaid.basal_subset_edges hR))
  have hYF : liftEdges ι Y ⊆ F0 := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
    exact hProtected (mem_map.mpr ⟨g,hYDR hg,rfl⟩)
  have hYCore := StockEntry.g4_positive_payload_in_child H W Y hYE hYInside
  obtain ⟨x,hx,hx0⟩ := actual_physical_residue_charge H F hPath ht ht3 Y hYPhys hYCore
  have hgen := actual_strata_catalog_generates ι H Hambient F W C0 S R0 es hInv hq hRunCap hGen
  let B := τMom+(3*Λ/2)*(ηCover+2*ρ+2*τSel)
  have hLocY : ∀ℓ ≤ L,∀j,|edgeSum (loc ℓ j) Y| ≤
      B*Fintype.card X*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card := by
    intro ℓ hℓ j
    exact same_cover_positive_moment H F D hD J0 R Ps Y Ccover hC hStockJ hCJ hLeft hRStock hPY hMoveC Dps hR hDps
      (Fintype.card X) ρ τSel ηCover τMom Λ hΛ hStockDeg hRDeg hCdeg _ (loc ℓ j) (hLocTri ℓ j) (hLocMom ℓ hℓ j)
  have hFullY : ∀j,|edgeSum (full j) Y| ≤ B*(Fintype.card X:ℝ)^2 := by
    intro j
    have hTri : ∀A,IsAllowed H F A → |triSum (full j) A| ≤ 3*Λ*(A∩(univ:Finset X)).card := by simpa using hFullTri j
    have hMom : |edgeSum (full j) (J0\cover D)| ≤ τMom*Fintype.card X*(univ:Finset X).card := by
      simpa only [card_univ,pow_two,mul_assoc] using hFullMom j
    have hh := same_cover_positive_moment H F D hD J0 R Ps Y Ccover hC hStockJ hCJ hLeft hRStock hPY hMoveC Dps hR hDps
      (Fintype.card X) ρ τSel ηCover τMom Λ hΛ hStockDeg hRDeg hCdeg univ (full j) hTri hMom
    simpa only [card_univ,pow_two,mul_assoc,B] using hh
  obtain ⟨J,hJL,word,hAct,hWordBound,hCancel,_⟩ :=
    ActualAllocation.activate_actual_bank_of_physical_moments H Hambient F W C0 ι S R0 es hInv hq hChain hRunCap
      (fun a Z => native_lifted_g_mem_K H F W C0 ι Rc P q Ecell z F0 a Z)
      (fun Z => native_lifted_K_bot_iff H F W C0 ι Rc P q Ecell z F0 Z)
      Mon Fm hgen (Fintype.card X) hγ hη hQn hCapacity hP Y x hx hx0 loc full
      (fun ℓ j => hLocRep ℓ j x (hgen (ℓ+1))) (fun j => hFullRep j x) B hKB hLocY hFullY hN
  let Actual := ((cover D∪R)∪T)∪Bank
  have hYU : Y ⊆ Actual := hYDR.trans (subset_union_left.trans subset_union_left)
  obtain ⟨Ytot,Yb,Bc,Dc,Dclocal,hYtot,hYtotE,hYtotU,hEY,hPartition,hDc,hDclocal,hDcMap,hDcCount,hDcSub,
    hLocalBudget,hExternalBudget,hBcF0,hBcYb,hYYb,hLam,hYbCore⟩ :=
    ActualAllocation.actual_activated_mode_avoiding_reference H Hambient F W C0 ι hLab F0 R0 es hInv
      Y Actual Eref x hYF hYE hx word (fun i p a ha => (hAct i p a ha).2) hWordBound hCancel hYU
      subset_union_right hAvoid
  have hBankEq : Bank=pullEdges ι Bc∪Yb := by
    ext e
    simp only [Bank,pullEdges,mem_preimage,mem_union]
    rw [hPartition,mem_union]
    constructor
    · rintro (he|he)
      · exact Or.inl he
      · obtain ⟨f,hf,hfe⟩ := mem_map.mp he
        exact Or.inr ((edgeEmbedding ι).injective hfe ▸ hf)
    · rintro (he|he)
      · exact Or.inl he
      · exact Or.inr (mem_map.mpr ⟨e,he,rfl⟩)
  have hBcYbLocal : Disjoint (pullEdges ι Bc) Yb := by
    rw [disjoint_left]
    intro e he hy
    exact disjoint_left.mp hBcYb (mem_preimage.mp he) (mem_map.mpr ⟨e,hy,rfl⟩)
  have hRE : Disjoint R Eref := (hAvoid.mono_right ((subset_union_right.trans subset_union_left).trans subset_union_left)).symm
  have hTE : Disjoint T Eref := (hAvoid.mono_right (subset_union_right.trans subset_union_left)).symm
  have hBE : Disjoint Bank Eref := (hAvoid.mono_right subset_union_right).symm
  let Dpaid := (Q∪Dps)∪Dclocal
  obtain ⟨_,hTerminal,_,hPaid,hP0paid,_⟩ := Vortex.paid_outer_partition_retaining_decompositions H F Q P0 Dps Dclocal Dpaid
    R T Bank Eref Rtail Ps Y Yb (pullEdges ι Bc) hQ subset_union_left
    (subset_union_left.trans subset_union_left) (subset_union_right.trans subset_union_left) subset_union_right
    hQR rfl hRtail hRB hRE hTB hTE hBE hMove hPY hDps hBankEq hDclocal hBcYbLocal hYYb
  have hYtotCore : Ytot ⊆ childEdges H.G W := by rw [hYtot]; exact union_subset hYCore hYbCore
  have hLocalModeSub : mapConfiguration ι Dclocal ⊆ RichBank.modes es := by rw [hDcMap]; exact hDcSub
  have hFixedDc : mapConfiguration ι Dclocal ⊆ Rfixed := hLocalModeSub.trans hFixedBank
  have hUniverse : Rfixed∪mapConfiguration ι Dpaid=Rfixed∪mapConfiguration ι (Q∪Dps) := by
    dsimp only [Dpaid]
    unfold mapConfiguration
    rw [map_union]
    ext A
    simp only [mem_union]
    have hh : A∈Dclocal.map (Finset.mapEmbedding ι).toEmbedding → A∈Rfixed := fun ha => hFixedDc ha
    tauto
  refine ⟨Ytot,Yb,Dclocal,hYtot,hYtotE,hYtotCore,hLam,hEY,?_,?_,hP0paid,hLocalModeSub,?_⟩
  · rwa [←hYtot] at hTerminal
  · rwa [←hYtot] at hPaid
  · rw [hUniverse]
    exact hQCost

end TypedTriangle.Pasch.ConcreteLayer
#print axioms TypedTriangle.Pasch.ConcreteLayer.activate_same_packing_paid_partition
