module
public import RequestProject.TypedTriangle.PaschAmbientNativeCatalogCell
public import RequestProject.TypedTriangle.PaschAmbientCellModes
public import RequestProject.TypedTriangle.PaschSeededNativeBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.AmbientBank
open S07V40 S07V42 S07V42.Explicit S07V43 CatalogNative.Explicit ProtectedBank

/-- Geometry, compression and numeric caps belong to the local host X. All
previous modes and all Pasch certificates remain on V. Only forbidden edges
and saturated vertices are pulled back, never the previous mode universe. -/
theorem native_ambient_cell_supply (α β : ℝ) (h : ℕ) (hα : 0<α) (hβ : 0<β)
    (d c E d' c' E' : ℕ) {X V I : Type} [Fintype X] [Fintype V]
    (ι : X ↪ V) (J : Host X I) (H : Host V I) (F : Set (Multiset I))
    (hAdj : ∀ x y, J.G.Adj x y → H.G.Adj (ι x) (ι y)) (hLab : ∀ x, J.lab x=H.lab (ι x))
    (W : Finset X) (h3 : CommonNbrCond J F α) (h4 : HingeCond J F α h)
    (hc3 : SparseEdge.CommonNbrCond (J.G.comap (Subtype.val : {x // x∈W} → X))
      (J.lab ∘ Subtype.val) F β)
    (hc4 : SparseEdge.HingeCond (J.G.comap (Subtype.val : {x // x∈W} → X))
      (J.lab ∘ Subtype.val) F β h)
    (hnC : coreN0 β h ≤ W.card) (hn : catalogCellOrder α β h d c E d' c' E' ≤ W.card)
    (C0 : CoreCompression J.G J.lab F W d c E) (P q zmax b0 : ℕ)
    (hz : (zmax:ℝ) ≤ catalogCellDeletionBudget α β h*W.card)
    (hbud : ((b0+q+(childSetting C0 (catRadius β d c E d' c' E') P q
      (catalogCellSize α β h d c E d' c' E') zmax).Bstar*
      (catalogCellSize α β h d c E d' c' E'):ℕ):ℝ) ≤ catalogCellDegreeBudget α β h*W.card)
    (CZ : ∀ Z : Finset X, Z.card≤zmax → DelCompression J.G J.lab F Z d' c' E')
    (F0 : Finset (Sym2 V)) (hF0 : ∀ x, degIn (pullEdges ι F0) x≤b0)
    (R0 : Finset (Finset V)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0) :
    RichBank.Seeded.CellSupply H F
      (liftSetting ι (protect (childSetting C0 (catRadius β d c E d' c' E') P q
        (catalogCellSize α β h d c E d' c' E') zmax) (pullEdges ι F0)))
      (weightedCatalogSupport α β h d c E d' c' E')
      (Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' (L0+2)) R0 := by
  let Ecell := catalogCellSize α β h d c E d' c' E'
  let S0 := childSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax
  let Sloc := protect S0 (pullEdges ι F0)
  let Samb := liftSetting ι Sloc
  let Ub := weightedCatalogSupport α β h d c E d' c' E'
  let ratio := Ambient.orderRatio ι
  let baseCost : ℝ := ((ExplicitCertificate.uniformCertCost (α/2) h*
    (4*rerouteSize β d c E d' c' E'):ℕ):ℝ)*Pasch.absorptionPotentialCost α h Ub (L0+2)
  have hnPosNat : 0<Fintype.card X := by
    have hh : 0<catalogCellOrder α β h d c E d' c' E' := by
      change 0<2*boundedPieceOrder (α/2) h (4*rerouteSize β d c E d' c' E')+
        ⌈40*(rerouteSize β d c E d' c' E':ℝ)/β⌉₊+1
      omega
    exact lt_of_lt_of_le hh (hn.trans (card_le_univ W))
  have hRatio : 1≤ratio := Ambient.orderRatio_one_le ι (by exact_mod_cast hnPosNat)
  have hRatio0 : 0≤ratio := Ambient.orderRatio_nonneg ι
  intro B Z hB hZ R hR hRB l hl r
  let Zloc := pullVertices ι Z
  have hZloc : Zloc.card≤zmax := (pull_vertices_card_le ι Z).trans hZ
  have hl' : S0.g l.2.1∈S0.K Zloc := hl
  have hlRaw := (childSetting_g_mem_K_iff C0 (catRadius β d c E d' c' E')
    P q Ecell zmax l.2.1 Zloc).mp hl'
  have hbLocal (x : X) : degIn (pullEdges ι B) x≤q+S0.Bstar*Ecell := by
    have hh := (pull_degree_le ι B x).trans (hB (ι x))
    exact hh
  have hbUnion : ∀ x, degIn (pullEdges ι B∪pullEdges ι F0) x≤b0+q+S0.Bstar*Ecell := by
    intro x
    have hh : degIn (pullEdges ι B∪pullEdges ι F0) x ≤ degIn (pullEdges ι B) x+degIn (pullEdges ι F0) x := by
      unfold degIn
      rw [filter_union]
      exact card_union_le _ _
    have hhB := hbLocal x
    have hhF := hF0 x
    omega
  obtain ⟨A,Y,hA,hDis,hAv,hYE,hCard,hCharge,U0,hFresh,hInside,hU0Z,hSupport,hFree,hPhi⟩ :=
    Ambient.native_catalog_cell_low_ambient_potential α β h hα hβ d c E d' c' E'
      ι J F W h3 h4 hc3 hc4 hnC hn C0 Zloc
      ((Nat.cast_le.mpr hZloc).trans hz) (CZ Zloc hZloc)
      (pullEdges ι B∪pullEdges ι F0) (b0+q+S0.Bstar*Ecell) hbUnion hbud
      (R0∪R) (L0+2) (hR0.union hR) l.2.1 hlRaw l.1
  have hGood0 : GoodCell S0 (pullEdges ι B∪pullEdges ι F0) Zloc l ⟨A,Y⟩ := by
    refine ⟨hA.1,hA.2.1,hA.2.2,hDis,hAv,hCard,?_⟩
    show charge (tagW J.G J.lab F W) Y=
      sgnQ l.1 ((gCat C0 (catRadius β d c E d' c' E') l.2.1,0):ClassQ J.G J.lab F W×ℤ)
    rw [charge_tagW_eq_sgnQ_iff]
    refine ⟨?_,fun f hf => edge_child_of_deleted (hYE f hf)⟩
    rw [hCharge]
    rfl
  have hGoodLoc := goodCell_protect (S:=S0) (pullEdges ι F0) (pullEdges ι B) Zloc l _ hGood0
  have hGoodAmb := goodCell_lift ι Sloc B Z l ⟨A,Y⟩ hGoodLoc
  have hInsideTotal : Inside (U0∪support A) (A∪Y) := by
    intro f hf x hx
    rcases mem_union.mp hf with hf | hf
    · exact mem_union_right _ (inside_support A f hf x hx)
    · exact mem_union_left _ (hInside f hf x hx)
  have hPhiTight : (Pasch.supportIncrementCost (R0∪R) (U0.map ι) ((support A).map ι):ℝ) ≤ ratio*baseCost := by
    dsimp only [Ambient.supportIncrementCost] at hPhi
    dsimp only [ratio,baseCost]
    simpa only [mul_assoc] using hPhi
  have hPhiFull : (Pasch.supportIncrementCost (R0∪R) (U0.map ι) ((U0∪support A).map ι):ℝ) ≤ ratio*baseCost := by
    simpa only [Pasch.supportIncrementCost,map_union,←union_assoc,union_self] using hPhiTight
  obtain ⟨Doff,hOff⟩ := hA.2.1
  obtain ⟨Don,hOn⟩ := hA.2.2
  obtain ⟨hOffLift,hOnLift,hModesL,hModesCard,hCountLocal,hCountExternal⟩ :=
    lifted_modes_two_budgets J H F ι hAdj hLab Ub hSupport hOff hOn hFresh hFree hInsideTotal
      R0 R L0 hR0 hR ratio baseCost hRatio hPhiFull
  have hPhiPay : (Pasch.supportIncrementCost (R0∪R) (U0.map ι) ((support A).map ι):ℝ) ≤
      ratio*catalogCellPotentialCost α β h d c E d' c' E' (L0+2) := by
    have hp : 0≤ratio*(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ) := by positivity
    change _ ≤ ratio*(baseCost+(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ))
    nlinarith only [hPhiTight,hp]
  have hPhiLocalPay : (Pasch.supportIncrementCost R (U0.map ι) ((support A).map ι):ℝ) ≤
      ratio*catalogCellPotentialCost α β h d c E d' c' E' (L0+2) :=
    (show (Pasch.supportIncrementCost R (U0.map ι) ((support A).map ι):ℝ) ≤
      Pasch.supportIncrementCost (R0∪R) (U0.map ι) ((support A).map ι) by
      exact_mod_cast supportIncrementCost_mono_previous (subset_union_right : R⊆R0∪R) _ _).trans hPhiPay
  have hAnchorAvoid : Disjoint (U0.map ι) Z := by
    rw [disjoint_left]
    intro v hv hvZ
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    exact disjoint_left.mp hU0Z hx (mem_preimage.mpr hvZ)
  have hSupportLift : ((U0.map ι)∪support (liftEdges ι A)).card≤Ub := by
    rw [support_lift,←map_union,card_map]
    exact hSupport
  let entry : RichBank.Entry V (Cat d (catRadius β d c E d' c' E')) P :=
    ⟨r,l,liftCell ι ⟨A,Y⟩,U0.map ι,mapConfiguration ι Doff,mapConfiguration ι Don,R,B,Z⟩
  refine ⟨entry, ?_, rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨⟨hGoodAmb,hOffLift,?_,fresh_lift ι hFresh,inside_lift ι hInside,
    hAnchorAvoid,hSupportLift,?_,?_⟩,?_,?_⟩
  · change IsDecomposition H F (liftCell ι ⟨A,Y⟩).tot (mapConfiguration ι Don)
    rw [liftCell_total]
    exact hOnLift
  · change (Pasch.supportIncrementCost R (U0.map ι) (support (liftEdges ι A)):ℝ) ≤
      ratio*catalogCellPotentialCost α β h d c E d' c' E' (L0+2)
    rw [support_lift]
    exact hPhiLocalPay
  · change _ ≤ (count R:ℝ)+ratio*(baseCost+(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ))
    exact hCountLocal
  · change (Pasch.supportIncrementCost (R0∪R) (U0.map ι) (support (liftEdges ι A)):ℝ) ≤
      ratio*catalogCellPotentialCost α β h d c E d' c' E' (L0+2)
    rw [support_lift]
    exact hPhiPay
  · change _ ≤ (count (R0∪R):ℝ)+ratio*(baseCost+(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ))
    exact hCountExternal

end TypedTriangle.Pasch.AmbientBank
#print axioms TypedTriangle.Pasch.AmbientBank.native_ambient_cell_supply
