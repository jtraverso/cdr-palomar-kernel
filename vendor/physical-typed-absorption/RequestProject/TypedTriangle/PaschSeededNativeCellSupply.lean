module
public import RequestProject.TypedTriangle.PaschSeededBankRound
public import RequestProject.TypedTriangle.PaschSeededNativeCatalogCell
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.RichBank.Seeded
open S07V40 S07V42 S07V42.Explicit S07V43 CatalogNative.Explicit ProtectedBank

/-- Native H3/H4 discharge of the rich supply interface. The cell and all its
chosen mode/support data are kept in the same existential witness. -/
theorem native_seeded_cell_supply (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (d c E d' c' E' : ℕ) {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hc3 : SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β)
    (hc4 : SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β h)
    (hnC : coreN0 β h ≤ W.card) (hn : catalogCellOrder α β h d c E d' c' E' ≤ W.card)
    (C0 : CoreCompression H.G H.lab F W d c E) (P q zmax b0 : ℕ)
    (hz : (zmax:ℝ) ≤ catalogCellDeletionBudget α β h*W.card)
    (hbud : ((b0+q+(childSetting C0 (catRadius β d c E d' c' E') P q
      (catalogCellSize α β h d c E d' c' E') zmax).Bstar*
      (catalogCellSize α β h d c E d' c' E'):ℕ):ℝ) ≤ catalogCellDegreeBudget α β h*W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H.G H.lab F Z d' c' E')
    (F0 : Finset (Sym2 V)) (hF0 : ∀ v, degIn F0 v ≤ b0)
    (R0 : Finset (Finset V)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0) :
    CellSupply H F (protect (childSetting C0 (catRadius β d c E d' c' E') P q
      (catalogCellSize α β h d c E d' c' E') zmax) F0)
      (weightedCatalogSupport α β h d c E d' c' E')
      (catalogCellPotentialCost α β h d c E d' c' E' (L0+2)) R0 := by
  let Ecell := catalogCellSize α β h d c E d' c' E'
  let S := childSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax
  intro B Z hB hZ R hL hRB l hl r
  have hl' : S.g l.2.1 ∈ S.K Z := hl
  have hlRaw := (childSetting_g_mem_K_iff C0 (catRadius β d c E d' c' E')
    P q Ecell zmax l.2.1 Z).mp hl'
  have hbU : ∀ v, degIn (B∪F0) v ≤ b0+q+S.Bstar*Ecell := by
    intro v
    have hh : degIn (B∪F0) v ≤ degIn B v+degIn F0 v := by
      unfold degIn
      rw [filter_union]
      exact card_union_le _ _
    have hb := hB v
    have hf := hF0 v
    change degIn B v ≤ q+S.Bstar*Ecell at hb
    omega
  obtain ⟨A,Y,hA,hDis,hAv,hYE,hcard,hcharge,U0,Doff,Don,hFresh,hInside,hU0Z,hSupport,
      hOff,hOn,hModesL,hModesR,hModesCard,hPhi,hCount,hExternalPhi,hExternalCount⟩ :=
    native_catalog_cell_with_seeded_potential α β h hα hβ d c E d' c' E' H F W h3 h4 hc3 hc4 hnC hn C0 Z
      ((Nat.cast_le.mpr hZ).trans hz) (CZ Z hZ) (B∪F0) (b0+q+S.Bstar*Ecell) hbU hbud
      R0 R L0 hR0 hL (fun T hT => (hRB T hT).trans subset_union_left) l.2.1 hlRaw l.1
  have hGood : GoodCell S (B∪F0) Z l ⟨A,Y⟩ := by
    refine ⟨hA.1,hA.2.1,hA.2.2,hDis,hAv,hcard,?_⟩
    show charge (tagW H.G H.lab F W) Y =
      sgnQ l.1 ((gCat C0 (catRadius β d c E d' c' E') l.2.1,0) : ClassQ H.G H.lab F W × ℤ)
    rw [charge_tagW_eq_sgnQ_iff]
    refine ⟨?_,fun e he => edge_child_of_deleted (hYE e he)⟩
    rw [hcharge]
    rfl
  let e : Entry V (Cat d (catRadius β d c E d' c' E')) P :=
    ⟨r,l,⟨A,Y⟩,U0,Doff,Don,R,B,Z⟩
  refine ⟨e, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨⟨goodCell_protect (S:=S) F0 B Z l _ hGood,
    hOff,hOn,hFresh,hInside,hU0Z,hSupport,hPhi,hCount⟩,hExternalPhi,hExternalCount⟩

end TypedTriangle.Pasch.RichBank.Seeded
#print axioms TypedTriangle.Pasch.RichBank.Seeded.native_seeded_cell_supply
