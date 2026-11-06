module
public import RequestProject.TypedTriangle.PaschConcreteStructuredLayer
public import RequestProject.TypedTriangle.PaschRawStockWithdrawalUniformRich
public import RequestProject.TypedTriangle.PaschStructuredActualChild
public import RequestProject.TypedTriangle.PaschResidualWindowPathCount
public import RequestProject.TypedTriangle.PaschRawStockProfile
public import RequestProject.TypedTriangle.PaschAdaptiveInsertionBudget
public import RequestProject.TypedTriangle.PaschWeightedWithdrawalPayment
public import RequestProject.TypedTriangle.PaschBankTotalPayment
public import RequestProject.TypedTriangle.ExplicitConcreteInnerLayers
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open Vortex Vortex.Explicit Vortex.IntrinsicRawPathsPreparedVortex
open CatalogNative CatalogNative.Explicit CorePaid BasalIncidence S07V26 S07V27

private theorem window_change_fintype {X Y : Type}
    (ι : X ↪ Y) (f₁ f₂ : Fintype X) :
    @embeddingWindow X Y f₁ ι = @embeddingWindow X Y f₂ ι := by
  cases Subsingleton.elim f₁ f₂
  rfl

private theorem card_bound_change_fintype {X : Type}
    (n : ℕ) (k : ℝ) (f₁ f₂ : Fintype X)
    (hBound : (n:ℝ) ≤ k*@Fintype.card X f₁) :
    (n:ℝ) ≤ k*@Fintype.card X f₂ := by
  cases Subsingleton.elim f₁ f₂
  exact hBound

private theorem degree_sdiff_change_decEq {X : Type}
    (R E : Finset (Sym2 X)) (v : X) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 X))
    (hBound : (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) R E) v : ℝ) ≤ b) :
    (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) R E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hBound

private theorem embedded_edges_change_fintype {X Y I : Type}
    (ι : X ↪ Y) (J : Host X I) (f₁ f₂ : Fintype X) :
    embeddedEdges ι (@edges X I f₁ J) = embeddedEdges ι (@edges X I f₂ J) := by
  cases Subsingleton.elim f₁ f₂
  rfl

private theorem diffuse_change_fintype {X I : Type} (H : Host X I)
    (F : Set (Multiset I)) (C : ℝ) (μ : Finset X → ℝ) (f₁ f₂ : Fintype X)
    (hSeed : @IsDiffuseSeed X I f₁ H F C μ) : @IsDiffuseSeed X I f₂ H F C μ := by
  cases Subsingleton.elim f₁ f₂
  exact hSeed

private theorem common_change_fintype {X I : Type} (H : Host X I)
    (F : Set (Multiset I)) (α : ℝ) (f₁ f₂ : Fintype X)
    (hH3 : @CommonNbrCond X I f₁ H F α) : @CommonNbrCond X I f₂ H F α := by
  cases Subsingleton.elim f₁ f₂
  exact hH3

private theorem clean_change_fintype {X I : Type} (H : Host X I)
    (F : Set (Multiset I)) (α : ℝ) (h : ℕ) (f₁ f₂ : Fintype X)
    (hH4 : @CleanHingeCond X I f₁ H F α h) : @CleanHingeCond X I f₂ H F α h := by
  cases Subsingleton.elim f₁ f₂
  exact hH4

private theorem physical_edges_change_fintype {X I : Type} (H : Host X I)
    (F : Set (Multiset I)) (f₁ f₂ : Fintype X)
    (hH2 : IsPhysical H F (@edges X I f₁ H)) : IsPhysical H F (@edges X I f₂ H) := by
  cases Subsingleton.elim f₁ f₂
  exact hH2

private theorem sparse_degree_union_le {X : Type}
    (E G : Finset (Sym2 X)) (v : X) :
    SparseEdge.degIn (E∪G) v ≤ SparseEdge.degIn E v+SparseEdge.degIn G v := by
  simpa only [SelSimul.edeg,SparseEdge.degIn] using SelSimul.edeg_union_le E G v

private theorem inter_change_decEq {X : Type}
    (S E : Finset X) (P : Finset X → Prop) (d₁ d₂ : DecidableEq X)
    (hh : P (@Inter.inter _ (@Finset.instInter _ d₁) S E)) :
    P (@Inter.inter _ (@Finset.instInter _ d₂) S E) := by
  cases Subsingleton.elim d₁ d₂
  exact hh

/-- Geometry-only cost, fixed after qInner and before the reference agenda,
outer rate, terminal order or either stock density. -/
def innerAdaptiveGeometryCoefficient (α C q a : ℝ) (h m : ℕ) : ℝ :=
  let αp := α/16
  let βb := α/32
  let d := catalogDimension βb h
  let c := catalogCoefficient βb h
  let E := catalogColumn βb h
  let Rc := bankCatalogRadius αp βb h
  let Lbank := bankCatalogSize αp βb h
  let AM := S07V34.Explicit.paymentCost d (S07V44.monR Rc E)
  let MM := S07V34.Explicit.monitorMagnitude d (S07V44.monR Rc E)
  let P := 2*S07V46.gammaL AM MM Lbank
  let Bstar := 2*Lbank*P
  let Bank := bankCubicPaymentCoefficient αp βb h d c E
    (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h) Bstar *
      geometricBankRoundRate αp βb h P
  let Stock := 1+8*C+12*(4*C)^2+7*(4*C)^3
  let Partial := (2*C^3+1)+16*C+12*(4*C)^2+7*(4*C)^3
  1+Stock+3*withdrawalGeometryCost (α*q/16) q (a/2) m+Bank+Partial+1

/-- The stage offset is constant: raw stock uses L, withdrawal L+1+182,
main packing L+66, and its cover L+68. -/
def innerAdaptiveDinner (α C q a : ℝ) (h m : ℕ) : ℝ :=
  (|innerAdaptiveGeometryCoefficient α C q a h m|+1)*(318 : ℝ)^3

/-- Concrete adaptive layers on the original raw vortex. The reference
profile remains the naked raw profile; resource stock uses the actual
parent's existing exact 2C seed. This is a candidate until its body compiles. -/
theorem concrete_inner_adaptive_paid_layers {I : Type} (F : Set (Multiset I))
    (α₀ C : ℝ) (h d T m : ℕ) (a : ℝ)
    (hα : 0 < α₀) (hC : 1 ≤ C) (hh : 6 ≤ h)
    (hm : 0 < m) (ha : 0 < a) (hOdd : Odd (m+1)) (hLen : 3 ≤ m+1) :
    ∃ εInner γInner ηInner : ℝ, 0 < εInner ∧ 0 < γInner ∧ 0 < ηInner ∧
      ∀ ρFuture q ζState Btotal : ℝ,
        0 < ρFuture → 0 < q → q ≤ 1/32 → 4*q ≤ εInner →
        2*q ≤ ρFuture → q ≤ ηInner/16 → q ≤ γInner/8 →
        q ≤ α₀/(64*(2 : ℝ)^h.choose 2) → q*m*(2 : ℝ)^m ≤ a/64 →
        0 < ζState → ζState ≤ windowRouteRate a q m/4 → ζState ≤ α₀*q/128 →
        0 ≤ Btotal → Btotal ≤ 1/8 → Btotal ≤ α₀/128 →
        Btotal*m*(2 : ℝ)^m ≤ a/64 →
      ∃ Dinner : ℝ, 0 < Dinner ∧ Dinner = innerAdaptiveDinner α₀ C q a h m ∧
      ∀ (β : ℕ → ℝ) (N : ℕ), (∀ j, 0 ≤ β j) →
        (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j) ≤ Btotal →
      ∀ schedule : ConcreteInnerLayerSchedule F (α₀/8) C ρFuture ζState β h N
          (d+(d+1)*Nat.log 2 T),
      ∃ Minner : ℕ, 1 ≤ Minner ∧
      ∀ {Orig : Type} [Fintype Orig] (HOrig : Host Orig I),
        max 1 (paschDepthOrder (embeddedEligibilityDepthCoefficient (α₀/32) (4*C) 133 67)) ≤
          Fintype.card Orig →
      ∀ M : ℕ, Minner ≤ M →
      ∀ {X : Type} [Fintype X] {H : Host X I} {μ : Finset X → ℝ}
        {εRoute t : ℝ}
        (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ),
        chain.HasRelativeWindows →
        AdaptivePaidLayers chain (2*C) (α₀/16) ζState HOrig Dinner 67 67
          (Nat.sqrt (Nat.sqrt (Fintype.card Orig))) := by
  obtain ⟨εInner,hεInner,hMain⟩ := ConcreteLayer.concrete_same_bank_layer F
    (2*C) (α₀/16) 1 1 1 h (by linarith only [hC]) (by positivity)
      (by norm_num) (by norm_num) (by norm_num)
  have h2C : 1 ≤ 2*C := by linarith only [hC]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hStockWindow : 1/(2*C) ≤ 2*C :=
    ((div_le_one (by positivity : (0 : ℝ) < 2*C)).mpr h2C).trans h2C
  obtain ⟨εRaw,γInner,hεRaw,hγInner,hRawStock⟩ := raw_stock_weighted_withdrawal_uniform_rich F
    (1/(2*C)) (2*C) (α₀/16) 1 (a/2) h 1 m (by norm_num) (by positivity) hStockWindow
      (by positivity) (by positivity) hm hOdd
  let ηInner := bankProtectionBudget (α₀/16) (α₀/32) h
  have hηInner : 0 < ηInner := bankProtectionBudget_pos h (by positivity) (by positivity)
  refine ⟨εInner,γInner,ηInner,hεInner,hγInner,hηInner,?_⟩
  intro ρFuture q ζState Btotal hρ hq hq32 hqReserve hqρ hqBank hqStock hqα hqPath
    hζ hζRoute hζPool hB0 hB8 hBα hBPath
  let Dinner := innerAdaptiveDinner α₀ C q a h m
  have hDinner : 0 < Dinner := by dsimp only [Dinner,innerAdaptiveDinner]; positivity
  refine ⟨Dinner,hDinner,rfl,?_⟩
  intro β N hβ hTotal schedule
  let L := d+(d+1)*Nat.log 2 T
  let γMin := (univ : Finset (Fin (L+1))).inf' (by simp) (fun j => schedule.γRef j)
  have hγMin : 0 < γMin := by
    apply (lt_inf'_iff _).mpr
    intro j _
    exact schedule.γRef_pos j (Nat.le_of_lt_succ j.isLt)
  have hγMin_le (j : Fin (L+1)) : γMin ≤ schedule.γRef j := inf'_le _ (mem_univ j)
  let εcap := min (γMin/8) (1/8)
  have hεcap : 0 < εcap := lt_min (by positivity) (by norm_num)
  have hεcap_j (j : Fin (L+1)) : εcap ≤ min (schedule.γRef j/4) (1/4) := by
    apply le_min
    · have hγj := hγMin_le j
      have hh : εcap ≤ γMin/8 := min_le_left _ _
      linarith only [hh,hγj,hγMin]
    · exact (min_le_right _ _).trans (by norm_num)
  let αp := α₀/16
  let βb := α₀/32
  have hαp : 0 < αp := by dsimp only [αp]; positivity
  have hβb : 0 < βb := by dsimp only [βb]; positivity
  let δcap := min (ExplicitGeometry.deletionBudget βb h) (S07V37.delOf (βb/2) h)/2
  have hδcap : 0 < δcap := by
    have hDel := (ExplicitGeometry.deletionBudget_spec hβb h).1
    have hDel2 : 0 < S07V37.delOf (βb/2) h := S07V37.delOf_pos (by positivity) h
    exact div_pos (lt_min hDel hDel2) (by norm_num)
  have hδcap_le : δcap ≤ min (ExplicitGeometry.deletionBudget βb h) (S07V37.delOf (βb/2) h) := by
    have hp := hδcap
    dsimp only [δcap] at hp ⊢
    linarith only [hp]
  let db := catalogDimension βb h
  let cb := catalogCoefficient βb h
  let Eb := catalogColumn βb h
  let Rc := bankCatalogRadius αp βb h
  let Lbank := bankCatalogSize αp βb h
  let Ecell := bankCellSize αp βb h
  let AM := S07V34.Explicit.paymentCost db (S07V44.monR Rc Eb)
  let MM := S07V34.Explicit.monitorMagnitude db (S07V44.monR Rc Eb)
  let KM := S07V34.Explicit.monitorDimension db (S07V44.monR Rc Eb)
  let Pbank := 2*S07V46.gammaL AM MM Lbank
  let Bstar := 2*Lbank*Pbank
  let Λ := physicalWeightMagnitude (αp/2) (βb/2) h db cb MM
  let κBank := bankRoundRate αp βb εcap δcap h Pbank
  let εBank := bankTolerance αp βb εcap h
  let ηPay := StockEntry.Explicit.bankEta κBank (q/2) εBank (2*Ecell*Bstar)
  let δ := StockEntry.Explicit.monitorCap Λ ηPay KM
  have hΛ : 0 < Λ := physicalWeightMagnitude_pos _ _ _ _ _ _
  have hκBank : 0 < κBank := bankRoundRate_pos h Pbank hαp hβb hεcap hδcap
  have hεBank : 0 < εBank := bankTolerance_pos h hαp hβb hεcap
  obtain ⟨_,_,hδ,_,_,_,_,_⟩ := StockEntry.Explicit.native_bank_scale_cap_explicit
    κBank (q/2) εBank Λ (2*Ecell*Bstar) KM hκBank (by positivity) hεBank hΛ.le
  let τSel := min 1 (min δ (min (q/64) (min (γMin*q/64) (ηInner*q/64))))
  have hτSel : 0 < τSel := by dsimp only [τSel]; positivity
  have hτSel1 : τSel ≤ 1 := min_le_left _ _
  have hτSelδ : τSel ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hτSelq : τSel ≤ q/64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτSelγ : τSel ≤ γMin*q/64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτSelη : τSel ≤ ηInner*q/64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hτSelCap (j : Fin (L+1)) : τSel ≤ min δ (min (q/64) (schedule.γRef j*q/64)) := by
    apply le_min hτSelδ
    apply le_min hτSelq
    have hg := mul_le_mul_of_nonneg_right (hγMin_le j) hq.le
    linarith only [hτSelγ,hg]
  let κGeom := α₀*q/16
  have hκGeom : 0 < κGeom := by dsimp only [κGeom]; positivity
  obtain ⟨θStock,hθStock,hRawByPrecision⟩ := hRawStock q κGeom hq hκGeom
  obtain ⟨ρ,κStock,hρStock,hρCap,hκStock,Nstock,hStockHost⟩ :=
    hRawByPrecision τSel τSel 1 hτSel hτSel (by norm_num)
  have hρCap_j (j : Fin (L+1)) : ρ ≤ min δ (min (q/64) (schedule.γRef j*q/64)) :=
    hρCap.trans (hτSelCap j)
  have hMainAt (j : Fin (L+1)) := hMain βb (α₀/8) (3/(4*C)) (2*C) ρFuture
    (schedule.ζRef j) (schedule.εRef j) (schedule.γRef j) q εcap δcap
    (schedule.nRef j) (m+1) 1 hβb (by dsimp only [αp,βb]; linarith only [hα])
    (schedule.γRef_pos j (Nat.le_of_lt_succ j.isLt)) hq hqReserve hεcap (hεcap_j j)
    hδcap hδcap_le hOdd hLen (schedule.reference j (Nat.le_of_lt_succ j.isLt))
      ρ τSel κStock 1 hρStock hτSel hκStock (by norm_num) (hρCap_j j) (hτSelCap j)
  choose nMain hMainHost using hMainAt
  let Mgeom := innerLayerOrder α₀ C q a h m L schedule.K schedule.εRef schedule.γRef
    schedule.nRef schedule.nPaid schedule.nGeometry
  let nTests := (Lbank+2)*KM
  let Minner := Mgeom+Nstock+(univ : Finset (Fin (L+1))).sup nMain+nTests+2
  refine ⟨Minner,by dsimp only [Minner]; omega,?_⟩
  intro Orig _ HOrig hRootOrder M hM X _ H μ εRoute t chain
  have hMgeom : Mgeom ≤ M := by dsimp only [Minner] at hM; omega
  have hMstock : Nstock ≤ M := by dsimp only [Minner] at hM; omega
  have hMmain (j : Fin (L+1)) : nMain j ≤ M := by
    have hj := Finset.le_sup (f := nMain) (mem_univ j)
    dsimp only [Minner] at hM
    omega
  have hMtests : nTests+2 ≤ M := by dsimp only [Minner] at hM; omega
  let E := max 1 (2*C)
  have hEb : E ≤ 2*C := by dsimp [E]; exact max_le (by linarith only [hC]) le_rfl
  have hAgenda : ∀r ≤ L,
      schedule.K r*(2*(2*C)*(∑ j ∈ range r,β j)) ≤ 1/(16*C) ∧
      2*(2*C)*(∑ j ∈ range r,β j) ≤ schedule.εRef r/8 := by
    intro r hr
    simpa only [show 2*(2*C)=4*C by ring] using
      And.intro (schedule.prefix_inverse r hr) (schedule.prefix_reference r hr)
  let nBudget := scheduledProfileOrder C schedule.K schedule.εRef L
  have hnBudget : 1 ≤ nBudget := scheduledProfileOrder_pos C schedule.K schedule.εRef L
  have hBudget := scheduled_raw_profile_budget_explicit C E (2*C)
    β schedule.K schedule.εRef L hC (by dsimp [E]; positivity) hEb hβ
    schedule.K_pos schedule.εRef_pos hAgenda
  let nRun : Fin (L+1) → ℕ := fun j => cleanLayerThreshold (α₀/16) C (α₀/32)
    (schedule.γRef j) q (α₀/4) (windowRouteRate a q m/4) h (m+1)
    (schedule.nRef j) (schedule.nPaid j) schedule.nGeometry
  let nAll := (univ : Finset (Fin (L+1))).sup nRun
  let M₀ := max 1 (max nAll (max nBudget ⌈2/q⌉₊))
  change M₀ ≤ M at hMgeom
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hMgeom
  have hMBudget : nBudget ≤ M :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hMgeom
  have hMRun : ∀j, nRun j ≤ M := by
    intro j
    exact (Finset.le_sup (mem_univ j)).trans
      (((le_max_left _ _).trans (le_max_right _ _)).trans hMgeom)
  induction chain with
  | terminal node upper => intro _; trivial
  | descend node W lower shrink route paths intermediate next_index tail ih =>
    intro hMetadata
    letI : DecidableEq (Survivors node.trim) := Classical.decEq _
    let current := IntrinsicRawPathsPreparedVortex.descend node W lower shrink route paths
      intermediate next_index tail
    let Hraw : Host (Survivors node.trim) I := current.preparedHost
    change RawSampleMetadata Hraw F α₀ q W ∧ tail.HasRelativeWindows at hMetadata
    refine ⟨?_,ih hMetadata.2⟩
    intro state eAmbient Rpast Lpast depth hTracking hDepth hLpast
      hAmbientAdj hAmbientLab hPastCG hPastThree
    let j : Fin (L+1) := ⟨tail.head.index,by
      exact Nat.lt_succ_of_le tail.head.index_le⟩
    let Hactual : Host (Survivors node.trim) I := state.host
    have hParentLower : M ≤ Fintype.card (Survivors node.trim) := by
      have hNat : M ≤ Nat.card (Survivors node.trim) := by
        simpa only [←Nat.card_eq_fintype_card] using node.lower
      simpa only [Nat.card_eq_fintype_card] using hNat
    have hSeedActual : IsDiffuseSeed Hactual F (2*C) state.seed :=
      diffuse_change_fintype Hactual F (2*C) state.seed _ _ state.diffuse
    have hCommonActual : CommonNbrCond Hactual F (α₀/16) :=
      common_change_fintype Hactual F (α₀/16) _ _ state.common
    have hCleanActual : CleanHingeCond Hactual F (α₀/16) h :=
      clean_change_fintype Hactual F (α₀/16) h _ _ state.clean
    have hPhysicalActual : IsPhysical Hactual F (edges Hactual) :=
      physical_edges_change_fintype Hactual F _ _ state.physical
    have hGraph : Hactual.G ≤ Hraw.G := state.graph_le
    have hLabels : Hactual.lab = Hraw.lab := state.labels
    let ι : Survivors tail.head.trim ↪ Survivors node.trim :=
      nextPreparedEmbedding W tail.head.trim
    let fullCanonical := embeddingWindow ι
    let canonicalFintype : ULift.{0} (Fintype (Survivors tail.head.trim)) := ⟨inferInstance⟩
    have hProtected := state.next_edges
    rw [nextPreparedEdges.eq_2 node W lower shrink route paths intermediate next_index tail] at hProtected
    have hProtectedCanonical : embeddedEdges ι (edges tail.preparedHost) ⊆ edges Hactual := by
      convert hProtected using 1 <;> simp only [head.eq_2,ι,Hactual]
    have hAdjRaw : ∀u v, tail.preparedHost.G.Adj u v → Hactual.G.Adj (ι u) (ι v) := by
      intro u v huv
      exact SparseEdge.mem_edges.mp (hProtectedCanonical
        (mem_image.mpr ⟨s(u,v),SparseEdge.mem_edges.mpr huv,rfl⟩))
    letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
    let e := embeddingWindowEquiv ι
    let Wfull := embeddingWindow ι
    letI : DecidableEq {x // x ∈ Wfull} := Classical.decEq _
    let JW := embeddingWindowHost ι Hactual
    let cut := liftVertexSet (univ \ W) tail.head.trim
    have hFullEq : Wfull = fullCanonical := window_change_fintype ι _ canonicalFintype.down
    have hProtected' : embeddedEdges ι (edges tail.preparedHost) ⊆ edges Hactual := by
      intro f hf
      obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
      induction g using Sym2.ind with
      | _ u v =>
        exact SparseEdge.mem_edges.mpr (hAdjRaw u v (SparseEdge.mem_edges.mp hg))
    have hWindow := preserved_window_host_equiv ι tail.preparedHost Hraw Hactual
      (fun _ _ => Iff.rfl) hGraph hProtected' (fun u => (congrFun hLabels (ι u)).symm)
    let U := tail.nextRawWindow.map e.toEmbedding
    let scheduled := ReferenceTrim.scheduledToWindow Wfull
    let Ares := U.map scheduled.symm.toEmbedding
    let Uambient := U.image Subtype.val
    let W0 := Wfull \ liftVertexSet (univ \ Wfull) Ares
    have hLiftA : liftVertexSet (univ \ Wfull) Ares = Uambient := by
      ext x
      constructor
      · intro hx
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
        obtain ⟨u,hu,rfl⟩ := mem_map.mp hy
        exact mem_image.mpr ⟨u,hu,rfl⟩
      · intro hx
        obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
        exact mem_map.mpr ⟨scheduled.symm u,mem_map.mpr ⟨u,hu,rfl⟩,rfl⟩
    have hUambient : Uambient ⊆ Wfull := by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      exact u.property
    have hUcard : Uambient.card = U.card :=
      card_image_of_injective _ Subtype.val_injective
    have hAcard : Ares.card = U.card := card_map _
    obtain ⟨hFullSetCanonical,hCutSub,hCutCard,hFullNat,hFullRealCanonical⟩ :=
      next_prepared_window_card_data W tail.head.trim
    have hFullSet : Wfull = W \ cut := hFullEq.trans hFullSetCanonical
    have hFullReal : (Wfull.card:ℝ) = (W.card:ℝ)-tail.head.trim.card := by
      rw [hFullEq]
      exact hFullRealCanonical
    have hCut : (cut.card:ℝ) ≤ Btotal*W.card :=
      next_prepared_trim_le_total W tail Btotal hβ hTotal
    have hSizes := raw_sample_metadata_quarter_sizes node W hMetadata.1 hβ hq.le
    have hFullCard : Wfull.card = Fintype.card (Survivors tail.head.trim) := card_embeddingWindow ι
    have hFuture : (U.card:ℝ) ≤ 2*q*Wfull.card := by
      rw [Finset.card_map,hFullCard]
      have hh := nextRawWindow_card_le tail hq.le hMetadata.2
      exact card_bound_change_fintype (X := Survivors tail.head.trim)
        tail.nextRawWindow.card (2*q) _ inferInstance hh
    have hResourceReal : (W0.card:ℝ) = (Wfull.card:ℝ)-U.card := by
      rw [show W0 = Wfull \ Uambient by dsimp only [W0]; rw [hLiftA],
        card_sdiff_of_subset hUambient,Nat.cast_sub (card_le_card hUambient),hUcard]
    have hFullReal' : (Wfull.card:ℝ) = (W.card:ℝ)-cut.card := by
      simpa only [cut,card_liftVertexSet] using hFullReal
    have hnParent : (0:ℝ) < Fintype.card (Survivors node.trim) := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < M) node.lower
    have hNumbers := relative_window_budgets
      (Fintype.card (Survivors node.trim)) W.card cut.card Wfull.card U.card W0.card
      Btotal q ρFuture ηInner γInner hnParent hq hq32 hB0 hB8 hSizes.1 hSizes.2
      (Nat.cast_nonneg cut.card) hCut hFullReal' (Nat.cast_nonneg U.card) hFuture
      hResourceReal hqρ hqBank hqStock
    let Z := cut ∪ Uambient
    have hW0 : W0 = W \ Z := by
      dsimp only [W0]
      rw [hLiftA,hFullSet]
      dsimp only [Z]
      ext x
      simp only [mem_sdiff,mem_union,not_or,and_assoc]
    have hZcard : (Z.card:ℝ) ≤ cut.card+U.card := by
      exact_mod_cast (card_union_le cut Uambient).trans (by rw [hUcard])
    have hZbudget : (Z.card:ℝ) ≤ (Btotal+2*q)*W.card :=
      hZcard.trans hNumbers.2.2.2.1
    have hRawData := raw_prepared_layer_window_data tail.head e JW hWindow.1 hWindow.2
    let μwindow := equivSeed e.symm (preparedRawWeights tail.head)
    let ξ := globalRawProfileError 4 E β Wfull.card tail.head.index
    have hRaw : RawProfileAt JW F C ξ μwindow := by
      simpa only [ξ,E,μwindow,← hFullCard] using hRawData.2.2.2
    have hRawQuarter : ξ ≤ 1/4 := by
      simpa only [ξ,E,← hFullCard] using tail.head.raw_cap
    have hξ : 0 ≤ ξ := globalRawProfileError_nonneg E β
      (by dsimp [E]; positivity) hβ _ _
    have hWeights := quarter_raw_profile_weights JW F C ξ μwindow hC hRawQuarter hRaw
    have hPrepared : Dispersal.PreparedCore JW.G JW.lab F (α₀/8) h
        (max (schedule.Nbase j) (schedule.Ns j)) (β j) := by
      apply preparedCore_lower_order JW F (α₀/8) (β j) h N _ hRawData.1
      have ho := schedule.orders j (Nat.le_of_lt_succ j.isLt)
      omega
    have hFull3 : CommonNbrCond JW F (α₀/8) :=
      commonNbrCond_mono hRawData.2.1 (by linarith only [hα])
    have hFullClean : CleanHingeCond JW F (α₀/8) h := hRawData.2.2.1.mono (by linarith only [hα])
    have hProfileBudget := hBudget Wfull.card (by rw [hFullCard]; exact hMBudget.trans tail.head.lower)
      tail.head.index tail.head.index_le
    have hRefError : ξ ≤ schedule.εRef j := hProfileBudget.1
    have hInverseBudget : schedule.K j*(ξ+(5*C/2)*⌊schedule.ζRef j*Wfull.card⌋₊/Wfull.card) ≤
        1/(4*C) := by
      apply hProfileBudget.2.2 (schedule.ζRef j) ⌊schedule.ζRef j*Wfull.card⌋₊
        (schedule.ζRef_pos j (Nat.le_of_lt_succ j.isLt)).le
      · exact Nat.floor_le (mul_nonneg (schedule.ζRef_pos j (Nat.le_of_lt_succ j.isLt)).le
          (Nat.cast_nonneg Wfull.card))
      · exact schedule.hole_inverse j (Nat.le_of_lt_succ j.isLt)
    have hDisjoint : Disjoint W0 Uambient := by
      dsimp only [W0]
      rw [hLiftA]
      exact disjoint_left.mpr (fun _ hx hu => (mem_sdiff.mp hx).2 hu)
    let S := SampledResource.lift Wfull (edges JW ∩ triEdges U)
    have hSdegree : ∀v, SparseEdge.degIn S v ≤ U.card :=
      future_core_lift_degree_le Wfull (edges JW) U
    let D : ℝ := 2^h.choose 2
    have hD : 0 < D := by dsimp [D]; positivity
    have hD1 : 1 ≤ D := by dsimp [D]; exact one_le_pow₀ (by norm_num)
    have hqD : q*D ≤ α₀/64 := by
      have hs := (le_div_iff₀ (by positivity : 0 < 64*D)).mp hqα
      nlinarith only [hs]
    have hAHinge : (Ares.card:ℝ)*D ≤ (α₀/8)*Wfull.card := by
      have hScaled := mul_le_mul_of_nonneg_right hFuture hD.le
      have hRateScaled := mul_le_mul_of_nonneg_right hqD (Nat.cast_nonneg Wfull.card)
      have hαW := mul_nonneg hα.le (Nat.cast_nonneg Wfull.card)
      rw [hAcard]
      nlinarith only [hScaled,hRateScaled,hαW]
    have hAplain : (Ares.card:ℝ) ≤ (α₀/8)*Wfull.card := by
      have hMono := mul_le_mul_of_nonneg_left hD1 (Nat.cast_nonneg Ares.card)
      nlinarith only [hMono,hAHinge]
    have hBankGeometry := window_resource_core_geometry Hactual F α₀ h Wfull Ares
      hα hRawData.2.1 hRawData.2.2.1 hAplain hAHinge
    have hPathBudget : (Btotal+2*q)*(m:ℝ)*(2:ℝ)^m ≤ a/4 := by
      nlinarith only [hBPath,hqPath,ha]
    have hTrimmedPaths : ∀v x y, S07V45.OrigAdm Hraw.G Hraw.lab F v x y →
        a*(Fintype.card (Survivors node.trim):ℝ)^m*q^m/4 ≤
        (S07V24.pathsIn (ComponentRows.link Hraw.G Hraw.lab F v) m x y (W \ Z)).card := by
      intro v x y hvxy
      exact path_count_after_relative_trim _ m hm x y W Z a q (Btotal+2*q)
        ha.le hq.le (by positivity) hMetadata.1.size_upper.le hZbudget hPathBudget
        (paths v x y hvxy)
    have hOrder : 2 ≤ q*Fintype.card (Survivors node.trim) := by
      have hMCeil : ⌈2/q⌉₊ ≤ M := by
        exact ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hMgeom
      have hCeil : (⌈2/q⌉₊:ℝ) ≤ Fintype.card (Survivors node.trim) := by
        exact_mod_cast hMCeil.trans node.lower
      have hDiv := (Nat.le_ceil (2/q)).trans hCeil
      simpa only [mul_comm] using (div_le_iff₀ hq).mp hDiv
    have hW0upper : ((W \ Z).card:ℝ) ≤ 2*q*Fintype.card (Survivors node.trim) := by
      have hs : ((W \ Z).card:ℝ) ≤ W.card := by exact_mod_cast (card_le_card sdiff_subset)
      exact hs.trans hMetadata.1.size_upper.le
    have hHoles : ∀v, (SparseEdge.degIn (edges Hraw \ edges Hactual) v : ℝ) ≤
        ζState*Fintype.card (Survivors node.trim) := by
      intro v
      apply degree_sdiff_change_decEq (edges Hraw) (edges Hactual) v
        (ζState*Fintype.card (Survivors node.trim))
        (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b))
        (@Sym2.instDecidableEq _ (Classical.decEq _))
      simpa only [Hraw,Hactual,current,preparedHost,head.eq_2] using state.holes v
    obtain ⟨hActualRoute,hActualPools⟩ := actual_window_tests_after_sparse_payment
      Hraw Hactual F hGraph hLabels W Z a q ζState
      (α₀*q*Fintype.card (Survivors node.trim)/4) m ha hq hζ.le hm hOrder hW0upper
      hζRoute hHoles hTrimmedPaths hMetadata.1.pools
    rw [← hW0] at hActualRoute hActualPools
    have hqPlain : q ≤ α₀/64 :=
      (by nlinarith only [hqD,mul_le_mul_of_nonneg_left hD1 hq.le])
    have hDelta : Btotal+2*q ≤ α₀/16 := by nlinarith only [hqPlain,hBα,hα]
    have hZscaled : (Z.card:ℝ) ≤ α₀*q*Fintype.card (Survivors node.trim)/8 := by
      have hw := mul_le_mul_of_nonneg_left hMetadata.1.size_upper.le
        (show 0 ≤ Btotal+2*q by positivity)
      have hc := mul_le_mul_of_nonneg_right hDelta
        (show 0 ≤ 2*q*Fintype.card (Survivors node.trim) by positivity)
      nlinarith only [hZbudget,hw,hc]
    have hFloor := Nat.floor_le
      (mul_nonneg hζ.le (Nat.cast_nonneg (Fintype.card (Survivors node.trim))))
    have hHolePool := mul_le_mul_of_nonneg_right hζPool
      (Nat.cast_nonneg (Fintype.card (Survivors node.trim)))
    have hPoolEnough : ∀u v, u ≠ v → ∀k,
        ({Hactual.lab u,Hactual.lab v,k} : Multiset I) ∈ F →
        (q/2)*(α₀/4)*Fintype.card (Survivors node.trim)/2 ≤
          ((commonNbrs Hactual k u v) ∩ W0).card := by
      intro u v huv k hk
      have hp := hActualPools u v huv k hk
      have hPositiveProduct := mul_pos (mul_pos hα hq) hnParent
      nlinarith only [hp,hZscaled,hFloor,hHolePool,hPositiveProduct]
    let Holes := edges Hraw \ edges Hactual
    let HoleGraph := SimpleGraph.fromEdgeSet (Holes : Set (Sym2 (Survivors node.trim)))
    letI : DecidableRel HoleGraph.Adj := Classical.decRel _
    let dHoles := ⌊ζState*Fintype.card (Survivors node.trim)⌋₊
    have hHoleNat : ∀ v, SparseEdge.degIn Holes v ≤ dHoles :=
      fun v => Nat.le_floor (hHoles v)
    have hHoleGraph : ∀ v, HoleGraph.degree v ≤ dHoles := by
      intro v
      have hv := CorePaid.fromEdges_degree_le Holes
        (CorePaid.edges_diagonal_free sdiff_subset) hHoleNat v
      convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
    have hDenseCap : (dHoles : ℝ) ≤ windowRouteRate a q m*Fintype.card (Survivors node.trim) := by
      have hR := windowRouteRate_pos m ha hq
      have hRate := mul_le_mul_of_nonneg_right hζRoute
        (Nat.cast_nonneg (Fintype.card (Survivors node.trim)))
      exact hFloor.trans (by nlinarith only [hRate,mul_nonneg hR.le (Nat.cast_nonneg (Fintype.card (Survivors node.trim)))])
    have hDenseActual := residual_window_path_count Hraw.G HoleGraph Hraw.lab F W0 a q m
      ha hq hm hOrder (by simpa only [hW0] using hW0upper)
      (by simpa only [hW0] using hTrimmedPaths) dHoles hHoleGraph hDenseCap
    have hActEq : Hactual.G=Hraw.G\HoleGraph := graph_eq_raw_sdiff_holes Hraw Hactual hGraph
    rw [←hActEq,←hLabels] at hDenseActual
    have hPath : S07V45.CorePathContract Hactual.G Hactual.lab F W0 (m+1) := by
      letI : ∀ v, DecidableRel (ComponentRows.link Hactual.G Hactual.lab F v).Adj :=
        fun _ => Classical.decRel _
      apply S07V45.contract_of_route (by omega)
      intro v x y hxy
      have hRouteBudget : 0 ≤ (windowRouteRate a q m/4)*Fintype.card (Survivors node.trim) :=
        mul_nonneg (div_pos (windowRouteRate_pos m ha hq) (by norm_num)).le hnParent.le
      obtain ⟨p,hp,hW,-,-⟩ := hActualRoute ∅ ⊥ 0
        (by simpa only [card_empty,Nat.cast_zero] using hRouteBudget)
        (fun u => by simp) (by simpa only [Nat.cast_zero] using hRouteBudget) v x y hxy
      exact ⟨p,hp,hW⟩
    let Jstock := residual Hactual (∅∪S)
    let μhat : Finset (Survivors node.trim) → ℝ := fun Q =>
      state.seed Q/(1+rawStockProfileMargin (α₀/16))
    let RawTests := childExceptionTupleTests eAmbient (allowed Jstock F) Rpast μhat
      (Fintype.card (Survivors node.trim) : ℝ)
    have hBoolCard : Fintype.card Bool ≤ (Fintype.card (Survivors node.trim))^1 := by
      have ht := hMtests.trans hParentLower
      have hTwo : 2 ≤ Fintype.card (Survivors node.trim) := by omega
      simpa only [Fintype.card_bool,pow_one] using hTwo
    have hStockCoeff : ∀ Q, IsAllowed Hactual F Q →
        (1/(2*C))/Fintype.card (Survivors node.trim) ≤ state.seed Q ∧
        state.seed Q ≤ (2*C)/Fintype.card (Survivors node.trim) := by
      intro Q hQ
      simpa only [div_div] using hSeedActual.1 Q hQ
    have hStockLoad : ∀ f ∈ edges Hactual,
        |bdry Hactual F state.seed f-1| ≤ εRaw := by
      intro f hf
      have he : f ∈ Hactual.G.edgeSet := by simpa only [edges,mem_filter,mem_univ,true_and] using hf
      have heq := IsDiffuseSeed.bdry_eq_one hSeedActual he
      simpa only [heq,sub_self,abs_zero] using hεRaw.le
    obtain ⟨Praw,Dstock,qSel,hStock3,hStockLoadRaw,hPrawSub,hPraw,hDSub,hDstock,
      hStockAvoid,hDdegree,hSupply,hDcount,hDambient,hRawControls,hqSel,hWithdrawal⟩ :=
      hStockHost Hactual state.seed W0 ∅ S ∅ 0 U.card (hMstock.trans hParentLower)
        hCommonActual hCleanActual.hingeCond hStockCoeff hStockLoad
        (empty_subset _) (by refine ⟨?_,?_,?_⟩ <;> simp) (by simp)
        (by intro v; simp [TypedTriangle.degIn])
        (by simpa only [Nat.cast_zero] using mul_nonneg hθStock.le hnParent.le)
        (by intro v; simpa only [SparseEdge.degIn,TypedTriangle.degIn] using hSdegree v)
        hNumbers.2.2.2.2.2.2 hOrder (by simpa only [hW0] using hW0upper) hNumbers.2.2.1
        hDenseActual
        (by intro u v huv k hk; convert hPoolEnough u v huv k hk using 1 <;> dsimp only [κGeom] <;> ring)
        Orig eAmbient Rpast Lpast hPastCG Bool RawTests hBoolCard
          (fun ℓ _ _ b Q => childExceptionTupleTests_nonneg _ _ _ _ _ ℓ b Q)
    have hRawC : rawProfileConstant (1/(2*C)) (2*C)=4*C := by
      unfold rawProfileConstant
      have hd : 2/(1/(2*C))=4*C := by field_simp [ne_of_gt hCpos] <;> ring
      rw [hd,max_eq_left (show 2*C ≤ 4*C by linarith only [hC]),
        max_eq_right (show 1 ≤ 4*C by linarith only [hC])]
    have hNorm := raw_stock_normalized_coefficient_window (by positivity : (0 : ℝ) < 1/(2*C))
      (by positivity : (0 : ℝ) < α₀/16) hnParent hStockCoeff ∅ S
    have hNormLoad := raw_stock_normalized_load_window (by positivity : (0 : ℝ) < α₀/16) ∅ S hStockLoadRaw
    have hBoolN : embeddedMixedEligibilityOrder (α₀/32) (4*C) Lpast ≤
        Fintype.card (Survivors node.trim) :=
      embedded_mixed_order_below_tracking_cutoff (α₀/32) (4*C) (by positivity)
        (by linarith only [hC]) 133 67 Lpast depth (Fintype.card Orig)
        (Fintype.card (Survivors node.trim)) (by omega)
        ((le_max_right _ _).trans hRootOrder) hDepth hTracking
    have hStock3' : CommonNbrCond Jstock F (α₀/32) := by
      convert hStock3 using 1 <;> ring
    have hStockExceptions := child_exception_statistics_le_of_capped_bool_controls
      hStock3' (by positivity : (0 : ℝ) < α₀/32) (by linarith only [hC] : 1 ≤ 4*C)
      (fun Q hQ => by simpa only [hRawC] using (hNorm Q hQ).1)
      (fun Q hQ => by simpa only [hRawC] using (hNorm Q hQ).2)
      (fun f hf => (hNormLoad f hf).2.2) eAmbient Rpast Lpast hBoolN hPastCG hPastThree
      Praw hRawControls Dstock hDSub
    have hStockInsert := embedded_insertion_count_le eAmbient Dstock Rpast Lpast
      (4*C) 1 (4*C) (by positivity) (by norm_num) (by positivity)
      (by have hh0 := (le_max_left _ _).trans hRootOrder; omega) hDcount
      (by convert hDambient using 1 <;> ring) hStockExceptions
    trace "INNER actual stock and exception insertion ready"
    let XS := SimpleGraph.fromEdgeSet (BasalIncidence.cover Dstock : Set (Sym2 (Survivors node.trim)))
    let emptyEdges : Finset (Sym2 (Survivors node.trim)) := ∅
    let BS := SimpleGraph.fromEdgeSet (emptyEdges : Set (Sym2 (Survivors node.trim)))
    letI : Fintype XS.edgeSet := XS.fintypeEdgeSet
    letI : Fintype BS.edgeSet := BS.fintypeEdgeSet
    let r := ⌈ρ*Fintype.card (Survivors node.trim)⌉₊
    let r1 := 3*r+forkQ κGeom r+4
    change WeightedWithdrawalResult eAmbient Hactual F (a/2) κGeom m W0 XS BS r
      (S07V27.selA (m+1)) qSel τSel
      (Rpast∪mapConfiguration eAmbient Dstock) (Lpast+1) at hWithdrawal
    obtain ⟨fk,σ,Cpay,DPaid,hFS,hFam,hRresDec,hBase,hBaseSub,hBaseInside,hBaseDegree,
      hResAvoid,hResMeets,hResDegree,hResCG,hResThree,hResCount,hModes⟩ := hWithdrawal
    let Tports := S07V26.XZ XS.edgeFinset W0
    let Rf := S07V26.forkUnion Tports fk
    let Rres := Rf∪(SelSimul.fuelU (univ\W0) σ∪Cpay)
    let Ures := forkModes Tports fk∪(selectorUniverse (univ\W0) σ∪DPaid)
    let DRes := S07V26.modeDec fk Tports ∅∪DPaid
    have hDecResource : IsDecomposition Hactual F Rres DRes := hRresDec
    have hXSEdges : XS.edgeFinset = BasalIncidence.cover Dstock := by
      ext f
      rw [SimpleGraph.mem_edgeFinset]
      simp only [XS,SimpleGraph.edgeSet_fromEdgeSet,Set.mem_sdiff,mem_coe,Sym2.mem_diagSet]
      exact ⟨And.left,fun hf => ⟨hf,CorePaid.edges_diagonal_free
        (CorePaid.basal_subset_edges ⟨Dstock,hDstock⟩) f hf⟩⟩
    have hBSEdges : BS.edgeFinset = ∅ := by
      ext f
      simp only [SimpleGraph.mem_edgeFinset,BS,emptyEdges,SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_sdiff,Set.mem_empty_iff_false,false_and,not_false_eq_true]
      simp
    have hResourceAvoid : Disjoint Rres (BasalIncidence.cover Dstock∪∅) := by
      have hh : Disjoint Rres (XS.edgeFinset∪BS.edgeFinset) := hResAvoid
      rw [hXSEdges,hBSEdges] at hh
      exact hh
    have hResourceDegree : ∀v,(SparseEdge.degIn Rres v : ℝ) ≤
        τSel*Fintype.card (Survivors node.trim) := hResDegree
    have hSU : ∀f∈S,∀v∈f,v∈Uambient := by
      intro f hf v hv
      obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
      induction g using Sym2.ind with
      | _ u w =>
        have hh := mem_triEdges.mp (mem_inter.mp hg).2
        have hmem : v=u.val ∨ v=w.val := by
          simpa only [SampledResource.edgeLift,Sym2.map_mk,Sym2.mem_iff] using hv
        rcases hmem with rfl | rfl
        · exact mem_image.mpr ⟨u,hh.1,rfl⟩
        · exact mem_image.mpr ⟨w,hh.2.1,rfl⟩
    have hResourceS : Disjoint Rres S := disjoint_of_core_incidence W0 Uambient Rres S
      hDisjoint hResMeets hSU
    have hMode : ∀L0 : Finset (Sym2 (Survivors node.trim)),
        L0⊆BasalIncidence.cover Dstock → IsPhysical Hactual F L0 →
        ∃Ps Y Dps,Rres∪L0=Ps∪Y ∧ Disjoint Ps Y ∧ IsDecomposition Hactual F Ps Dps ∧
          Dps⊆Ures ∧ (∀f∈Y,∀v∈f,v∈W0) ∧
          (∀v,(SelSimul.edeg Y v : ℝ)≤τSel*Fintype.card (Survivors node.trim)) ∧
          IsPhysical Hactual F Y := by
      intro L0 hL hPhys
      have hL' : L0⊆XS.edgeFinset := by simpa only [hXSEdges] using hL
      obtain ⟨Ps,Y,hEq,hDis,hDec,hSub,hInside,hDegree,hPhysical⟩ := hModes L0 hL' hPhys
      exact ⟨Ps,Y,_,hEq,hDis,hDec,hSub,hInside,hDegree,hPhysical⟩
    let F0local := ((BasalIncidence.cover Dstock∪Rres)∪∅)∪S
    let F0 := AmbientBank.liftEdges eAmbient F0local
    have hDegreeF0 : ∀x,(SparseEdge.degIn F0local x : ℝ) ≤ ηInner*W0.card := by
      intro x
      have hUnion : (SparseEdge.degIn F0local x : ℝ) ≤
          SparseEdge.degIn (BasalIncidence.cover Dstock) x+SparseEdge.degIn Rres x+
            SparseEdge.degIn S x := by
        have ha := sparse_degree_union_le (BasalIncidence.cover Dstock∪Rres) S x
        have hb := sparse_degree_union_le (BasalIncidence.cover Dstock) Rres x
        have hn : SparseEdge.degIn F0local x ≤
          SparseEdge.degIn (BasalIncidence.cover Dstock) x+SparseEdge.degIn Rres x+
          SparseEdge.degIn S x := by
          dsimp only [F0local]
          simpa only [union_empty] using ha.trans (Nat.add_le_add_right hb _)
        exact_mod_cast hn
      have hd : (SparseEdge.degIn (BasalIncidence.cover Dstock) x : ℝ) ≤
          ρ*Fintype.card (Survivors node.trim) := by
        simpa only [TypedTriangle.degIn,SparseEdge.degIn] using (hDdegree x).le
      have hr := hResourceDegree x
      have hs : (SparseEdge.degIn S x : ℝ) ≤ U.card := by exact_mod_cast hSdegree x
      have hρ := mul_le_mul_of_nonneg_right (hρCap.trans hτSelη) hnParent.le
      have hτ := mul_le_mul_of_nonneg_right hτSelη hnParent.le
      have hcore := mul_le_mul_of_nonneg_left hNumbers.2.2.1 hηInner.le
      have hfuture := hNumbers.2.2.2.2.2.1
      nlinarith only [hUnion,hd,hr,hs,hρ,hτ,hcore,hfuture]
    have hPullF0 : AmbientBank.pullEdges eAmbient F0 = F0local := by
      ext f
      simp only [F0,AmbientBank.pullEdges,mem_preimage,AmbientBank.liftEdges,mem_map]
      constructor
      · rintro ⟨g,hg,he⟩
        exact (AmbientBank.edgeEmbedding eAmbient).injective he ▸ hg
      · intro hf
        exact ⟨f,hf,rfl⟩
    have hDirect3 := nested_prepared_commonNbrCond_direct Hactual F Wfull Ares βb hBankGeometry.1
    have hDirect4 := nested_prepared_hingeCond_direct Hactual F Wfull Ares βb h hBankGeometry.2
    have hWeightsWindow : ∀Q,IsAllowed JW F Q →
        (3/(4*C))/Wfull.card ≤ μwindow Q ∧ μwindow Q ≤ (5*C/4)/Wfull.card := by
      simpa only [Fintype.card_coe,JW,Wfull,embeddingWindowHost] using hWeights
    have hRefUpper : 5*C/4 ≤ 2*C := by linarith only [hC]
    have hReferenceWeights : ∀Q,IsAllowed JW F Q →
        (3/(4*C))/Wfull.card ≤ μwindow Q ∧ μwindow Q ≤ (2*C)/Wfull.card := by
      intro Q hQ
      exact ⟨(hWeightsWindow Q hQ).1,(hWeightsWindow Q hQ).2.trans
        (div_le_div_of_nonneg_right hRefUpper (Nat.cast_nonneg _))⟩
    have hMainTests : ((Lbank+2)*KM+Fintype.card Empty : ℕ) ≤
        (Fintype.card (Survivors node.trim))^1 := by
      have ht := hMtests.trans hParentLower
      simpa only [Fintype.card_empty,add_zero,pow_one] using
        (show (Lbank+2)*KM ≤ Fintype.card (Survivors node.trim) by dsimp only [nTests] at ht; omega)
    trace "INNER core geometry and withdrawal ready"
    have hMainData := hMainHost j (X:=Survivors node.trim) (V:=Orig) eAmbient Hactual HOrig state.seed Wfull W0
      Dstock DRes ∅ Ures Rres ∅ U μwindow F0 Rpast Lpast
    trace "INNER main host/data specialized"
    have hMainBase := hMainData
      ((hMmain j).trans hParentLower) hAmbientAdj hAmbientLab hSeedActual hPhysicalActual
      hCommonActual hCleanActual.hingeCond
    trace "INNER main seed/parent geometry specialized"
    have hMainWindow := hMainBase
      (by simpa only [W0] using hDirect3) (by simpa only [W0] using hDirect4)
      sdiff_subset hNumbers.1 hNumbers.2.1.le
      (by convert hNumbers.2.2.1 using 1 <;> ring)
      hFull3 hFullClean.hingeCond hReferenceWeights (fun f hf => (hRaw.2 f hf).trans hRefError)
      hNumbers.2.2.2.2.1
    trace "INNER main window/reference specialized"
    have hFutureEq : ConcreteLayer.futureEdges Hactual Wfull U = S := by
      exact inter_change_decEq (edges JW) (triEdges U)
        (fun Z => SampledResource.lift Wfull Z=S)
        (@Sym2.instDecidableEq _ (Classical.decEq _))
        (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b)) rfl
    have hDFuture : Disjoint (BasalIncidence.cover Dstock) (ConcreteLayer.futureEdges Hactual Wfull U) := by
      rw [hFutureEq]
      exact hStockAvoid.mono_right subset_union_right
    have hRFuture : Disjoint Rres (ConcreteLayer.futureEdges Hactual Wfull U) := by
      rw [hFutureEq]
      exact hResourceS
    have hProtectedF0 : AmbientBank.liftEdges eAmbient
        ((((BasalIncidence.cover Dstock∪Rres)∪∅)∪ConcreteLayer.futureEdges Hactual Wfull U)) ⊆ F0 := by
      rw [hFutureEq]
    have hPullDegreeTT : ∀x,(TypedTriangle.degIn (AmbientBank.pullEdges eAmbient F0) x : ℝ) ≤
        bankProtectionBudget αp βb h*W0.card := by
      intro x
      rw [hPullF0]
      simpa only [TypedTriangle.degIn,SparseEdge.degIn] using hDegreeF0 x
    have hResourceDegreeTT : ∀x,(TypedTriangle.degIn Rres x : ℝ) ≤
        τSel*Fintype.card (Survivors node.trim) := by
      intro x
      simpa only [TypedTriangle.degIn,SparseEdge.degIn] using hResourceDegree x
    have hγj : 0 < schedule.γRef j := schedule.γRef_pos j (Nat.le_of_lt_succ j.isLt)
    have hMainResources := hMainWindow hDstock hDecResource
      (by refine ⟨?_,?_,?_⟩ <;> simp) (by simp) hResourceAvoid
      hDFuture hRFuture (by simp)
      hProtectedF0 hPullDegreeTT
      (fun x => (hDdegree x).le) hResourceDegreeTT (by intro x; simp; positivity) hSupply
    trace "INNER main stock/withdrawal specialized"
    have hMainPrepared := hMainResources
      hResCG hResThree hPastCG hPastThree hPath hMode Empty (fun k => nomatch k)
      hMainTests (fun k => nomatch k)
    trace "INNER main family/tests specialized"
    obtain ⟨Bbank,E0,D0,hBankCG,hBankThree,hBankCard,hBankCount,hPreCG,hPreThree,hE0,hFutureE0,hRefHoles,
      ψ,hψ,hψ3,hψSupp,hψClose,hPackingByTests⟩ := hMainPrepared
    trace "INNER real bank/reference/psi extracted"
    let Bfull := (Dstock∪Ures)∪Bbank
    let Pre := Rpast∪mapConfiguration eAmbient Bfull
    let Removed := (((BasalIncidence.cover Dstock∪Rres)∪∅)∪Bbank.biUnion triEdges)∪
      SampledResource.lift Wfull E0
    let MainTests := childExceptionTupleTests eAmbient (allowed (residual Hactual Removed) F) Pre ψ
      (Fintype.card (Survivors node.trim) : ℝ)
    obtain ⟨P0,Ccover,Dps,Dclocal,Ytot,hP0,hQ,hStats,hYtot,hYCore,hLam,hErefY,hReserved,
      hDpaid,hP0Paid,hNextCG,hNextThree,hPaidNext,hNextCount⟩ :=
      hPackingByTests Bool MainTests hBoolCard
        (fun ℓ _ _ b Q => childExceptionTupleTests_nonneg _ _ _ _ _ ℓ b Q)
    trace "INNER same P0 and paid decomposition extracted"
    let Q := P0∪Ccover
    let Dpaid := (Q∪Dps)∪Dclocal
    let Rnext := Pre∪mapConfiguration eAmbient Q
    have hBoolNPre : embeddedMixedEligibilityOrder (α₀/32) (4*C) (Lpast+66) ≤
        Fintype.card (Survivors node.trim) :=
      embedded_mixed_order_below_tracking_cutoff (α₀/32) (4*C) (by positivity)
        (by linarith only [hC]) 133 67 (Lpast+66) depth (Fintype.card Orig)
        (Fintype.card (Survivors node.trim)) (by omega)
        ((le_max_right _ _).trans hRootOrder) hDepth hTracking
    have hψ' : IsDiffuseSeed (residual Hactual Removed) F (4*C) ψ := by
      convert hψ using 1 <;> ring
    have hψ3' : CommonNbrCond (residual Hactual Removed) F (α₀/32) := by
      convert hψ3 using 1 <;> ring
    have hMainExceptions := child_exception_statistics_le_of_seed_bool_controls
      hψ' hψ3' (by positivity : (0 : ℝ) < α₀/32) (by linarith only [hC] : 1 ≤ 4*C)
      eAmbient Pre (Lpast+66) hBoolNPre hPreCG hPreThree P0 hStats.extras P0 subset_rfl
    have hMainMonitor : ∑T∈P0,childPaddedWeight eAmbient Pre (Lpast+66) T ≤
        (8*C)*Fintype.card (Survivors node.trim) := by
      have hu := child_padded_target_upper eAmbient Pre (Lpast+66) hPreCG
        (by linarith only [hC] : 1 ≤ 4*C) hnParent hψ'
      have he := (le_abs_self _).trans hStats.previous_relative
      nlinarith only [hu,he]
    have hMainPure : (count P0 : ℝ) ≤ (2*C^3+1)*(Fintype.card (Survivors node.trim) : ℝ)^2 := by
      have hu := target_le_seed_order_square (lt_of_lt_of_le zero_lt_one h2C)
        hSeedActual (Nat.cast_pos.mp hnParent)
      have he := (le_abs_self _).trans hStats.pasch
      nlinarith only [hu,he]
    have hMainInsert := embedded_insertion_count_le eAmbient P0 Pre (Lpast+66)
      (4*C) (2*C^3+1) (8*C) (by positivity) (by positivity) (by positivity)
      (by have hh0 := (le_max_left _ _).trans hRootOrder; omega)
      hMainPure hMainMonitor hMainExceptions
    let n : ℝ := Fintype.card (Survivors node.trim)
    let nRoot : ℝ := Fintype.card Orig
    let J : ℝ := ((Lpast+184 : ℕ) : ℝ)^3
    let KStock := 1+8*C+12*(4*C)^2+7*(4*C)^3
    let KPartial := (2*C^3+1)+16*C+12*(4*C)^2+7*(4*C)^3
    let KResource := withdrawalGeometryCost κGeom q (a/2) m
    let KBank := bankCubicPaymentCoefficient αp βb h db cb Eb
      (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h) Bstar
    let κGeomBank := geometricBankRoundRate αp βb h Pbank
    have hKStock : 0 ≤ KStock := by dsimp only [KStock]; positivity
    have hKPartial : 0 ≤ KPartial := by dsimp only [KPartial]; positivity
    have hKResource : 0 < KResource := withdrawalGeometryCost_pos m hκGeom hq (by positivity)
    have hKBank : 0 ≤ KBank := bankCubicPaymentCoefficient_nonneg hαp h db cb Eb
      (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h) Bstar
    have hκBound : κBank ≤ κGeomBank :=
      bankRoundRate_le_geometric αp βb εcap δcap h Pbank hαp hβb hεcap hδcap
    have hκGeomBank : 0 ≤ κGeomBank := hκBank.le.trans hκBound
    have hCube (s : ℕ) (hs : s ≤ 184) : ((Lpast+s : ℕ) : ℝ)^3 ≤ J :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show Lpast+s ≤ Lpast+184 by omega)) 3
    have hStockInsert' : (count (Rpast∪mapConfiguration eAmbient Dstock) : ℝ) ≤
        count Rpast+KStock*J*nRoot*n := by
      have hc := mul_le_mul_of_nonneg_left (hCube 1 (by omega))
        (show 0 ≤ KStock*nRoot*n by dsimp only [nRoot,n]; positivity)
      have hs : (count (mapConfiguration eAmbient Dstock∪Rpast) : ℝ) ≤
          count Rpast+KStock*((Lpast+1 : ℕ) : ℝ)^3*nRoot*n := by
        convert hStockInsert using 1 <;> dsimp only [KStock,nRoot,n] <;> ring
      rw [union_comm] at hs
      nlinarith only [hs,hc]
    have hXd : ∀v,SelSimul.edeg XS.edgeFinset v ≤ r := by
      intro v
      rw [hXSEdges]
      exact_mod_cast (hDdegree v).le.trans (Nat.le_ceil _)
    have hRootCount : (Tports.card : ℝ) ≤ n*r/2 := by
      have hh : 2*Tports.card ≤ Fintype.card (Survivors node.trim)*r :=
        Envelope.two_card_le_card_mul_degree Tports
          (fun f hf => CorePaid.edges_diagonal_free
            (CorePaid.basal_subset_edges ⟨Dstock,hDstock⟩) f
              (by rw [←hXSEdges]; exact S07V26.XZ_subset XS.edgeFinset W0 hf))
          (fun v => (S07V26.degIn_mono (S07V26.XZ_subset XS.edgeFinset W0) v).trans (hXd v))
      have hr : 2*(Tports.card : ℝ) ≤ n*r := by
        dsimp only [n]
        exact_mod_cast hh
      linarith only [hr]
    have hR1 : r1 ≤ (CorePaid.Explicit.forkQLimit κGeom+6)*(r+1) := by
      have hf := (CorePaid.Explicit.forkQ_limit_spec hκGeom).2 r
      dsimp only [r1]
      nlinarith only [hf]
    have hQsel : qSel ≤ CorePaid.Explicit.selQLimit (windowRouteRate (a/2) q m)
        (S07V27.selA (m+1))*(CorePaid.Explicit.forkQLimit κGeom+6+1)*(r+1) := by
      have hs := hqSel
      change qSel ≤ CorePaid.Explicit.selQLimit (windowRouteRate (a/2) q m)
        (S07V27.selA (m+1))*(r1+1) at hs
      apply hs.trans
      have hh : r1+1 ≤ (CorePaid.Explicit.forkQLimit κGeom+6+1)*(r+1) := by nlinarith only [hR1]
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left _ hh
    have hWRoot : W0.card ≤ Fintype.card Orig :=
      (card_le_univ W0).trans (Fintype.card_le_of_injective eAmbient eAmbient.injective)
    have hRawPayment := withdrawal_raw_payment_le_uniform m hκGeom hq (by positivity : 0 < a/2)
      (Lpast+1) (Fintype.card Orig) (Fintype.card (Survivors node.trim)) W0.card
      Tports.card r r1 (univ\W0).card qSel (Nat.cast_pos.mp hnParent) hWRoot hNumbers.2.2.1
      hRootCount (card_le_univ _) hR1 hQsel
    have hnOne : 1 ≤ n := by
      dsimp only [n]
      exact_mod_cast (show 1 ≤ Fintype.card (Survivors node.trim) from Nat.cast_pos.mp hnParent)
    have hρOne : ρ ≤ 1 := hρCap.trans hτSel1
    have hr : (r : ℝ)+1 ≤ 3*n := by
      have hc := (Nat.ceil_lt_add_one (mul_nonneg hρStock.le hnParent.le)).le
      have hρn := mul_le_mul_of_nonneg_right hρOne hnParent.le
      change (r : ℝ) ≤ ρ*n+1 at hc
      nlinarith only [hc,hρn,hnOne]
    have hWithdrawCost : (count (Rpast∪mapConfiguration eAmbient (Dstock∪Ures)) : ℝ) ≤
        count (Rpast∪mapConfiguration eAmbient Dstock)+3*KResource*J*nRoot*n := by
      have hActual : (count ((Rpast∪mapConfiguration eAmbient Dstock)∪mapConfiguration eAmbient Ures) : ℝ) ≤
          count (Rpast∪mapConfiguration eAmbient Dstock)+
            withdrawalRawPayment κGeom (a/2) m (Lpast+1) (Fintype.card Orig)
              (Fintype.card (Survivors node.trim)) W0.card Tports.card r1 (univ\W0).card qSel := by
        simpa only [withdrawalRawPayment,r1,add_assoc] using hResCount
      have hc := mul_le_mul_of_nonneg_left (hCube 183 (by omega))
        (show 0 ≤ KResource*((r:ℝ)+1)*nRoot by dsimp only [nRoot]; positivity)
      have hSmall := mul_le_mul_of_nonneg_right hr
        (show 0 ≤ KResource*J*nRoot by dsimp only [J,nRoot]; positivity)
      have hPay : withdrawalRawPayment κGeom (a/2) m (Lpast+1) (Fintype.card Orig)
          (Fintype.card (Survivors node.trim)) W0.card Tports.card r1 (univ\W0).card qSel ≤
            3*KResource*J*nRoot*n := by
        change _ ≤ KResource*((r:ℝ)+1)*nRoot*((Lpast+1+182 : ℕ) : ℝ)^3 at hRawPayment
        rw [show Lpast+1+182=Lpast+183 by omega] at hRawPayment
        nlinarith only [hRawPayment,hc,hSmall]
      have hEq : Rpast∪mapConfiguration eAmbient (Dstock∪Ures) =
          (Rpast∪mapConfiguration eAmbient Dstock)∪mapConfiguration eAmbient Ures := by
        simp only [mapConfiguration,map_union,union_assoc]
      rw [hEq]
      nlinarith only [hActual,hPay]
    have hW0pos : 0 < W0.card := Nat.cast_pos.mp (lt_of_lt_of_le (by positivity) hNumbers.2.2.1)
    have hBankCubic := ambient_catalog_bank_inner_payment_le eAmbient W0 αp βb hαp h db cb Eb
      (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h)
      (Bstar*⌊κBank*(W0.card : ℝ)^2⌋₊) Bstar (Lpast+64) κBank hκBank.le hW0pos le_rfl
    have hBankCost : (count Pre : ℝ) ≤ count (Rpast∪mapConfiguration eAmbient (Dstock∪Ures))+
        KBank*κGeomBank*J*nRoot*n := by
      have hActual := hBankCount
      change (count Pre : ℝ) ≤ count (Rpast∪mapConfiguration eAmbient (Dstock∪Ures))+
        (Bstar*⌊κBank*(W0.card : ℝ)^2⌋₊ : ℕ)*
          (Ambient.orderRatio eAmbient*catalogCellPotentialCost αp βb h db cb Eb
            (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h) (Lpast+66)) at hActual
      have hs := mul_le_mul_of_nonneg_right hκBound
        (show 0 ≤ KBank*((Lpast+65 : ℕ) : ℝ)^3*nRoot*n by dsimp only [nRoot,n]; positivity)
      have hc := mul_le_mul_of_nonneg_left (hCube 65 (by omega))
        (show 0 ≤ KBank*κGeomBank*nRoot*n by dsimp only [nRoot,n]; positivity)
      rw [show Lpast+64+2=Lpast+66 by omega,show Lpast+64+1=Lpast+65 by omega] at hBankCubic
      change _ ≤ KBank*κBank*((Lpast+65 : ℕ) : ℝ)^3*nRoot*n at hBankCubic
      nlinarith only [hActual,hBankCubic,hs,hc]
    have hMainInsert' : (count (Pre∪mapConfiguration eAmbient P0) : ℝ) ≤
        count Pre+KPartial*J*nRoot*n := by
      have hs : (count (mapConfiguration eAmbient P0∪Pre) : ℝ) ≤
          count Pre+KPartial*((Lpast+66+1 : ℕ) : ℝ)^3*nRoot*n := by
        convert hMainInsert using 1 <;> dsimp only [KPartial,nRoot,n] <;> ring
      rw [union_comm,show Lpast+66+1=Lpast+67 by omega] at hs
      have hc := mul_le_mul_of_nonneg_left (hCube 67 (by omega))
        (show 0 ≤ KPartial*nRoot*n by dsimp only [nRoot,n]; positivity)
      nlinarith only [hs,hc]
    have hNextCount' : (count Rnext : ℝ) ≤ count (Pre∪mapConfiguration eAmbient P0)+J*nRoot*n := by
      have hs := hNextCount
      change (count Rnext : ℝ) ≤ count (Pre∪mapConfiguration eAmbient P0)+
        1*nRoot*n*((Lpast+68 : ℕ) : ℝ)^3 at hs
      have hc := mul_le_mul_of_nonneg_left (hCube 68 (by omega))
        (show 0 ≤ nRoot*n by dsimp only [nRoot,n]; positivity)
      nlinarith only [hs,hc]
    have hTotalCount : (count Rnext : ℝ) ≤ count Rpast+
        innerAdaptiveGeometryCoefficient α₀ C q a h m*J*nRoot*n := by
      have hSlack : 0 ≤ J*nRoot*n := by dsimp only [J,nRoot,n]; positivity
      have hGeom : innerAdaptiveGeometryCoefficient α₀ C q a h m =
          1+KStock+3*KResource+KBank*κGeomBank+KPartial+1 := rfl
      rw [hGeom]
      nlinarith only [hStockInsert',hWithdrawCost,hBankCost,hMainInsert',hNextCount',hSlack]
    have hCountUniform : (count Rnext : ℝ) ≤ count Rpast+
        Dinner*Fintype.card Orig*((depth : ℝ)+1)^3*Fintype.card (Survivors node.trim) := by
      have hGeomUpper : innerAdaptiveGeometryCoefficient α₀ C q a h m ≤
          |innerAdaptiveGeometryCoefficient α₀ C q a h m|+1 :=
        (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
      have hs := affine_codegree_shift_cube_le Lpast 67 67 depth 184 hLpast
      norm_num only [show 67+67+184=318 by norm_num,Nat.cast_add,Nat.cast_one] at hs
      have hFirst := mul_le_mul_of_nonneg_right hGeomUpper
        (show 0 ≤ J*nRoot*n by dsimp only [J,nRoot,n]; positivity)
      have hSecond := mul_le_mul_of_nonneg_left hs
        (show 0 ≤ (|innerAdaptiveGeometryCoefficient α₀ C q a h m|+1)*nRoot*n by
          dsimp only [nRoot,n]; positivity)
      dsimp only [Dinner,innerAdaptiveDinner]
      dsimp only [J,nRoot,n] at hTotalCount hFirst hSecond
      push_cast at hTotalCount hFirst
      nlinarith only [hTotalCount,hFirst,hSecond]
    trace "INNER uniform count budget ready"
    have hChildOrder : max 1 (max (schedule.nPaid j) schedule.nGeometry) ≤ Wfull.card := by
      have ht : ⌈2*((max 1 (max (schedule.nPaid j) schedule.nGeometry) : ℕ) : ℝ)/q⌉₊ ≤
          Fintype.card (Survivors node.trim) :=
        (le_max_right _ _).trans ((hMRun j).trans hParentLower)
      have hc := (Nat.le_ceil (2*((max 1 (max (schedule.nPaid j) schedule.nGeometry) : ℕ) : ℝ)/q)).trans
        (Nat.cast_le.mpr ht)
      have hp := (div_le_iff₀ hq).mp hc
      have hLow := hNumbers.1
      exact_mod_cast (show ((max 1 (max (schedule.nPaid j) schedule.nGeometry) : ℕ) : ℝ) ≤ Wfull.card by
        nlinarith only [hp,hLow])
    have hFutureE0Class : edges JW∩triEdges U ⊆ E0 := by
      exact inter_change_decEq (edges JW) (triEdges U) (fun Z => Z⊆E0)
        (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b))
        (@Sym2.instDecidableEq _ (Classical.decEq _))
        (by simpa only [ConcreteLayer.referenceHost,JW,Wfull,embeddingWindowHost] using hFutureE0)
    have hRefHolesClass : ∀v,(SparseEdge.degIn (edges JW\E0) v : ℝ) ≤
        schedule.ζRef j*Wfull.card := by
      intro v
      exact degree_sdiff_change_decEq (edges JW) E0 v (schedule.ζRef j*Wfull.card)
        (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b))
        (@Sym2.instDecidableEq _ (Classical.decEq _))
        (by simpa only [ConcreteLayer.referenceHost,JW,Wfull,embeddingWindowHost,
          TypedTriangle.degIn,SparseEdge.degIn] using hRefHoles v)
    have hChildResult := structured_reference_actual_child tail (α₀/8) (β j) (schedule.K j) (schedule.ηSpec j)
      C (schedule.ζRef j) ξ ζState (schedule.Nbase j) (schedule.Ns j) (schedule.nPaid j) schedule.nGeometry
      hC (schedule.ζRef_pos j (Nat.le_of_lt_succ j.isLt)).le (schedule.ref_spec j (Nat.le_of_lt_succ j.isLt))
      hξ (schedule.ref_state j (Nat.le_of_lt_succ j.isLt))
      (schedule.paid_cap j (Nat.le_of_lt_succ j.isLt)) (schedule.paid_smooth j (Nat.le_of_lt_succ j.isLt))
      Hactual ι (fun u v => ⟨hAdjRaw u v,fun hv => hGraph hv⟩)
      (fun u => (congrFun hLabels (ι u)).symm) W0 sdiff_subset μwindow E0 D0 Ytot Dpaid Dpaid
      hChildOrder hPrepared hFull3 hFullClean hWeightsWindow hRaw.2 hE0 hYtot hLam hYCore hErefY hRefHolesClass
      (schedule.ref_clean j (Nat.le_of_lt_succ j.isLt)) hInverseBudget hFutureE0Class
      (by simpa only [empty_union] using hDpaid) subset_rfl
    rw [show (α₀/8)/2=α₀/16 by ring] at hChildResult
    obtain ⟨child,P,hBasal,hDis,hPartition,hDec,hDU,hPeq,hChildEq⟩ := hChildResult
    trace "INNER actual child and literal decomposition extracted"
    have hCanonEdges : embeddedEdges ι (edges child.host) =
        embeddedEdges ι (@edges _ _ canonicalFintype.down child.host) :=
      embedded_edges_change_fintype ι child.host _ canonicalFintype.down
    refine ⟨child,P,Dpaid,Rnext,hDec,?_,?_,subset_union_left.trans subset_union_left,
      hPaidNext,hNextCG,hNextThree,hCountUniform⟩
    · change Disjoint P (AmbientBank.liftEdges ι (@edges _ _ canonicalFintype.down child.host))
      rw [liftEdges_eq_embeddedEdges,←hCanonEdges]
      exact hDis
    · change edges Hactual = P∪AmbientBank.liftEdges ι (@edges _ _ canonicalFintype.down child.host)
      rw [liftEdges_eq_embeddedEdges,←hCanonEdges]
      exact hPartition

#print axioms concrete_inner_adaptive_paid_layers
end TypedTriangle.Pasch
