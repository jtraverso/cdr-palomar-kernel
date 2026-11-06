module
public import RequestProject.TypedTriangle.PaschConcreteStructuredLayer
public import RequestProject.TypedTriangle.PaschRawStockWithdrawalUniformRich
public import RequestProject.TypedTriangle.PaschStructuredActualChild
public import RequestProject.TypedTriangle.PaschOuterPackingUniverseBudget
public import RequestProject.TypedTriangle.PaschWeightedWithdrawalPayment
public import RequestProject.TypedTriangle.PaschWeightedWithdrawalSupport
public import RequestProject.TypedTriangle.PaschOuterResourceLedger
public import RequestProject.TypedTriangle.PaschOuterResourceBudget
public import RequestProject.TypedTriangle.PaschBankTotalPayment
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorConcreteOuterLayer
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
open CatalogNative CatalogNative.Explicit BasalIncidence CorePaid S07V26 S07V27

private theorem inter_change_decEq {Y : Type*}
    (S E : Finset Y) (P : Finset Y → Prop) (d₁ d₂ : DecidableEq Y)
    (hh : P (@Inter.inter _ (@Finset.instInter _ d₁) S E)) :
    P (@Inter.inter _ (@Finset.instInter _ d₂) S E) := by
  cases Subsingleton.elim d₁ d₂
  exact hh

private theorem degree_sdiff_change_decEq {Y : Type}
    (S E : Finset (Sym2 Y)) (v : Y) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 Y))
    (hh : (SparseEdge.degIn (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) S E) v : ℝ) ≤ b) :
    (SparseEdge.degIn (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) S E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hh

private theorem map_configuration_refl {X : Type} (D : Finset (Finset X)) :
    mapConfiguration (Function.Embedding.refl X) D = D := by
  unfold mapConfiguration
  have he : (Finset.mapEmbedding (Function.Embedding.refl X)).toEmbedding = Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro Q
    simp
  rw [he]
  simp

private theorem lift_edges_refl {X : Type} (E : Finset (Sym2 X)) :
    AmbientBank.liftEdges (Function.Embedding.refl X) E = E := by
  unfold AmbientBank.liftEdges
  have he : AmbientBank.edgeEmbedding (Function.Embedding.refl X) = Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro e
    induction e using Sym2.ind with
    | _ u v => rfl
  rw [he]
  simp

private theorem pull_edges_refl {X : Type} (E : Finset (Sym2 X)) :
    AmbientBank.pullEdges (Function.Embedding.refl X) E = E := by
  ext e
  simp [AmbientBank.pullEdges,AmbientBank.edgeEmbedding]

private theorem outer_prepared_window_eq {X : Type} [Fintype X]
    (A : Finset X) (W : Finset (Survivors A)) :
    letI : DecidableEq (Survivors A) := Classical.decEq _
    ∀ B : Finset (Survivors (univ \ W)),
    letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
    embeddingWindow (outerPreparedEmbedding A W B) =
      liftVertexSet A W \ liftVertexSet A (liftVertexSet (univ \ W) B) := by
  letI : DecidableEq (Survivors A) := Classical.decEq _
  intro B
  letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    have hW : x.val.val ∈ W := by simpa using x.val.property
    refine mem_sdiff.mpr ⟨mem_map.mpr ⟨x.val.val,hW,rfl⟩,?_⟩
    intro hB
    have hB' := (mem_liftVertexSet A (liftVertexSet (univ \ W) B) x.val.val).mp hB
    exact x.property ((mem_liftVertexSet (univ \ W) B x.val).mp hB')
  · intro hy
    obtain ⟨hW,hB⟩ := mem_sdiff.mp hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hW
    let xW : Survivors (univ \ W) := ⟨x,by simpa using hx⟩
    have hxB : xW ∉ B := by
      intro hb
      exact hB ((mem_liftVertexSet A (liftVertexSet (univ \ W) B) x).mpr
        ((mem_liftVertexSet (univ \ W) B xW).mpr hb))
    exact mem_map.mpr ⟨⟨xW,hxB⟩,mem_univ _,rfl⟩


/-- Candidate concrete outer assembly. The raw stock, withdrawal, native
bank and partial packing retain their literal witnesses throughout. -/
theorem concrete_outer_paid_layer_with_triangle_monitors_and_pasch {I : Type} (F : Set (Multiset I))
    (α₀ C ζStat τPasch : ℝ) (h d T mOuter qStat : ℕ) (aOuter : ℝ)
    (hα : 0 < α₀) (hC : 1 ≤ C) (hh : 6 ≤ h)
    (hm : 0 < mOuter) (ha : 0 < aOuter) (hOdd : Odd (mOuter+1)) (hLen : 3 ≤ mOuter+1) (hζStat : 0 < ζStat) (hτPasch : 0 < τPasch) :
    ∃ εOuter γStock ηBank : ℝ, 0 < εOuter ∧ 0 < γStock ∧ 0 < ηBank ∧
      ∀ ρFuture qInner ζState Btotal : ℝ,
        0 < ρFuture → 0 < qInner → qInner ≤ 1/32 →
        2*qInner ≤ ρFuture → qInner ≤ ηBank/16 → qInner ≤ γStock/8 →
        qInner ≤ α₀/(64*(2:ℝ)^h.choose 2) →
        qInner*mOuter*(2:ℝ)^mOuter ≤ (aOuter/2)/64 → 0 < ζState →
        0 ≤ Btotal → Btotal ≤ 1/8 → Btotal ≤ α₀/128 →
        Btotal*mOuter*(2:ℝ)^mOuter ≤ (aOuter/2)/64 →
      ∀ (β : ℕ → ℝ) (Ninner : ℕ), (∀ j, 0 ≤ β j) →
        (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1),β j) ≤ Btotal →
      ∀ schedule : ConcreteInnerLayerSchedule F (α₀/8) C ρFuture ζState β h Ninner
          (d+(d+1)*Nat.log 2 T),
      ∃ MrawBudget : ℕ, 1 ≤ MrawBudget ∧
      ∀ qOuter : ℝ, 0 < qOuter → qOuter ≤ 1/32 → 4*qOuter ≤ εOuter →
      ∃ θT : ℝ, ∃ nRoot : ℕ, 0 < θT ∧
      ∀ {X : Type} [Fintype X] (H : Host X I) (μ : Finset X → ℝ),
        nRoot ≤ Fintype.card X → IsDiffuseSeed H F C μ → IsPhysical H F (edges H) →
        CommonNbrCond H F (8*α₀) → CleanHingeCond H F (8*α₀) h →
      ∀ {Nouter Mouter M mInner : ℕ} {aInner εRouteInner t : ℝ}, MrawBudget ≤ M →
      ∀ node : IntrinsicRawPreparedLayer H F α₀ C β h Nouter Mouter d T μ,
        letI : DecidableEq (Survivors node.trim) := Classical.decEq _
      ∀ W : Finset (Survivors node.trim),
        letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
        (1-automaticRelativeError (Fintype.card (Survivors node.trim)))*qOuter*
          Fintype.card (Survivors node.trim) ≤ (W.card:ℝ) →
        (W.card:ℝ) < (1+automaticRelativeError (Fintype.card (Survivors node.trim)))*qOuter*
          Fintype.card (Survivors node.trim) →
        (∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
          (4*α₀)*Fintype.card X*qOuter/2 ≤ ((commonNbrs H k u v) ∩ liftVertexSet node.trim W).card) →
        (∀ v x y, S07V45.OrigAdm H.G H.lab F v x y →
          aOuter*(Fintype.card X:ℝ)^mOuter*qOuter^mOuter/4 ≤
            (S07V24.pathsIn (ComponentRows.link H.G H.lab F v) mOuter x y (liftVertexSet node.trim W)).card) →
      ∀ chain : IntrinsicRawPathsPreparedVortex F α₀ qInner C β h Ninner M d T mInner aInner
          εRouteInner t (restrictedHost (restrictedHost H node.trim) (univ \ W))
          (RawReference.survivorSampledWeights (RawReference.restrictedWeights μ node.trim) W qOuter),
        chain.HasRelativeWindows →
      ∀ (R : Finset (Sym2 X)) (DR : Finset (Finset X)) (dR : ℕ),
        R ⊆ edges H → IsDecomposition H F R DR →
        Disjoint R (triEdges (liftVertexSet node.trim W)) →
        (∀ v, SparseEdge.degIn R v ≤ dR) → (dR:ℝ) ≤ θT*Fintype.card X →
      ∀ (ν : Type) [Fintype ν] (w : ν → Finset X → ℝ),
        (Fintype.card ν:ℝ) ≤ (Fintype.card X:ℝ)^qStat →
        (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
      ∃ P₀ : Finset (Finset X),
        (IsPacking H F P₀ ∧
          (∀ v, (SparseEdge.degIn (edges H\P₀.biUnion triEdges) v : ℝ) ≤ ζStat*Fintype.card X) ∧
          (∀ k, |(∑ Q∈P₀,w k Q)-(∑ Q∈allowed H F,μ Q*w k Q)| ≤
            ζStat*(Fintype.card X : ℝ)^2) ∧
          |(Pasch.count P₀ : ℝ)-Pasch.target μ (allowed H F)| ≤ τPasch*(Fintype.card X : ℝ)^2) ∧
      ∃ state : ActualState chain (2*C) (α₀/16) ζState,
      ∃ Pouter : Finset (Sym2 X), ∃ Dpaid Rnext : Finset (Finset X),
        IsDecomposition H F Pouter Dpaid ∧ P₀ ⊆ Dpaid ∧ Dpaid ⊆ Rnext ∧
        PairCodegreeBound Rnext 67 ∧ (∀ Q∈Rnext,Q.card=3) ∧
        (Fintype.card (Survivors chain.head.trim) : ℝ) ≤ 2*qOuter*Fintype.card X ∧
        (Pasch.count Rnext : ℝ) ≤ Pasch.count P₀+(τPasch/2)*(Fintype.card X : ℝ)^2 ∧
        Disjoint Pouter (R ∪ embeddedEdges (outerPreparedEmbedding node.trim W chain.head.trim) (edges state.host)) ∧
        Disjoint R (embeddedEdges (outerPreparedEmbedding node.trim W chain.head.trim) (edges state.host)) ∧
        edges H = Pouter ∪ (R ∪ embeddedEdges (outerPreparedEmbedding node.trim W chain.head.trim) (edges state.host)) := by
  obtain ⟨εReserve,hεReserve,hMain⟩ := ConcreteLayer.concrete_same_bank_layer F
    C (α₀/16) ζStat τPasch 1 h hC (by positivity) hζStat hτPasch (by norm_num)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hStockWindow : 1/C ≤ C :=
    ((div_le_one hCpos).mpr hC).trans hC
  obtain ⟨εRaw,γStock,hεRaw,hγStock,hRawStock⟩ := raw_stock_weighted_withdrawal_uniform_rich F
    (1/C) C (α₀/16) 1 (aOuter/2) h 0 mOuter (by norm_num) (by positivity)
      hStockWindow (by positivity) (by positivity) hm hOdd
  let ηBank := bankProtectionBudget (α₀/16) (α₀/32) h
  have hηBank : 0 < ηBank := bankProtectionBudget_pos h (by positivity) (by positivity)
  let αp := α₀/16
  let βb := α₀/32
  have hαp : 0 < αp := by dsimp only [αp]; positivity
  have hβb : 0 < βb := by dsimp only [βb]; positivity
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
  let Kbank := bankCubicPaymentCoefficient αp βb h db cb Eb
    (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h) Bstar
  let κGeomBank := geometricBankRoundRate αp βb h Pbank
  have hKbank : 0 ≤ Kbank := bankCubicPaymentCoefficient_nonneg hαp h db cb Eb _ _ _ Bstar
  have hκGeomBank : 0 ≤ κGeomBank := by
    dsimp only [κGeomBank,geometricBankRoundRate,quadraticBankRate]
    have hp := bankProtectionBudget_pos h hαp hβb
    have hd := (ExplicitGeometry.deletionBudget_spec hαp h).1
    positivity
  let bankCost := 2*Kbank*κGeomBank*(65 : ℝ)^3
  let bankSize := 8*(Ecell*Bstar : ℕ)*κGeomBank
  have hBankCost : 0 ≤ bankCost := by dsimp only [bankCost]; positivity
  have hBankSize : 0 ≤ bankSize := by dsimp only [bankSize]; positivity
  let βCount := outerMixedCountBudget (τPasch/4)
  let δSize := outerMixedSizeBudget (4*C) (τPasch/4) 66
  let εMixed := outerMixedTestBudget (4*C) (τPasch/4) 66
  obtain ⟨hβCount,hδSize,hδSize1,hεMixed,hεMixed1,_⟩ :=
    outer_mixed_budgets (4*C) (τPasch/4) 66 (by positivity) (by positivity)
  let qCap := adaptiveOuterRate (εReserve/4) 0 1 (βCount/4) (δSize/4) bankCost bankSize
  obtain ⟨hqCap,hqCapReserve,_,hBankCountCap,hBankSizeCap⟩ :=
    adaptiveOuterRate_spec (εReserve/4) 0 1 (βCount/4) (δSize/4) bankCost bankSize
      (by positivity) (by norm_num) (by norm_num) (by positivity) (by positivity) hBankCost hBankSize
  refine ⟨4*qCap,γStock,ηBank,by positivity,hγStock,hηBank,?_⟩
  intro ρFuture qInner ζState Btotal hρ hq hq32 hqρ hqBank hqStock hqα hqPath hζ
    hB0 hB8 hBα hBPath β Ninner hβ hTotal schedule
  let L := d+(d+1)*Nat.log 2 T
  let E := max 1 (2*C)
  let aEff := aOuter/2
  have haEff : 0 < aEff := by dsimp only [aEff]; positivity
  have hEb : E ≤ 2*C := by dsimp only [E]; exact max_le (by linarith only [hC]) le_rfl
  have hAgenda : ∀r ≤ L,
      schedule.K r*(2*(2*C)*(∑ j ∈ range r,β j)) ≤ 1/(16*C) ∧
      2*(2*C)*(∑ j ∈ range r,β j) ≤ schedule.εRef r/8 := by
    intro r hr
    simpa only [show 2*(2*C)=4*C by ring] using
      And.intro (schedule.prefix_inverse r hr) (schedule.prefix_reference r hr)
  let nBudget := scheduledProfileOrder C schedule.K schedule.εRef L
  have hnBudget : 1 ≤ nBudget := scheduledProfileOrder_pos C schedule.K schedule.εRef L
  have hBudget := scheduled_raw_profile_budget_explicit C E (2*C)
    β schedule.K schedule.εRef L hC (by dsimp only [E]; positivity) hEb hβ
    schedule.K_pos schedule.εRef_pos hAgenda
  refine ⟨max 1 nBudget,le_max_left _ _,?_⟩
  intro qOuter hqOuter hqOuter32 hqOuterCap
  have hqCap_le : qOuter ≤ qCap := by linarith only [hqOuterCap]
  have hqOuterReserve : 4*qOuter ≤ εReserve := by linarith only [hqCap_le,hqCapReserve]
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
      have hh := min_le_left (γMin/8) (1/8)
      linarith only [hh,hγj,hγMin]
    · exact (min_le_right _ _).trans (by norm_num)
  let δcap := min (ExplicitGeometry.deletionBudget βb h) (S07V37.delOf (βb/2) h)/2
  have hδcap : 0 < δcap := by
    have hDel := (ExplicitGeometry.deletionBudget_spec hβb h).1
    have hDel2 : 0 < S07V37.delOf (βb/2) h := S07V37.delOf_pos (by positivity) h
    exact div_pos (lt_min hDel hDel2) (by norm_num)
  have hδcap_le : δcap ≤ min (ExplicitGeometry.deletionBudget βb h) (S07V37.delOf (βb/2) h) := by
    have hp := hδcap
    dsimp only [δcap] at hp ⊢
    linarith only [hp]
  let Λ := physicalWeightMagnitude (αp/2) (βb/2) h db cb MM
  let κBank := bankRoundRate αp βb εcap δcap h Pbank
  let εBank := bankTolerance αp βb εcap h
  let ηPay := StockEntry.Explicit.bankEta κBank (qOuter/2) εBank (2*Ecell*Bstar)
  let δMain := StockEntry.Explicit.monitorCap Λ ηPay KM
  have hΛ : 0 < Λ := physicalWeightMagnitude_pos _ _ _ _ _ _
  have hκBank : 0 < κBank := bankRoundRate_pos h Pbank hαp hβb hεcap hδcap
  have hεBank : 0 < εBank := bankTolerance_pos h hαp hβb hεcap
  obtain ⟨_,_,hδMain,_,_,_,_,_⟩ := StockEntry.Explicit.native_bank_scale_cap_explicit
    κBank (qOuter/2) εBank Λ (2*Ecell*Bstar) KM hκBank (by positivity) hεBank hΛ.le
  let τSel := min (δSize/512) (min δMain (min (qOuter/64) (min (γMin*qOuter/64) (ηBank*qOuter/64))))
  have hτSel : 0 < τSel := by dsimp only [τSel]; positivity
  have hτSelSize : τSel ≤ δSize/512 := min_le_left _ _
  have hτSelδ : τSel ≤ δMain := (min_le_right _ _).trans (min_le_left _ _)
  have hτSelq : τSel ≤ qOuter/64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτSelγ : τSel ≤ γMin*qOuter/64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτSelη : τSel ≤ ηBank*qOuter/64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hτSelCap (j : Fin (L+1)) : τSel ≤ min δMain (min (qOuter/64) (schedule.γRef j*qOuter/64)) := by
    apply le_min hτSelδ
    apply le_min hτSelq
    have hg := mul_le_mul_of_nonneg_right (hγMin_le j) hqOuter.le
    linarith only [hτSelγ,hg]
  let κGeom := α₀*qOuter/16
  have hκGeom : 0 < κGeom := by dsimp only [κGeom]; positivity
  let cost := withdrawalGeometryCost κGeom qOuter aEff mOuter*(183 : ℝ)^3
  have hCost : 0 ≤ cost := by
    dsimp only [cost]
    exact mul_nonneg (withdrawalGeometryCost_pos mOuter hκGeom hqOuter haEff).le (by norm_num)
  let ρcap := outerResourceRate τSel cost (βCount/4)
  obtain ⟨hρcap,hρcapSel,hResourcePay⟩ := outer_resource_rate_and_order τSel cost (βCount/4)
    hτSel hCost (by positivity)
  obtain ⟨θStock,hθStock,hRawByPrecision⟩ := hRawStock qOuter κGeom hqOuter hκGeom
  obtain ⟨ρStock,κStock,hρStock,hρStockCap,hκStock,Nstock,hStockHost⟩ :=
    hRawByPrecision τSel ρcap (βCount/4) hτSel hρcap (by positivity)
  have hρSel : ρStock ≤ τSel := hρStockCap.trans hρcapSel
  have hρCap_j (j : Fin (L+1)) : ρStock ≤ min δMain (min (qOuter/64) (schedule.γRef j*qOuter/64)) :=
    hρSel.trans (hτSelCap j)
  let u := τPasch/(4*(68 : ℝ)^3)
  have hu : 0 < u := by dsimp only [u]; positivity
  have hMainAt (j : Fin (L+1)) := hMain βb (α₀/8) (3/(4*C)) (2*C) ρFuture
    (schedule.ζRef j) (schedule.εRef j) (schedule.γRef j) qOuter εcap δcap
    (schedule.nRef j) (mOuter+1) (qStat+2) hβb (by dsimp only [αp,βb]; linarith only [hα])
    (schedule.γRef_pos j (Nat.le_of_lt_succ j.isLt)) hqOuter hqOuterReserve hεcap (hεcap_j j)
    hδcap hδcap_le hOdd hLen (schedule.reference j (Nat.le_of_lt_succ j.isLt))
      ρStock τSel κStock u hρStock hτSel hκStock hu (hρCap_j j) (hτSelCap j)
  choose nMain hMainHost using hMainAt
  let θT := min θStock (min (qOuter/64) (min (γMin*qOuter/64) (ηBank*qOuter/64)))
  have hθT : 0 < θT := by dsimp only [θT]; positivity
  let nGeometry := (univ : Finset (Fin (L+1))).sup (fun j =>
    max (schedule.nPaid j) schedule.nGeometry)
  let nTests := (Lbank+2)*KM
  obtain ⟨nNoise,hnNoise,hNoise⟩ := exists_egj13_square_order 1 1 εMixed 1 0 (by norm_num) hεMixed
  let nRoot := 1+Nstock+(univ : Finset (Fin (L+1))).sup nMain+⌈2/qOuter⌉₊+
    outerResourceOrder cost (βCount/4)+nTests+⌈2*nGeometry/qOuter⌉₊+nNoise
  refine ⟨θT,nRoot,hθT,?_⟩
  intro X _ H μ hn hSeed hPhysical h3Orig hCleanOrig Nouter Mouter M mInner aInner εRouteInner t hM node
  letI : DecidableEq (Survivors node.trim) := Classical.decEq _
  intro W
  letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
  intro hWlo hWhi hPoolsOrig hPathsOrig chain hMetadata R DR dR hR hRDec hRAvoid hRd hRcap ν _ w hν hw
  let j : Fin (L+1) := ⟨chain.head.index,Nat.lt_succ_of_le chain.head.index_le⟩

  let ι := outerPreparedEmbedding node.trim W chain.head.trim
  let e := embeddingWindowEquiv ι
  let Wraw := liftVertexSet node.trim W
  let Wfull := embeddingWindow ι
  let cut := liftVertexSet node.trim (liftVertexSet (univ \ W) chain.head.trim)
  letI : DecidableEq {x // x ∈ Wfull} := Classical.decEq _
  let JW := embeddingWindowHost ι H
  have hWindowAdj : ∀u v, chain.preparedHost.G.Adj u v ↔ JW.G.Adj (e u) (e v) := fun _ _ => Iff.rfl
  have hWindowLab : ∀u, chain.preparedHost.lab u = JW.lab (e u) := fun _ => rfl
  let U := chain.nextRawWindow.map e.toEmbedding
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
  have hUcard : Uambient.card = U.card := card_image_of_injective _ Subtype.val_injective
  have hAcard : Ares.card = U.card := card_map _
  have hFullSet : Wfull = Wraw \ cut := by
    ext x
    have hs := Finset.ext_iff.mp (outer_prepared_window_eq node.trim W chain.head.trim) x
    simpa only [Wfull,ι,Wraw,cut,mem_sdiff] using hs
  have hFullSub : Wfull ⊆ Wraw := by
    rw [hFullSet]
    exact sdiff_subset
  have hCutSub : cut ⊆ Wraw := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨v,(next_prepared_window_card_data W chain.head.trim).2.1 hv,rfl⟩
  have hRawCard : Wraw.card = W.card := card_liftVertexSet _ _
  have hCut : (cut.card:ℝ) ≤ Btotal*Wraw.card := by
    simpa only [cut,hRawCard,card_liftVertexSet] using
      next_prepared_trim_le_total W chain Btotal hβ hTotal
  have hFullReal : (Wfull.card:ℝ) = (Wraw.card:ℝ)-cut.card := by
    rw [hFullSet,card_sdiff_of_subset hCutSub,Nat.cast_sub (card_le_card hCutSub)]
  have hSizes := raw_prepared_outer_sample_quarter_sizes node W qOuter hβ hqOuter.le
    (hTotal.trans hB8) hWlo hWhi
  have hSizes' : (3/4:ℝ)*qOuter*Fintype.card X ≤ Wraw.card ∧
      (Wraw.card:ℝ) ≤ (5/4:ℝ)*qOuter*Fintype.card X := by simpa only [hRawCard] using hSizes
  have hFullCard : Wfull.card = Fintype.card (Survivors chain.head.trim) := card_embeddingWindow ι
  have hFuture : (U.card:ℝ) ≤ 2*qInner*Wfull.card := by
    rw [Finset.card_map,hFullCard]
    exact nextRawWindow_card_le chain hq.le hMetadata
  have hResourceReal : (W0.card:ℝ) = (Wfull.card:ℝ)-U.card := by
    rw [show W0 = Wfull \ Uambient by dsimp only [W0]; rw [hLiftA],
      card_sdiff_of_subset hUambient,Nat.cast_sub (card_le_card hUambient),hUcard]
  have hnRoot : 1 ≤ nRoot := by dsimp only [nRoot]; omega
  have hnPos : 0 < Fintype.card X := lt_of_lt_of_le
    (lt_of_lt_of_le Nat.zero_lt_one hnRoot) hn
  have hnParent : (0:ℝ) < Fintype.card X := by exact_mod_cast hnPos
  have hOuterProduct : 0 < qOuter*(Fintype.card X:ℝ) := mul_pos hqOuter hnParent
  -- The outer window uses qOuter for size and qInner only for its future.
  have hRaw0 : (0:ℝ) ≤ Wraw.card := Nat.cast_nonneg _
  have hFullRaw : (Wfull.card:ℝ) ≤ Wraw.card := by exact_mod_cast card_le_card hFullSub
  have hCut8 := hCut.trans (mul_le_mul_of_nonneg_right hB8 hRaw0)
  have hFullLow : qOuter*Fintype.card X/2 ≤ Wfull.card := by
    nlinarith only [hFullReal,hCut8,hSizes'.1,hOuterProduct.le]
  have hFullUp : (Wfull.card:ℝ) < 2*qOuter*Fintype.card X := by
    nlinarith only [hFullRaw,hSizes'.2,hOuterProduct]
  have hFull0 : (0:ℝ) ≤ Wfull.card := Nat.cast_nonneg _
  have hFutureSmall : (U.card:ℝ) ≤ (Wfull.card:ℝ)/16 := by
    nlinarith only [hFuture,mul_le_mul_of_nonneg_right hq32 hFull0]
  have hResourceLow : qOuter*Fintype.card X/4 ≤ W0.card := by
    nlinarith only [hResourceReal,hFutureSmall,hFullLow,hOuterProduct.le]
  have hResource0 : (0:ℝ) ≤ W0.card := Nat.cast_nonneg _
  have hFullResource : (Wfull.card:ℝ) ≤ 2*W0.card := by
    nlinarith only [hResourceReal,hFutureSmall,hResource0]
  have hFutureρ : (U.card:ℝ) ≤ ρFuture*Wfull.card :=
    hFuture.trans (mul_le_mul_of_nonneg_right hqρ hFull0)
  have hFutureBank : (U.card:ℝ) ≤ ηBank/2*W0.card := by
    nlinarith only [hFuture,mul_le_mul_of_nonneg_right hqBank hFull0,
      mul_le_mul_of_nonneg_left hFullResource hηBank.le,mul_nonneg hηBank.le hResource0]
  have hFutureStock : (U.card:ℝ) ≤ γStock*Fintype.card X := by
    have hnRaw : (Wraw.card:ℝ) ≤ Fintype.card X := by
      exact_mod_cast (show Wraw.card ≤ Fintype.card X by simpa using card_le_card (subset_univ Wraw))
    have hs := mul_le_mul_of_nonneg_left (hFullRaw.trans hnRaw) (show 0 ≤ 2*qInner by positivity)
    nlinarith only [hFuture,hs,mul_le_mul_of_nonneg_right hqStock hnParent.le,
      mul_pos hγStock hnParent]
  have hCutFuture : (cut.card:ℝ)+U.card ≤ (Btotal+2*qInner)*Wraw.card := by
    nlinarith only [hCut,hFuture,mul_le_mul_of_nonneg_left hFullRaw (show 0 ≤ 2*qInner by positivity)]
  let Z := cut ∪ Uambient
  have hW0 : W0 = Wraw \ Z := by
    dsimp only [W0]
    rw [hLiftA,hFullSet]
    dsimp only [Z]
    ext x
    simp only [mem_sdiff,mem_union]
    tauto
  have hZcard : (Z.card:ℝ) ≤ cut.card+U.card := by
    exact_mod_cast (card_union_le cut Uambient).trans (by rw [hUcard])
  have hZbudget : (Z.card:ℝ) ≤ (Btotal+2*qInner)*Wraw.card := hZcard.trans hCutFuture
  have hRawData := raw_prepared_layer_window_data chain.head e JW hWindowAdj hWindowLab
  let μwindow := equivSeed e.symm (preparedRawWeights chain.head)
  let ξ := globalRawProfileError 4 E β Wfull.card chain.head.index
  have hRaw : RawProfileAt JW F C ξ μwindow := by
    simpa only [ξ,E,← hFullCard] using hRawData.2.2.2
  have hRawQuarter : ξ ≤ 1/4 := by simpa only [ξ,E,← hFullCard] using chain.head.raw_cap
  have hξ : 0 ≤ ξ := globalRawProfileError_nonneg E β (by dsimp [E]; positivity) hβ _ _
  have hWeights := quarter_raw_profile_weights JW F C ξ μwindow hC hRawQuarter hRaw
  have hWeightsWindow : ∀Q,IsAllowed JW F Q →
      (3/(4*C))/Wfull.card ≤ μwindow Q ∧ μwindow Q ≤ (5*C/4)/Wfull.card := by
    simpa only [Fintype.card_coe] using hWeights
  have hPrepared : Dispersal.PreparedCore JW.G JW.lab F (α₀/8) h
      (max (schedule.Nbase j) (schedule.Ns j)) (β j) := by
    apply preparedCore_lower_order JW F (α₀/8) (β j) h Ninner _ hRawData.1
    have ho := schedule.orders j (Nat.le_of_lt_succ j.isLt)
    exact ((le_max_left _ _).trans (le_max_left _ _)).trans ho
  have hFull3 : CommonNbrCond JW F (α₀/8) := commonNbrCond_mono hRawData.2.1 (by linarith only [hα])
  have hFullClean : CleanHingeCond JW F (α₀/8) h := hRawData.2.2.1.mono (by linarith only [hα])
  have hMBudget : nBudget ≤ M := (le_max_right _ _).trans hM
  have hProfileBudget := hBudget Wfull.card (by rw [hFullCard]; exact hMBudget.trans chain.head.lower)
    chain.head.index chain.head.index_le
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
  have hSdegree : ∀v, SparseEdge.degIn S v ≤ U.card := future_core_lift_degree_le Wfull (edges JW) U
  let D : ℝ := 2^h.choose 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; exact one_le_pow₀ (by norm_num)
  have hqD : qInner*D ≤ α₀/64 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 64*D)).mp hqα
    nlinarith only [hs]
  have hAHinge : (Ares.card:ℝ)*D ≤ (α₀/8)*Wfull.card := by
    have hs := mul_le_mul_of_nonneg_right hFuture hD.le
    have hr := mul_le_mul_of_nonneg_right hqD (Nat.cast_nonneg Wfull.card)
    rw [hAcard]
    nlinarith only [hs,hr,mul_nonneg hα.le (Nat.cast_nonneg Wfull.card)]
  have hAplain : (Ares.card:ℝ) ≤ (α₀/8)*Wfull.card := by
    nlinarith only [hAHinge,mul_le_mul_of_nonneg_left hD1 (Nat.cast_nonneg Ares.card)]
  have hBankGeometry := window_resource_core_geometry H F α₀ h Wfull Ares
    hα hRawData.2.1 hRawData.2.2.1 hAplain hAHinge
  have hPathBudget : (Btotal+2*qInner)*(mOuter:ℝ)*(2:ℝ)^mOuter ≤ aEff/4 := by
    change (Btotal+2*qInner)*(mOuter:ℝ)*(2:ℝ)^mOuter ≤ (aOuter/2)/4
    nlinarith only [hqPath,hBPath,ha]
  have hRawUpper : (Wraw.card:ℝ) ≤ 2*qOuter*Fintype.card X := by
    nlinarith only [hSizes'.2,hOuterProduct.le]
  have hTrimmedPaths : ∀v x y, S07V45.OrigAdm H.G H.lab F v x y →
      aEff*(Fintype.card X:ℝ)^mOuter*qOuter^mOuter/4 ≤
        (S07V24.pathsIn (ComponentRows.link H.G H.lab F v) mOuter x y (Wraw \ Z)).card := by
    intro v x y hvxy
    apply path_count_after_relative_trim _ mOuter hm x y Wraw Z aEff qOuter (Btotal+2*qInner)
      haEff.le hqOuter.le (by positivity) hRawUpper hZbudget hPathBudget
    convert hPathsOrig v x y hvxy using 1 <;> dsimp [aEff,Wraw] <;> ring
  have hOrder : 2 ≤ qOuter*Fintype.card X := by
    have hCeil : (⌈2/qOuter⌉₊:ℝ) ≤ Fintype.card X := by
      exact_mod_cast (by dsimp only [nRoot] at hn; omega)
    exact ((div_le_iff₀ hqOuter).mp ((Nat.le_ceil (2/qOuter)).trans hCeil)).trans_eq
      (mul_comm (Fintype.card X:ℝ) qOuter)
  have hW0upper : ((Wraw \ Z).card:ℝ) ≤ 2*qOuter*Fintype.card X := by
    have hs : ((Wraw \ Z).card:ℝ) ≤ Wraw.card := by
      exact_mod_cast card_le_card (sdiff_subset : Wraw \ Z ⊆ Wraw)
    exact hs.trans hRawUpper
  have hPools : ∀u v, u ≠ v → ∀k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
      α₀*qOuter*Fintype.card X/4 ≤ ((commonNbrs H k u v) ∩ Wraw).card := by
    intro u v huv k hk
    have hp := hPoolsOrig u v huv k hk
    dsimp [Wraw]
    nlinarith only [hp,mul_nonneg (mul_nonneg hα.le hqOuter.le) hnParent.le]
  obtain ⟨hActualRoute,hActualPools⟩ := actual_window_tests_after_sparse_payment H H F le_rfl rfl
    Wraw Z aEff qOuter 0 (α₀*qOuter*Fintype.card X/4) mOuter haEff hqOuter (by norm_num) hm
    hOrder hW0upper (by exact (div_pos (windowRouteRate_pos mOuter haEff hqOuter) (by norm_num)).le)
    (by intro v; simp [TypedTriangle.degIn]) hTrimmedPaths hPools
  rw [← hW0] at hActualRoute hActualPools
  have hqPlain : qInner ≤ α₀/64 := by nlinarith only [hqD,mul_le_mul_of_nonneg_left hD1 hq.le]
  have hDelta : Btotal+2*qInner ≤ α₀/16 := by nlinarith only [hBα,hqPlain,hα]
  have hZscaled : (Z.card:ℝ) ≤ α₀*qOuter*Fintype.card X/8 := by
    have hw := mul_le_mul_of_nonneg_left hRawUpper (show 0 ≤ Btotal+2*qInner by positivity)
    have hc := mul_le_mul_of_nonneg_right hDelta (show 0 ≤ 2*qOuter*Fintype.card X by positivity)
    nlinarith only [hZbudget,hw,hc]
  have hPoolEnough : ∀u v, u ≠ v → ∀k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
      (qOuter/2)*(α₀/4)*Fintype.card X/2 ≤ ((commonNbrs H k u v) ∩ W0).card := by
    intro u v huv k hk
    have hp := hActualPools u v huv k hk
    norm_num at hp
    nlinarith only [hp,hZscaled,mul_nonneg hα.le hOuterProduct.le]
  have hSwithin : S ⊆ triEdges Wraw := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    induction g using Sym2.ind with
    | _ u v =>
      have hguv := (mem_triEdges.mp (mem_inter.mp hg).2)
      exact mem_triEdges.mpr ⟨hFullSub u.property,hFullSub v.property,
        fun he => hguv.2.2 (Subtype.ext he)⟩
  have hRS : Disjoint R S := hRAvoid.mono_right hSwithin

  have hnStock : Nstock ≤ Fintype.card X := by dsimp only [nRoot] at hn; omega
  have hnMain : nMain j ≤ Fintype.card X := by
    have hj := Finset.le_sup (f := nMain) (mem_univ j)
    dsimp only [nRoot] at hn
    omega
  have hnResource : outerResourceOrder cost (βCount/4) ≤ Fintype.card X := by
    dsimp only [nRoot] at hn; omega
  have hnNoise : nNoise ≤ Fintype.card X := by dsimp only [nRoot] at hn; omega
  have hnTests : nTests ≤ Fintype.card X := by dsimp only [nRoot] at hn; omega
  have hTStock : (dR : ℝ) ≤ θStock*Fintype.card X :=
    hRcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnParent.le)
  have hRawWeights : ∀ Q,IsAllowed H F Q → (1/C)/Fintype.card X ≤ μ Q ∧ μ Q ≤ C/Fintype.card X := by
    intro Q hQ
    simpa only [div_div] using hSeed.1 Q hQ
  have hRawLoad : ∀e∈edges H,|bdry H F μ e-1| ≤ εRaw := by
    intro e he
    have he' : e∈H.G.edgeSet := by simpa [edges] using he
    simp only [IsDiffuseSeed.bdry_eq_one hSeed he',sub_self,abs_zero]
    exact hεRaw.le
  have hStockPaths : ∀v x y,S07V45.OrigAdm H.G H.lab F v x y →
      aEff*(Fintype.card X : ℝ)^mOuter*qOuter^mOuter/4 ≤
        (S07V24.pathsIn (ComponentRows.link H.G H.lab F v) mOuter x y W0).card := by
    simpa only [hW0] using hTrimmedPaths
  have hStockPool : ∀u v,u≠v → ∀k,({H.lab u,H.lab v,k} : Multiset I)∈F →
      κGeom*Fintype.card X ≤ ((commonNbrs H k u v)∩W0).card := by
    intro u v huv k hk
    convert hPoolEnough u v huv k hk using 1 <;> dsimp only [κGeom] <;> ring
  let ιId := Function.Embedding.refl X
  have hEmptyCG : PairCodegreeBound (∅ : Finset (Finset X)) 0 := by intro x y hxy; simp
  obtain ⟨Praw,Dstock,qSel,hStockH3,hStockLoad,hPsub,hPraw,hDP,hDstock,hDAvoid,hDd,hSupply,
    hStockCount,hAmbientStock,hControls,hqSel,hWithdrawal⟩ :=
    hStockHost H μ W0 R S DR dR U.card hnStock
      (commonNbrCond_mono h3Orig (by change α₀/16 ≤ 8*α₀; linarith only [hα]))
      ((hCleanOrig.mono (by change α₀/16 ≤ 8*α₀; linarith only [hα])).hingeCond)
      hRawWeights hRawLoad hR hRDec hRS hRd hTStock hSdegree hFutureStock hOrder
      (by rw [hW0]; exact hW0upper) hResourceLow hStockPaths hStockPool X ιId ∅ 0 hEmptyCG
      Unit (fun _ _ _ => 0) (by simp) (by intros; exact le_rfl)
  let XS := SimpleGraph.fromEdgeSet (BasalIncidence.cover Dstock : Set (Sym2 X))
  let BS := SimpleGraph.fromEdgeSet (R : Set (Sym2 X))
  letI : Fintype XS.edgeSet := XS.fintypeEdgeSet
  letI : Fintype BS.edgeSet := BS.fintypeEdgeSet
  let r := ⌈ρStock*Fintype.card X⌉₊
  let r1 := 3*r+forkQ κGeom r+4
  change WeightedWithdrawalResult ιId H F aEff κGeom mOuter W0 XS BS r (S07V27.selA (mOuter+1))
    qSel τSel (∅∪mapConfiguration ιId Dstock) 1 at hWithdrawal
  obtain ⟨fk,σ,Cpay,DPaid,hFS,hFam,hRresDec,hBase,hBaseSub,hBaseInside,hBaseDegree,
    hResAvoid,hResMeets,hResDegree,hResCG,hResThree,hResCount,hModes⟩ := hWithdrawal
  let Tports := S07V26.XZ XS.edgeFinset W0
  let Rf := S07V26.forkUnion Tports fk
  let Rres := Rf∪(SelSimul.fuelU (univ\W0) σ∪Cpay)
  let Ures := forkModes Tports fk∪(selectorUniverse (univ\W0) σ∪DPaid)
  let DRes := S07V26.modeDec fk Tports ∅∪DPaid
  have hDecResource : IsDecomposition H F Rres DRes := hRresDec
  have hResCG' : PairCodegreeBound Ures 63 := by
    simpa only [ιId,map_configuration_refl] using hResCG
  have hResThree' : ∀Q∈Ures,Q.card=3 := hResThree
  have hXSEdges : XS.edgeFinset = BasalIncidence.cover Dstock := by
    ext e
    rw [SimpleGraph.mem_edgeFinset]
    simp only [XS,SimpleGraph.edgeSet_fromEdgeSet,Set.mem_sdiff,mem_coe,Sym2.mem_diagSet]
    exact ⟨And.left,fun he => ⟨he,CorePaid.edges_diagonal_free (CorePaid.basal_subset_edges ⟨Dstock,hDstock⟩) e he⟩⟩
  have hBSEdges : BS.edgeFinset = R := by
    ext e
    rw [SimpleGraph.mem_edgeFinset]
    simp only [BS,SimpleGraph.edgeSet_fromEdgeSet,Set.mem_sdiff,mem_coe,Sym2.mem_diagSet]
    exact ⟨And.left,fun he => ⟨he,CorePaid.edges_diagonal_free hR e he⟩⟩
  have hResourceAvoid : Disjoint Rres (BasalIncidence.cover Dstock∪R) := by
    have hh : Disjoint Rres (XS.edgeFinset∪BS.edgeFinset) := hResAvoid
    rw [hXSEdges,hBSEdges] at hh
    exact hh
  have hResourceDegree : ∀v,(SparseEdge.degIn Rres v : ℝ) ≤ τSel*Fintype.card X := hResDegree
  have hSU : ∀f∈S,∀v∈f,v∈Uambient := by
    intro f hf v hv
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    induction g using Sym2.ind with
    | _ u w =>
      have hh := mem_triEdges.mp (mem_inter.mp hg).2
      change v∈s(u.val,w.val) at hv
      have hmem : v=u.val ∨ v=w.val := Sym2.mem_iff.mp hv
      rcases hmem with rfl | rfl
      · exact mem_image.mpr ⟨u,hh.1,rfl⟩
      · exact mem_image.mpr ⟨w,hh.2.1,rfl⟩
  have hResourceS : Disjoint Rres S := disjoint_of_core_incidence W0 Uambient Rres S
    hDisjoint hResMeets hSU
  have hResSupport : ∀Q∈Ures,triEdges Q⊆Rres∪BasalIncidence.cover Dstock := by
    have hh := weighted_withdrawal_universe_edges_subset H F W0 XS BS fk σ Cpay DPaid
      (S07V27.selA (mOuter+1)) qSel hFS hFam hRresDec
    have hh' : ∀Q∈Ures,triEdges Q⊆Rres∪XS.edgeFinset := hh
    rw [hXSEdges] at hh'
    exact hh'
  have hResSize : (Ures.card : ℝ) ≤ 63*(τSel+ρStock)*(Fintype.card X : ℝ)^2 :=
    weighted_universe_card_le_real_degree_caps ιId Ures Rres (BasalIncidence.cover Dstock)
      hResCG hResThree hResSupport τSel ρStock hResourceDegree (fun v => (hDd v).le)
  have hMode : ∀L0 : Finset (Sym2 X),L0⊆BasalIncidence.cover Dstock → IsPhysical H F L0 →
      ∃Ps Y Dps,Rres∪L0=Ps∪Y ∧ Disjoint Ps Y ∧ IsDecomposition H F Ps Dps ∧ Dps⊆Ures ∧
        (∀e∈Y,∀v∈e,v∈W0) ∧ (∀v,(SelSimul.edeg Y v : ℝ)≤τSel*Fintype.card X) ∧ IsPhysical H F Y := by
    intro L0 hL hPhys
    have hL' : L0⊆XS.edgeFinset := by simpa only [hXSEdges] using hL
    obtain ⟨Ps,Y,hEq,hDis,hDec,hSub,hInside,hDegree,hPhysical⟩ := hModes L0 hL' hPhys
    exact ⟨Ps,Y,_,hEq,hDis,hDec,hSub,hInside,hDegree,hPhysical⟩

  let F0 := ((BasalIncidence.cover Dstock∪Rres)∪R)∪S
  have hDegreeF0 : ∀x,(SparseEdge.degIn F0 x : ℝ) ≤ ηBank*W0.card := by
    intro x
    have hUnion : (SparseEdge.degIn F0 x : ℝ) ≤
        SparseEdge.degIn (BasalIncidence.cover Dstock) x+SparseEdge.degIn Rres x+
          SparseEdge.degIn R x+SparseEdge.degIn S x := by
      have ha := SelSimul.edeg_union_le ((BasalIncidence.cover Dstock∪Rres)∪R) S x
      have hb := SelSimul.edeg_union_le (BasalIncidence.cover Dstock∪Rres) R x
      have hc := SelSimul.edeg_union_le (BasalIncidence.cover Dstock) Rres x
      exact_mod_cast (show SparseEdge.degIn F0 x ≤
        SparseEdge.degIn (BasalIncidence.cover Dstock) x+SparseEdge.degIn Rres x+
          SparseEdge.degIn R x+SparseEdge.degIn S x by
        dsimp only [F0]
        simp only [SparseEdge.degIn,SelSimul.edeg] at ha hb hc ⊢
        omega)
    have hD : (SparseEdge.degIn (BasalIncidence.cover Dstock) x : ℝ) ≤ ρStock*Fintype.card X := by
      simpa only [SparseEdge.degIn,TypedTriangle.degIn,SelSimul.edeg] using (hDd x).le
    have hRes := hResourceDegree x
    have hRnat : (SparseEdge.degIn R x : ℝ) ≤ dR := by exact_mod_cast hRd x
    have hSnat : (SparseEdge.degIn S x : ℝ) ≤ U.card := by exact_mod_cast hSdegree x
    have hρRate := mul_le_mul_of_nonneg_right (hρSel.trans hτSelη) hnParent.le
    have hτRate := mul_le_mul_of_nonneg_right hτSelη hnParent.le
    have hθRate : (dR : ℝ) ≤ ηBank*qOuter/64*Fintype.card X :=
      hRcap.trans (mul_le_mul_of_nonneg_right
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hnParent.le)
    have hCore := mul_le_mul_of_nonneg_left hResourceLow hηBank.le
    have hηW : 0 ≤ ηBank*(W0.card : ℝ) := mul_nonneg hηBank.le (Nat.cast_nonneg _)
    nlinarith only [hUnion,hD,hRes,hRnat,hSnat,hρRate,hτRate,hθRate,hCore,hFutureBank,hηW]
  have hMainTests : ((Lbank+2)*KM+Fintype.card ν : ℕ) ≤ (Fintype.card X)^(qStat+2) := by
    have hn2 : (2 : ℝ) ≤ Fintype.card X := by
      have hCeil : 2 ≤ Fintype.card X := by
        have hp := hOrder
        have hqn := mul_le_mul_of_nonneg_right hqOuter32 hnParent.le
        have hN : (2 : ℝ) ≤ Fintype.card X := by nlinarith only [hp,hqn,hnParent]
        exact_mod_cast hN
      exact_mod_cast hCeil
    have hSum : ((Lbank+2)*KM : ℕ)+Fintype.card ν ≤
        (Fintype.card X : ℝ)+(Fintype.card X : ℝ)^qStat := by
      have hTestReal : (((Lbank+2)*KM : ℕ) : ℝ) ≤ Fintype.card X := by exact_mod_cast hnTests
      push_cast at hTestReal ⊢
      exact add_le_add hTestReal hν
    exact_mod_cast hSum.trans (CatalogNative.polynomial_monitor_sum_bound (Fintype.card X : ℝ) qStat hn2)
  have hReferenceWeights : ∀Q,IsAllowed JW F Q →
      (3/(4*C))/Wfull.card ≤ μwindow Q ∧ μwindow Q ≤ (2*C)/Wfull.card := by
    intro Q hQ
    have hh := hWeightsWindow Q hQ
    refine ⟨hh.1,hh.2.trans ?_⟩
    exact div_le_div_of_nonneg_right (by linarith only [hC]) (Nat.cast_nonneg _)
  have hTerminalDegree : ∀v,(SparseEdge.degIn R v : ℝ) ≤
      min (qOuter/64) (schedule.γRef j*qOuter/64)*Fintype.card X := by
    intro v
    have hNat : (SparseEdge.degIn R v : ℝ) ≤ dR := by exact_mod_cast hRd v
    apply hNat.trans (hRcap.trans (mul_le_mul_of_nonneg_right ?_ hnParent.le))
    apply le_min
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · have hs : θT ≤ γMin*qOuter/64 :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have hg := mul_le_mul_of_nonneg_right (hγMin_le j) hqOuter.le
      linarith only [hs,hg]
  have hRouteBudget : 0 ≤ (windowRouteRate aEff qOuter mOuter/4)*(Fintype.card X : ℝ) :=
    mul_nonneg (div_pos (windowRouteRate_pos mOuter haEff hqOuter) (by norm_num)).le hnParent.le
  have hCorePath : S07V45.CorePathContract H.G H.lab F W0 (mOuter+1) := by
    letI : ∀v,DecidableRel (ComponentRows.link H.G H.lab F v).Adj := fun _ => Classical.decRel _
    apply S07V45.contract_of_route (by omega)
    intro v x y hxy
    obtain ⟨p,hp,hW,-,-⟩ := hActualRoute ∅ ⊥ 0
      (by simpa only [card_empty,Nat.cast_zero] using hRouteBudget)
      (fun u => by simp) (by simpa only [Nat.cast_zero] using hRouteBudget) v x y hxy
    exact ⟨p,hp,hW⟩
  have hCore3 : SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {x // x∈W0} → X)) (H.lab ∘ Subtype.val) F βb :=
    nested_prepared_commonNbrCond_direct H F Wfull Ares βb hBankGeometry.1
  have hCore4 : SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {x // x∈W0} → X)) (H.lab ∘ Subtype.val) F βb h :=
    nested_prepared_hingeCond_direct H F Wfull Ares βb h hBankGeometry.2
  trace "OUTER core geometry ready"
  have hMainData := hMainHost j (X:=X) (V:=X) ιId H H μ Wfull W0 Dstock DRes DR Ures
    Rres R U μwindow F0 ∅ 0
  trace "OUTER main host/data specialized"
  have hMainBase := hMainData hnMain (fun _ _ hv => hv) (fun _ => rfl) hSeed hPhysical
    (commonNbrCond_mono h3Orig (by change α₀/16 ≤ 8*α₀; linarith only [hα]))
    ((hCleanOrig.mono (by change α₀/16 ≤ 8*α₀; linarith only [hα])).hingeCond)
  trace "OUTER main seed/parent geometry specialized"
  have hMainWindow := hMainBase hCore3 hCore4 (show W0⊆Wfull from sdiff_subset)
    hFullLow hFullUp.le (by convert hResourceLow using 1 <;> ring)
    hFull3 hFullClean.hingeCond hReferenceWeights (fun e he => (hRaw.2 e he).trans hRefError) hFutureρ
  trace "OUTER main window/reference specialized"
  have hFutureEq : ConcreteLayer.futureEdges H Wfull U = S := by
    exact inter_change_decEq (edges JW) (triEdges U)
      (fun Z => SampledResource.lift Wfull Z=S)
      (@Sym2.instDecidableEq _ (Classical.decEq _))
      (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b)) rfl
  have hDFuture : Disjoint (BasalIncidence.cover Dstock) (ConcreteLayer.futureEdges H Wfull U) := by
    rw [hFutureEq]
    exact hDAvoid.mono_right subset_union_right
  have hResFuture : Disjoint Rres (ConcreteLayer.futureEdges H Wfull U) := by
    rw [hFutureEq]
    exact hResourceS
  have hTerminalFuture : Disjoint R (ConcreteLayer.futureEdges H Wfull U) := by
    rw [hFutureEq]
    exact hRS
  have hProtected : AmbientBank.liftEdges ιId
      ((((BasalIncidence.cover Dstock∪Rres)∪R)∪ConcreteLayer.futureEdges H Wfull U)) ⊆ F0 := by
    rw [hFutureEq,lift_edges_refl]
  have hPullDegreeTT : ∀x,(TypedTriangle.degIn (AmbientBank.pullEdges ιId F0) x : ℝ) ≤
      bankProtectionBudget αp βb h*W0.card := by
    intro x
    rw [pull_edges_refl]
    simpa only [TypedTriangle.degIn,SparseEdge.degIn,SelSimul.edeg] using hDegreeF0 x
  have hResourceDegreeTT : ∀x,(TypedTriangle.degIn Rres x : ℝ) ≤ τSel*Fintype.card X := by
    intro x
    simpa only [TypedTriangle.degIn,SparseEdge.degIn,SelSimul.edeg] using hResourceDegree x
  have hTerminalDegreeTT : ∀x,(TypedTriangle.degIn R x : ℝ) ≤
      min (qOuter/64) (schedule.γRef j*qOuter/64)*Fintype.card X := by
    intro x
    simpa only [TypedTriangle.degIn,SparseEdge.degIn,SelSimul.edeg] using hTerminalDegree x
  trace "OUTER future-edge instances aligned"
  have hMainDecomp := hMainWindow hDstock hDecResource hRDec
  trace "OUTER main resource decompositions specialized"
  have hMainDisjoint := hMainDecomp (hDAvoid.mono_right subset_union_left) hResourceAvoid
  trace "OUTER main stock/resource disjoint specialized"
  have hMainFuture := hMainDisjoint hDFuture hResFuture hTerminalFuture
  trace "OUTER main protected-future disjoint specialized"
  have hMainProtected := hMainFuture hProtected
  trace "OUTER main F0 inclusion specialized"
  have hMainDegree := hMainProtected hPullDegreeTT
  trace "OUTER main F0 degree specialized"
  have hMainResources := hMainDegree (fun x => (hDd x).le) hResourceDegreeTT hTerminalDegreeTT hSupply
  trace "OUTER main stock/withdrawal specialized"
  have hMainPrepared := hMainResources hResCG hResThree hEmptyCG (by simp) hCorePath hMode ν w hMainTests hw
  trace "OUTER main family/tests specialized"
  obtain ⟨Bbank,E0,D0,hBankCG,hBankThree,hBankCard,hBankCount,hPreCG,hPreThree,hE0,hFutureE0,hHoles,
    ψ,hψ,hψ3,hψSupp,hψClose,hPackingByTests⟩ := hMainPrepared
  trace "OUTER bank/reference/psi extracted"
  obtain ⟨P0,Ccover,Dps,Dclocal,Ytot,hP0,hQ,hStats,hYtot,hYCore,hLam,hErefY,hReserved,
    hDpaid,hP0Paid,hNextCG,hNextThree,hPaidNext,hNextCount⟩ :=
    hPackingByTests Unit (fun _ _ _ => 0) (by simpa only [Fintype.card_unique] using
      (one_le_pow₀ (show 1 ≤ Fintype.card X by omega) : 1 ≤ (Fintype.card X)^(qStat+2))) (by intros; exact le_rfl)
  trace "OUTER same P0 and paid decomposition extracted"
  let Bfull := (Dstock∪Ures)∪Bbank
  let Pre := Bfull
  let Q := P0∪Ccover
  let Dpaid := (Q∪Dps)∪Dclocal
  let Rnext := Bfull∪Q
  have hNextCG' : PairCodegreeBound Rnext 67 := by
    simpa only [ιId,map_configuration_refl,empty_union,Nat.zero_add] using hNextCG
  have hNextThree' : ∀Q∈Rnext,Q.card=3 := by
    simpa only [ιId,map_configuration_refl,empty_union] using hNextThree
  have hPaidNext' : Dpaid⊆Rnext := by
    simpa only [ιId,map_configuration_refl,empty_union] using hPaidNext
  have hPreCG' : PairCodegreeBound Bfull 66 := by
    simpa only [ιId,map_configuration_refl,empty_union,Nat.zero_add] using hPreCG
  have hPreThree' : ∀Q∈Bfull,Q.card=3 := by
    simpa only [ιId,map_configuration_refl,empty_union] using hPreThree
  have hNextCount' : (count Rnext : ℝ) ≤ count (Bfull∪P0)+u*(Fintype.card X : ℝ)^2*(68 : ℝ)^3 := by
    simpa only [Rnext,Bfull,Q,ιId,map_configuration_refl,empty_union,Nat.zero_add,Nat.cast_ofNat,pow_two,mul_assoc] using hNextCount
  -- The universe budget below uses independent count and support/cardinality estimates.

  trace "OUTER literal ledger normalized"
  have hXd : ∀v,SelSimul.edeg XS.edgeFinset v ≤ r := by
    intro v
    rw [hXSEdges]
    exact_mod_cast (hDd v).le.trans (Nat.le_ceil _)
  have hRootCount : (Tports.card : ℝ) ≤ (Fintype.card X : ℝ)*r/2 := by
    have hh : 2*Tports.card ≤ Fintype.card X*r := Envelope.two_card_le_card_mul_degree Tports
      (fun e he => CorePaid.edges_diagonal_free
        (CorePaid.basal_subset_edges ⟨Dstock,hDstock⟩) e (by
          rw [←hXSEdges]; exact S07V26.XZ_subset XS.edgeFinset W0 he))
      (fun v => (S07V26.degIn_mono (S07V26.XZ_subset XS.edgeFinset W0) v).trans (hXd v))
    have hr : 2*(Tports.card : ℝ) ≤ (Fintype.card X : ℝ)*r := by exact_mod_cast hh
    linarith only [hr]
  have hR1 : r1 ≤ (CorePaid.Explicit.forkQLimit κGeom+6)*(r+1) := by
    have hf := (CorePaid.Explicit.forkQ_limit_spec hκGeom).2 r
    dsimp only [r1]
    nlinarith only [hf]
  have hQsel : qSel ≤ CorePaid.Explicit.selQLimit (windowRouteRate aEff qOuter mOuter)
      (S07V27.selA (mOuter+1))*(CorePaid.Explicit.forkQLimit κGeom+6+1)*(r+1) := by
    have hq := hqSel
    change qSel ≤ CorePaid.Explicit.selQLimit (windowRouteRate aEff qOuter mOuter)
      (S07V27.selA (mOuter+1))*(r1+1) at hq
    apply hq.trans
    have hh : r1+1 ≤ (CorePaid.Explicit.forkQLimit κGeom+6+1)*(r+1) := by nlinarith only [hR1]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left _ hh
  have hRawPayment := withdrawal_raw_payment_le_uniform mOuter hκGeom hqOuter haEff
    1 (Fintype.card X) (Fintype.card X) W0.card Tports.card r r1 (univ\W0).card qSel
    hnPos (Finset.card_le_univ W0) hResourceLow hRootCount
    (Finset.card_le_univ _) hR1 hQsel
  have hCeil : (r : ℝ) ≤ ρcap*Fintype.card X+1 := by
    have hh := (Nat.ceil_lt_add_one (mul_nonneg hρStock.le hnParent.le)).le
    have hρn := mul_le_mul_of_nonneg_right hρStockCap hnParent.le
    exact hh.trans (by linarith only [hρn])
  have hResourceStat := hResourcePay (Fintype.card X) r hnResource hCeil
  have hWithdrawCost : (count (Dstock∪Ures) : ℝ) ≤ count Dstock+(βCount/3)*(Fintype.card X : ℝ)^2 := by
    have hActualCost : (count (Dstock∪Ures) : ℝ) ≤ count Dstock+
        withdrawalRawPayment κGeom aEff mOuter 1 (Fintype.card X) (Fintype.card X)
          W0.card Tports.card r1 (univ\W0).card qSel := by
      simpa only [ιId,map_configuration_refl,empty_union,withdrawalRawPayment,r1,Tports,Ures,add_assoc] using hResCount
    have hPay : withdrawalRawPayment κGeom aEff mOuter 1 (Fintype.card X) (Fintype.card X)
          W0.card Tports.card r1 (univ\W0).card qSel ≤ (βCount/4)*(Fintype.card X : ℝ)^2 := by
      have hh : withdrawalGeometryCost κGeom qOuter aEff mOuter*(r+1)*(Fintype.card X : ℝ)*
          (((1+182 : ℕ) : ℝ)^3) = cost*(r+1)*(Fintype.card X : ℝ) := by dsimp only [cost]; norm_num; ring
      rw [hh] at hRawPayment
      exact hRawPayment.trans hResourceStat
    have hs := sq_nonneg (Fintype.card X : ℝ)
    nlinarith only [hActualCost,hPay,mul_nonneg hβCount.le hs]
  have hDSize : (Dstock.card : ℝ) ≤ ρStock*(Fintype.card X : ℝ)^2 := by
    have hFamily := family_card_le_codegree_mul_edge_card Dstock (BasalIncidence.cover Dstock) 1
      (pairCodegreeBound_of_linear (packing_linear ⟨hDstock.1,hDstock.2.1⟩))
      (fun Q hQ => (hDstock.1 Q hQ).1) (fun Q hQ => hDstock.subset hQ)
    have hEdge := edge_card_le_real_degree_cap (BasalIncidence.cover Dstock) ρStock (fun v => (hDd v).le)
    have hF : (Dstock.card : ℝ) ≤ (BasalIncidence.cover Dstock).card := by simpa only [one_mul] using Nat.cast_le.mpr hFamily
    exact hF.trans hEdge
  have hκBound : κBank ≤ κGeomBank := bankRoundRate_le_geometric αp βb εcap δcap h Pbank hαp hβb hεcap hδcap
  have hW0pos : 0 < W0.card := Nat.cast_pos.mp (lt_of_lt_of_le (by positivity) hResourceLow)
  have hBankCubic := ambient_catalog_bank_outer_payment_le ιId W0 αp βb hαp h db cb Eb
    (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h)
    (Bstar*⌊κBank*(W0.card : ℝ)^2⌋₊) Bstar 64 κBank qOuter hκBank.le hW0pos
      (by rw [hW0]; exact hW0upper) le_rfl
  have hBankCount' : (count Bfull : ℝ) ≤ count (Dstock∪Ures)+(βCount/3)*(Fintype.card X : ℝ)^2 := by
    have hBankRate : bankCost*qOuter ≤ βCount/4 := by
      have hh := mul_le_mul_of_nonneg_left hqCap_le (show 0 ≤ 3*bankCost by positivity)
      nlinarith only [hh,hBankCountCap,mul_nonneg hBankCost hqOuter.le]
    have hκPay := mul_le_mul_of_nonneg_left hκBound
      (show 0 ≤ 2*Kbank*(65 : ℝ)^3*qOuter*(Fintype.card X : ℝ)^2 by positivity)
    have hCount : (count Bfull : ℝ) ≤ count (Dstock∪Ures)+
        (Bstar*⌊κBank*(W0.card : ℝ)^2⌋₊ : ℕ)*
          (Ambient.orderRatio ιId*catalogCellPotentialCost αp βb h db cb Eb
            (catalogDimension (αp/2) h) (catalogCoefficient (αp/2) h) (catalogColumn (αp/2) h) 66) := by
      simpa only [ιId,map_configuration_refl,empty_union,Nat.zero_add] using hBankCount
    have hBudget := mul_le_mul_of_nonneg_right hBankRate (sq_nonneg (Fintype.card X : ℝ))
    dsimp only [bankCost,Kbank] at hBudget hκPay
    nlinarith only [hCount,hBankCubic,hκPay,hBudget,mul_nonneg hβCount.le (sq_nonneg (Fintype.card X : ℝ))]
  have hBankSize' : (Bbank.card : ℝ) ≤ (δSize/2)*(Fintype.card X : ℝ)^2 := by
    have hSizeRate : 2*bankSize*qOuter ≤ δSize := by
      have hh := mul_le_mul_of_nonneg_left hqCap_le (show 0 ≤ 2*bankSize by positivity)
      nlinarith only [hh,hBankSizeCap,hδSize]
    have hQuad := quadratic_bank_size_payment qOuter bankSize δSize hqOuter.le
      (hqOuter32.trans (by norm_num)) hBankSize hSizeRate
    have hBankCardNat : Bbank.card ≤ 2*(Ecell*Bstar)*⌊κBank*(W0.card : ℝ)^2⌋₊ := by
      calc
        Bbank.card ≤ 2*(Ecell*Bstar*⌊κBank*(W0.card : ℝ)^2⌋₊) := hBankCard
        _ = _ := by ring
    have hCardReal : (Bbank.card : ℝ) ≤ 2*(Ecell*Bstar : ℕ)*κBank*(W0.card : ℝ)^2 := by
      have hc : (Bbank.card : ℝ) ≤ 2*(Ecell*Bstar : ℕ)*(⌊κBank*(W0.card : ℝ)^2⌋₊ : ℝ) := by
        exact_mod_cast hBankCardNat
      calc
        _ ≤ 2*(Ecell*Bstar : ℕ)*(⌊κBank*(W0.card : ℝ)^2⌋₊ : ℝ) := hc
        _ ≤ 2*(Ecell*Bstar : ℕ)*(κBank*(W0.card : ℝ)^2) :=
          mul_le_mul_of_nonneg_left (Nat.floor_le (mul_nonneg hκBank.le (sq_nonneg (W0.card : ℝ))))
            (show (0 : ℝ) ≤ 2*(Ecell*Bstar : ℕ) by positivity)
        _ = _ := by ring
    have hw : (W0.card : ℝ)^2 ≤ (2*qOuter*Fintype.card X)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by rw [hW0]; exact hW0upper) 2
    have hcp := mul_le_mul_of_nonneg_left hκBound (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (Ecell*Bstar))) (sq_nonneg (W0.card : ℝ)))
    have hwp := mul_le_mul_of_nonneg_left hw (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (Ecell*Bstar))) hκGeomBank)
    have hp := mul_le_mul_of_nonneg_right hQuad (sq_nonneg (Fintype.card X : ℝ))
    dsimp only [bankSize] at hp
    nlinarith only [hCardReal,hcp,hwp,hp]
  have hStockCount' : (count Dstock : ℝ) ≤ (βCount/3)*(Fintype.card X : ℝ)^2 := by
    nlinarith only [hStockCount,mul_nonneg hβCount.le (sq_nonneg (Fintype.card X : ℝ))]
  have hSizeRates : 64*ρStock+63*τSel ≤ δSize/2 := by nlinarith only [hρSel,hτSelSize,hδSize]
  obtain ⟨hCountPre,hSizePre⟩ := outer_resource_count_and_size_budget Dstock Ures Bbank βCount δSize
    ρStock τSel hStockCount' hWithdrawCost hBankCount' hDSize hResSize hBankSize' hSizeRates
  let Aψ := allowed (TypedTriangle.residual H (((((BasalIncidence.cover Dstock∪Rres)∪R)∪Bbank.biUnion triEdges)∪
    SampledResource.lift Wfull E0))) F
  let μfloor := floorWeights Aψ ψ (Fintype.card X : ℝ)
  have hFloor0 : ∀Q∈Aψ,0 ≤ μfloor Q := fun Q _ => floorWeights_nonneg Aψ ψ _ Q
  have hFloorUpper : ∀Q∈Aψ,μfloor Q ≤ (4*C)/Fintype.card X := by
    intro Q hQ
    have hQ' := isAllowed_of_mem_allowed hQ
    have hLow := fun T hT => (hψ.1 T (isAllowed_of_mem_allowed hT)).1
    have hf := (floorWeights_bounds Aψ ψ (by positivity : 0 < 2*C) hnParent hLow hQ).2
    have hs := (hψ.1 Q hQ').2
    exact hf.trans (hs.trans (div_le_div_of_nonneg_right (by linarith only [hC]) hnParent.le))
  have hTarget : target μfloor Aψ ≤ (4*C)^3*(Fintype.card X : ℝ)^2/4 := by
    have ht := floor_target_le_seed_order_square hψ (by positivity : 0 < 2*C) hnPos
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*C) (by linarith only [hC] : 2*C ≤ 4*C) 3
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg (Fintype.card X : ℝ))
    dsimp only [Aψ,μfloor]
    linarith only [ht,hh]
  have hMixed := mixed_statistics_total_le Aψ Bfull P0 μfloor (4*C)
    (((Fintype.card X : ℝ)^2)^(-egj13Epsilon)) 66 (by positivity) (Real.rpow_nonneg (by positivity) _)
    hnPos hPreCG' hPreThree' hFloor0 hFloorUpper hTarget
    (by simpa only [Aψ,μfloor,ιId,map_configuration_refl,empty_union,Nat.zero_add] using hStats.mixed)
  have hNoiseCap : ((Fintype.card X : ℝ)^2)^(-egj13Epsilon) ≤ εMixed :=
    (hNoise (Fintype.card X) hnNoise).2.2.2.2.2.1
  have hFinalCount : (count Rnext : ℝ) ≤ count P0+(τPasch/2)*(Fintype.card X : ℝ)^2 :=
    outer_final_universe_count_budget P0 Bfull Rnext (4*C) τPasch
      (((Fintype.card X : ℝ)^2)^(-egj13Epsilon)) u 66 (by positivity) hτPasch hCountPre hSizePre
      hNoiseCap hMixed (by simpa only [union_comm] using hNextCount')
      (by have he : u*(68 : ℝ)^3=τPasch/4 := by dsimp only [u]; ring
          exact he.le)
  have hChildOrder : max 1 (max (schedule.nPaid j) schedule.nGeometry) ≤ Wfull.card := by
    apply max_le
    · rw [hFullCard]
      exact le_trans (by omega : 1 ≤ M) chain.head.lower
    · have hg : max (schedule.nPaid j) schedule.nGeometry ≤ nGeometry := by
        exact Finset.le_sup (f := fun k : Fin (L+1) =>
          max (schedule.nPaid k) schedule.nGeometry) (mem_univ j)
      have hnG : ⌈2*nGeometry/qOuter⌉₊ ≤ Fintype.card X := by dsimp only [nRoot] at hn; omega
      have hc := (Nat.le_ceil (2*nGeometry/qOuter)).trans (Nat.cast_le.mpr hnG)
      have hp := (div_le_iff₀ hqOuter).mp hc
      have hnGeomReal : (nGeometry : ℝ) ≤ Wfull.card := by
        nlinarith only [hp,hFullLow]
      have hnGeomNat : nGeometry ≤ Wfull.card := by exact_mod_cast hnGeomReal
      exact hg.trans hnGeomNat
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
        TypedTriangle.degIn,SparseEdge.degIn] using hHoles v)
  trace "OUTER count/mixed budget ready"
  have hChildResult := structured_reference_reserved_actual_child chain (α₀/8) (β j) (schedule.K j) (schedule.ηSpec j)
      C (schedule.ζRef j) ξ ζState (schedule.Nbase j) (schedule.Ns j) (schedule.nPaid j) schedule.nGeometry
      hC (schedule.ζRef_pos j (Nat.le_of_lt_succ j.isLt)).le (schedule.ref_spec j (Nat.le_of_lt_succ j.isLt))
      hξ (schedule.ref_state j (Nat.le_of_lt_succ j.isLt))
      (schedule.paid_cap j (Nat.le_of_lt_succ j.isLt)) (schedule.paid_smooth j (Nat.le_of_lt_succ j.isLt))
      H ι (fun _ _ => Iff.rfl) (fun _ => rfl) W0 sdiff_subset μwindow E0 D0 Ytot R Dpaid Rnext
      hChildOrder hPrepared hFull3 hFullClean hWeightsWindow hRaw.2 hE0 hYtot hLam hYCore hErefY hRefHolesClass
      (schedule.ref_clean j (Nat.le_of_lt_succ j.isLt)) hInverseBudget hFutureE0Class hR hReserved hDpaid hPaidNext'
  rw [show (α₀/8)/2=α₀/16 by ring] at hChildResult
  obtain ⟨state,Pouter,hBasal,hOuterDis,hRDis,hPart,hDPaid,hDPaidU,hOuterEq,hChildEq⟩ := hChildResult
  trace "OUTER actual reserved child extracted"
  refine ⟨P0,⟨hP0,hStats.complement_degree,hStats.triangles,hStats.pasch⟩,state,Pouter,Dpaid,Rnext,
    hDPaid,hP0Paid,hPaidNext',hNextCG',hNextThree',?_,hFinalCount,hOuterDis,hRDis,?_⟩
  · rw [←hFullCard]
    exact hFullUp.le
  · simpa only [union_assoc] using hPart

#print axioms concrete_outer_paid_layer_with_triangle_monitors_and_pasch

end TypedTriangle.Pasch
