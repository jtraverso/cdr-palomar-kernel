module
public import RequestProject.TypedTriangle.ExplicitConcreteLayerParameters
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorStructuredLayer
public import RequestProject.TypedTriangle.TriangleMonitorConcreteOuterLayer
public import RequestProject.TypedTriangle.ExplicitScheduledRawProfileBudget
public import RequestProject.TypedTriangle.VortexConcreteInnerLayers
public import RequestProject.TypedTriangle.VortexConcreteOuterLayer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open IntrinsicRawPathsPreparedVortex CatalogNative CorePaid BasalIncidence
def monitorOuterLayerOrder (α C qOuter aOuter ζStat : ℝ) (h m L qStat : ℕ)
    (γRef : ℕ → ℝ) (nRef nPaid : ℕ → ℕ) (nGeometry : ℕ) : ℕ :=
  let nRun : Fin (L+1) → ℕ := fun j =>
    monitorCleanLayerThreshold (α/16) C (α/32) (γRef j) qOuter (α/4)
      (windowRouteRate (aOuter/2) qOuter m/4) ζStat h (m+1)
      (nRef j) (nPaid j) nGeometry qStat
  max 1 (max (univ.sup nRun) ⌈2/qOuter⌉₊)

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

private theorem diffuse_seed_double {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I)) (C : ℝ) (μ : Finset X → ℝ)
    (hC : 0 < C) (hn : 0 < Fintype.card X) (hSeed : IsDiffuseSeed H F C μ) :
    IsDiffuseSeed H F (2*C) μ := by
  refine ⟨?_,hSeed.2⟩
  intro Q hQ
  have hnR : (0:ℝ) < Fintype.card X := by exact_mod_cast hn
  have hCn : 0 < C*Fintype.card X := mul_pos hC hnR
  have hLower : 1/((2*C)*Fintype.card X) ≤ 1/(C*Fintype.card X) :=
    one_div_le_one_div_of_le hCn (by nlinarith only [hCn])
  exact ⟨hLower.trans (hSeed.1 Q hQ).1,
    (hSeed.1 Q hQ).2.trans (div_le_div_of_nonneg_right (by linarith : C ≤ 2*C) hnR.le)⟩

theorem concrete_outer_paid_layer_with_triangle_monitors_explicit {I : Type} (F : Set (Multiset I))
    (α₀ C ζStat : ℝ) (h d T mOuter qStat : ℕ) (aOuter : ℝ)
    (hα : 0 < α₀) (hC : 1 ≤ C) (hh : 6 ≤ h)
    (hm : 0 < mOuter) (ha : 0 < aOuter) (hOdd : Odd (mOuter+1)) (hLen : 3 ≤ mOuter+1) (hζStat : 0 < ζStat) :
    let εOuter := monitorComplementBudget (2*C) (α₀/16) h ζStat
    let γStock := resourceStockBudget (α₀/16) (2*C)
    let ηBank := CatalogNative.Explicit.bankProtectionBudget (α₀/16) (α₀/32) h
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
      let MrawBudget := max 1 (scheduledProfileOrder C schedule.K schedule.εRef
        (d+(d+1)*Nat.log 2 T))
      ∀ qOuter : ℝ, 0 < qOuter → qOuter ≤ 1/32 → 4*qOuter ≤ εOuter →
      let θT := outerLayerTerminalBudget α₀ C qOuter aOuter h mOuter
        (d+(d+1)*Nat.log 2 T) schedule.γRef
      let nRoot := monitorOuterLayerOrder α₀ C qOuter aOuter ζStat h mOuter
        (d+(d+1)*Nat.log 2 T) qStat schedule.γRef schedule.nRef schedule.nPaid schedule.nGeometry
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
      ∃ P₀ : Finset (Finset X), OriginalTriangleMonitorData H F μ w (2*ζStat) (2*ζStat) P₀ ∧
      ∃ state : ActualState chain (2*C) (α₀/16) ζState,
      ∃ P : Finset (Sym2 X), Basal H F P ∧
        P₀.biUnion triEdges ⊆ P ∧ Basal H F (P\P₀.biUnion triEdges) ∧
        Disjoint P (R ∪ embeddedEdges (outerPreparedEmbedding node.trim W chain.head.trim) (edges state.host)) ∧
        Disjoint R (embeddedEdges (outerPreparedEmbedding node.trim W chain.head.trim) (edges state.host)) ∧
        edges H = (P ∪ R) ∪ embeddedEdges (outerPreparedEmbedding node.trim W chain.head.trim) (edges state.host) := by
  intro earlyOuter earlyStock earlyBank
  let εOuter := monitorComplementBudget (2*C) (α₀/16) h ζStat
  let γStock := resourceStockBudget (α₀/16) (2*C)
  let ηBank := CatalogNative.Explicit.bankProtectionBudget (α₀/16) (α₀/32) h
  have hηBank : 0 < ηBank := CatalogNative.Explicit.bankProtectionBudget_pos h (by positivity) (by positivity)
  have hγStock : 0 < γStock :=
    (resource_parameters_pos (α₀/16) (2*C) h 1 1 1 1 0 1 1 (by positivity)
      (by linarith only [hC]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).1
  intro ρFuture qInner ζState Btotal hρ hq hq32 hqρ hqBank hqStock hqα hqPath hζ
    hB0 hB8 hBα hBPath β Ninner hβ hTotal schedule
  let L := d+(d+1)*Nat.log 2 T
  let E := max 1 (2*C)
  let aEff := aOuter/2
  have haEff : 0 < aEff := by dsimp [aEff]; positivity
  have hCpos : 0 < C := by linarith only [hC]
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
  intro rawBudgetTarget
  intro qOuter hqOuter hqOuter32 hqOuterBank
  let θRun : Fin (L+1) → ℝ := fun j => layerTerminalBudget (α₀/16) (2*C) (α₀/32)
    (schedule.γRef j) qOuter (α₀/4) (windowRouteRate aEff qOuter mOuter/4) h (mOuter+1)
  let nRun : Fin (L+1) → ℕ := fun j => monitorCleanLayerThreshold (α₀/16) C (α₀/32)
    (schedule.γRef j) qOuter (α₀/4) (windowRouteRate aEff qOuter mOuter/4) ζStat h (mOuter+1)
    (schedule.nRef j) (schedule.nPaid j) schedule.nGeometry qStat
  have hNonempty : (univ : Finset (Fin (L+1))).Nonempty := ⟨0,mem_univ _⟩
  let θT := univ.inf' hNonempty θRun
  have hθT : 0 < θT := (lt_inf'_iff hNonempty).mpr (by
    intro j _
    exact layerTerminalBudget_pos (α₀/16) (2*C) (α₀/32) (schedule.γRef j)
      qOuter (α₀/4) (windowRouteRate aEff qOuter mOuter/4) h (mOuter+1)
      (by positivity) (by linarith only [hC]) (by positivity)
      (schedule.γRef_pos j (Nat.le_of_lt_succ j.isLt)) hqOuter (by positivity)
      (div_pos (windowRouteRate_pos mOuter haEff hqOuter) (by norm_num)))
  let nRoot := max 1 (max ((univ : Finset (Fin (L+1))).sup nRun) ⌈2/qOuter⌉₊)
  intro θTarget nTarget
  intro X _ H μ hn hSeed hPhysical h3Orig hCleanOrig Nouter Mouter M mInner aInner εRouteInner t hM node
  letI : DecidableEq (Survivors node.trim) := Classical.decEq _
  intro W
  letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
  intro hWlo hWhi hPoolsOrig hPathsOrig chain hMetadata R DR dR hR hRDec hRAvoid hRd hRcap ν _ w hν hw
  change nRoot ≤ Fintype.card X at hn
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
  have hnRoot : 1 ≤ nRoot := le_max_left _ _
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
      exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hn
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
  have hnLocal : nRun j ≤ Fintype.card X :=
    (Finset.le_sup (mem_univ j)).trans (((le_max_left _ _).trans (le_max_right _ _)).trans hn)
  have hθj : θT ≤ θRun j := inf'_le _ (mem_univ j)
  have hRLocal : (dR:ℝ) ≤ θRun j*Fintype.card X :=
    hRcap.trans (mul_le_mul_of_nonneg_right hθj hnParent.le)
  have layerNumeric :=
    structured_clean_paid_layer_state_with_triangle_monitors_explicit (V:=X) F (α₀/16) C (α₀/32) (α₀/8) ζStat h qStat
      (by positivity) hC (by positivity) (by linarith only [hα]) hh hζStat (β j) (schedule.K j) (schedule.ηSpec j) (3/(4*C)) (2*C) ρFuture
      (schedule.ζRef j) (schedule.εRef j) (schedule.γRef j) (schedule.nRef j)
      (schedule.Nbase j) (schedule.Ns j) (schedule.nPaid j) schedule.nGeometry
      (schedule.γRef_pos j (Nat.le_of_lt_succ j.isLt)) le_rfl
      (by nlinarith only [hC]) (schedule.ζRef_pos j (Nat.le_of_lt_succ j.isLt)).le
      (schedule.ref_spec j (Nat.le_of_lt_succ j.isLt))
      (schedule.ref_clean j (Nat.le_of_lt_succ j.isLt))
      (schedule.paid_cap j (Nat.le_of_lt_succ j.isLt))
      (schedule.paid_smooth j (Nat.le_of_lt_succ j.isLt))
      (schedule.reference j (Nat.le_of_lt_succ j.isLt))
      qOuter hqOuter hqOuterBank (α₀/4) (windowRouteRate aEff qOuter mOuter/4) (mOuter+1)
      (by positivity) (by exact div_pos (windowRouteRate_pos mOuter haEff hqOuter) (by norm_num)) hOdd hLen
  trace "layer numeric specialized"
  have layerData := layerNumeric
      H μ Wfull Ares U R DR dR U.card μwindow ξ
  trace "layer data specialized"
  have layerBase := layerData hnLocal
      (diffuse_seed_double H F C μ hCpos hnPos hSeed) hPhysical
      (commonNbrCond_mono h3Orig (by linarith only [hα])) (hCleanOrig.mono (by linarith only [hα])).hingeCond
  trace "layer base specialized"
  have layerGeometry := layerBase
      hFullLow hFullUp (by convert hResourceLow using 1 <;> ring)
      hPoolEnough hActualRoute hBankGeometry.1 hBankGeometry.2 hPrepared hFull3 hFullClean
  trace "layer geometry specialized"
  have layerWeights := layerGeometry
      (by simpa only [JW,Wfull,embeddingWindowHost,Fintype.card_coe] using hWeights) hξ hRefError hRaw.2 hInverseBudget
  trace "layer weights specialized"
  obtain ⟨P₀,E₀,D₀,Ytot,hData,hDec,hFuture,ψ,hPaidSeed,hClose,hPaidPhysical,h3Child,hCleanChild,
    hEkeep,hChildHoles,hFutureGraph,hChildAmbient,hOuter,hP₀E,hRest,hTerminal⟩ :=
    layerWeights
      hFutureρ (by simpa only [Uambient] using hDisjoint)
      hSdegree hFutureStock hFutureBank hRDec hRS hRd hRLocal ν w hν hw
  let Jchild := subHost JW (E₀ ∪ SampledResource.pull Wfull Ytot)
  have hNextChild : chain.nextPreparedEdges.image (Sym2.map e) ⊆ edges Jchild := by
    apply nextPreparedEdges_mapped_subset_child chain e JW Jchild hWindowAdj
    intro f hf
    have he := hEkeep (hFuture hf)
    simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using he
  have hUniformHoles : ∀v, (SparseEdge.degIn (edges JW \ edges Jchild) v:ℝ) ≤
      ζState*Fintype.card {x // x ∈ Wfull} := by
    intro v
    have hp := hChildHoles v
    have hs := mul_le_mul_of_nonneg_right (schedule.ref_state j (Nat.le_of_lt_succ j.isLt))
      (Nat.cast_nonneg Wfull.card)
    simpa only [Jchild,JW,Wfull,embeddingWindowHost,Fintype.card_coe] using hp.trans hs
  have hαChild : (α₀/8)/2 = α₀/16 := by ring
  refine ⟨P₀,hData,?_⟩
  apply raw_paths_reserved_actual_child_retaining_initial_packing chain H ι (2*C) (α₀/16) ζState
    R hR (fun _ _ => Iff.rfl) (fun _ => rfl) Jchild ψ P₀
  · exact subHost_le JW _
  · rfl
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hPaidSeed
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hPaidPhysical
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union,hαChild] using h3Child
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union,hαChild] using hCleanChild
  · exact hUniformHoles
  · exact hNextChild
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hOuter
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hP₀E
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hRest
  · simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hTerminal

#print axioms concrete_outer_paid_layer_with_triangle_monitors_explicit
end TypedTriangle.Vortex.Explicit
