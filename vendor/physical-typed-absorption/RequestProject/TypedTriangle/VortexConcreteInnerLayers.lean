/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexConcreteInnerLayerParameters
public import RequestProject.TypedTriangle.VortexStructuredCleanPaidLayerState
public import RequestProject.TypedTriangle.VortexRawPathsActualChild
public import RequestProject.TypedTriangle.VortexRawPathsPreparedWindowData
public import RequestProject.TypedTriangle.VortexRawPathsFutureProtection
public import RequestProject.TypedTriangle.VortexRawPathsWindowSizeData
public import RequestProject.TypedTriangle.VortexWindowResourceCoreGeometry
public import RequestProject.TypedTriangle.VortexActualWindowTransport
public import RequestProject.TypedTriangle.VortexRelativeWindowBudget
public import RequestProject.TypedTriangle.VortexScheduledRawProfileBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open IntrinsicRawPathsPreparedVortex CatalogNative CorePaid BasalIncidence

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

/-- Effective inner paid layers on every node of the same raw vortex. The
bank constants precede the reference density and all sampled rates; the
finite agenda precedes the common terminal-order threshold. -/
theorem concrete_inner_local_layers {I : Type} (F : Set (Multiset I))
    (α₀ C : ℝ) (h d T m : ℕ) (a : ℝ)
    (hα : 0 < α₀) (hC : 1 ≤ C) (hh : 6 ≤ h)
    (hm : 0 < m) (ha : 0 < a) (hOdd : Odd (m+1)) (hLen : 3 ≤ m+1) :
    ∃ εOuter γStock ηBank : ℝ, 0 < εOuter ∧ 0 < γStock ∧ 0 < ηBank ∧
      ∀ ρFuture q ζState Btotal : ℝ,
        0 < ρFuture → 0 < q → q ≤ 1/32 → 4*q ≤ εOuter →
        2*q ≤ ρFuture → q ≤ ηBank/16 → q ≤ γStock/8 →
        q ≤ α₀/(64*(2:ℝ)^h.choose 2) → q*m*(2:ℝ)^m ≤ a/64 →
        0 < ζState → ζState ≤ windowRouteRate a q m/4 → ζState ≤ α₀*q/128 →
        0 ≤ Btotal → Btotal ≤ 1/8 → Btotal ≤ α₀/128 →
        Btotal*m*(2:ℝ)^m ≤ a/64 →
      ∀ (β : ℕ → ℝ) (N : ℕ), (∀ j, 0 ≤ β j) →
        (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1),β j) ≤ Btotal →
      ∀ schedule : ConcreteInnerLayerSchedule F (α₀/8) C ρFuture ζState β h N
          (d+(d+1)*Nat.log 2 T),
      ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ {X : Type} [Fintype X] {H : Host X I} {μ : Finset X → ℝ}
        {εRoute t : ℝ}
        (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ),
        chain.HasRelativeWindows → LocalLayers chain (2*C) (α₀/16) ζState := by
  obtain ⟨εOuter,γStock,ηBank,hεOuter,hγStock,hηBank,hBank⟩ :=
    structured_clean_paid_layer_state F (α₀/16) C (α₀/32) (α₀/8) h
      (by positivity) hC (by positivity) (by linarith) hh
  refine ⟨εOuter,γStock,ηBank,hεOuter,hγStock,hηBank,?_⟩
  intro ρFuture q ζState Btotal hρ hq hq32 hqOuter hqρ hqBank hqStock hqα hqPath
    hζ hζRoute hζPool hB0 hB8 hBα hBPath β N hβ hTotal schedule
  let L := d+(d+1)*Nat.log 2 T
  let E := max 1 (2*C)
  have hCpos : 0 < C := by linarith
  have hEb : E ≤ 2*C := by dsimp [E]; exact max_le (by linarith) le_rfl
  have hAgenda : ∀r ≤ L,
      schedule.K r*(2*(2*C)*(∑ j ∈ range r,β j)) ≤ 1/(16*C) ∧
      2*(2*C)*(∑ j ∈ range r,β j) ≤ schedule.εRef r/8 := by
    intro r hr
    simpa only [show 2*(2*C)=4*C by ring] using
      And.intro (schedule.prefix_inverse r hr) (schedule.prefix_reference r hr)
  obtain ⟨nBudget,hnBudget,hBudget⟩ := exists_scheduled_raw_profile_budget C E (2*C)
    β schedule.K schedule.εRef L hC (by dsimp [E]; positivity) hEb hβ
    schedule.K_pos schedule.εRef_pos hAgenda
  let localChoice := fun j : Fin (L+1) =>
    hBank (β j) (schedule.K j) (schedule.ηSpec j) (3/(4*C)) (2*C) ρFuture
      (schedule.ζRef j) (schedule.εRef j) (schedule.γRef j) (schedule.nRef j)
      (schedule.Nbase j) (schedule.Ns j) (schedule.nPaid j) schedule.nGeometry
      (schedule.γRef_pos j (Nat.le_of_lt_succ j.isLt)) le_rfl
      (by nlinarith) (schedule.ζRef_pos j (Nat.le_of_lt_succ j.isLt)).le
      (schedule.ref_spec j (Nat.le_of_lt_succ j.isLt))
      (schedule.ref_clean j (Nat.le_of_lt_succ j.isLt))
      (schedule.paid_cap j (Nat.le_of_lt_succ j.isLt))
      (schedule.paid_smooth j (Nat.le_of_lt_succ j.isLt))
      (schedule.reference j (Nat.le_of_lt_succ j.isLt))
      q hq hqOuter (α₀/4) (windowRouteRate a q m/4) (m+1)
      (by positivity) (by exact div_pos (windowRouteRate_pos m ha hq) (by norm_num)) hOdd hLen
  let nRun : Fin (L+1) → ℕ := fun j => Classical.choose (Classical.choose_spec (localChoice j))
  let nAll := (univ : Finset (Fin (L+1))).sup nRun
  let M₀ := max 1 (max nAll (max nBudget ⌈2/q⌉₊))
  refine ⟨M₀,le_max_left _ _,?_⟩
  intro M hM X _ H μ εRoute t chain
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hM
  have hMBudget : nBudget ≤ M :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hM
  have hMRun : ∀j, nRun j ≤ M := by
    intro j
    exact (Finset.le_sup (mem_univ j)).trans
      (((le_max_left _ _).trans (le_max_right _ _)).trans hM)
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
    intro state
    let j : Fin (L+1) := ⟨tail.head.index,by
      exact Nat.lt_succ_of_le tail.head.index_le⟩
    have hLocal := (Classical.choose_spec (Classical.choose_spec (localChoice j))).2
      (V := Survivors node.trim)
    let Hactual : Host (Survivors node.trim) I := state.host
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
      Btotal q ρFuture ηBank γStock hnParent hq hq32 hB0 hB8 hSizes.1 hSizes.2
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
        exact ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hM
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
    have hnLocal : nRun j ≤ Fintype.card (Survivors node.trim) :=
      (hMRun j).trans node.lower
    have hθ := (Classical.choose_spec (Classical.choose_spec (localChoice j))).1
    obtain ⟨E₀,D₀,Ytot,hDec,hFuture,ψ,hSeed,hClose,hPhysical,h3Child,hCleanChild,
      hEkeep,hChildHoles,hFutureGraph,hChildAmbient,hOuter,hTerminal⟩ :=
      hLocal Hactual state.seed Wfull Ares U ∅ ∅ 0 U.card μwindow ξ hnLocal
        state.diffuse state.physical state.common state.clean.hingeCond
        hNumbers.1 hNumbers.2.1 (by convert hNumbers.2.2.1 using 1 <;> ring)
        hPoolEnough hActualRoute hBankGeometry.1 hBankGeometry.2 hPrepared hFull3 hFullClean
        (by simpa only [Fintype.card_coe,JW,Wfull,embeddingWindowHost] using hWeights) hξ hRefError hRaw.2 hInverseBudget
        hNumbers.2.2.2.2.1 (by simpa only [Uambient] using hDisjoint)
        hSdegree hNumbers.2.2.2.2.2.2 hNumbers.2.2.2.2.2.1
        (by refine ⟨?_,?_,?_⟩ <;> simp) (by simp)
        (by intro v; simp [TypedTriangle.degIn])
        (by simpa only [Nat.cast_zero] using
          mul_nonneg hθ.le (Nat.cast_nonneg (Fintype.card (Survivors node.trim))))
    let Jchild := subHost JW (E₀ ∪ SampledResource.pull Wfull Ytot)
    have hNextChild : tail.nextPreparedEdges.image (Sym2.map e) ⊆ edges Jchild := by
      apply nextPreparedEdges_mapped_subset_child tail e JW Jchild hWindow.1
      intro f hf
      have he := hEkeep (hFuture hf)
      simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using he
    have hUniformHoles : ∀v,
        (SparseEdge.degIn (edges JW \ edges Jchild) v : ℝ) ≤
          ζState*Fintype.card {x // x ∈ Wfull} := by
      intro v
      have hp := hChildHoles v
      have hScale := mul_le_mul_of_nonneg_right
        (schedule.ref_state j (Nat.le_of_lt_succ j.isLt)) (Nat.cast_nonneg Wfull.card)
      simpa only [Fintype.card_coe,Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union]
        using hp.trans hScale
    have hαChild : (α₀/8)/2 = α₀/16 := by ring
    obtain ⟨child,P,hP,hDP,hPartition⟩ :=
      raw_paths_actual_child_of_window_paid_child Hraw Hactual W _ tail
        (2*C) (α₀/16) ζState hGraph hLabels hProtected' Jchild ψ
        (subHost_le JW _) rfl
        (by simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hSeed)
        (by simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hPhysical)
        (by simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union,hαChild] using h3Child)
        (by simpa only [Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union,hαChild] using hCleanChild)
        hUniformHoles hNextChild
        (by simpa only [empty_union,Jchild,JW,Wfull,embeddingWindowHost,subHost,Finset.coe_union] using hOuter)
    have hCanonEdges : embeddedEdges ι (edges child.host) =
        embeddedEdges ι (@edges _ _ canonicalFintype.down child.host) :=
      embedded_edges_change_fintype ι child.host _ canonicalFintype.down
    refine ⟨child,P,hP,?_,?_⟩
    · change Disjoint P (embeddedEdges ι (@edges _ _ canonicalFintype.down child.host))
      rw [← hCanonEdges]
      exact hDP
    · change edges Hactual = P ∪ embeddedEdges ι (@edges _ _ canonicalFintype.down child.host)
      rw [← hCanonEdges]
      exact hPartition

#print axioms concrete_inner_local_layers
end TypedTriangle.Vortex
