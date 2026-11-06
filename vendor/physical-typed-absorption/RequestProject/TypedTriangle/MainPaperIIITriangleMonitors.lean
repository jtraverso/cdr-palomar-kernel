/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexConcreteInnerLayers
public import RequestProject.TypedTriangle.TriangleMonitorConcreteOuterLayer
public import RequestProject.TypedTriangle.VortexOuterInnerRawPreparedVortex
public import RequestProject.TypedTriangle.VortexPrescribedRawPathsAmbientAssembly
public import RequestProject.TypedTriangle.TriangleMonitorCompletionCount
public import RequestProject.TypedTriangle.VortexUniformTerminalReserve
public import RequestProject.TypedTriangle.VortexGlobalAssemblyParameters
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open IntrinsicRawPathsPreparedVortex CorePaid

private theorem embedded_disjoint {X Y : Type} (ι : X ↪ Y)
    {E E' : Finset (Sym2 X)} (hDis : Disjoint E E') :
    Disjoint (embeddedEdges ι E) (embeddedEdges ι E') := by
  apply disjoint_left.mpr
  intro f hf hf'
  obtain ⟨e,he,hef⟩ := mem_image.mp hf
  obtain ⟨e',he',hef'⟩ := mem_image.mp hf'
  have hEq : e = e' := Sym2.map.injective ι.injective (hef.trans hef'.symm)
  exact disjoint_left.mp hDis he (hEq ▸ he')

/-- The original H1--H4 imply an allowed triangle decomposition. Every
sampling, preparation, local bank and terminal absorber is constructed
inside the proof, with its constants chosen before the host. -/
theorem main_theorem_T_with_triangle_monitors {I : Type} (F : Set (Multiset I))
    (αOriginal C η : ℝ) (hOriginal qStat : ℕ)
    (hαOriginal : 0 < αOriginal) (hC : 1 ≤ C) (hhOriginal : 6 ≤ hOriginal) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {X : Type} [Fintype X] (H : Host X I) (μ : Finset X → ℝ),
      n₀ ≤ Fintype.card X →
      IsDiffuseSeed H F C μ →
      IsPhysical H F (edges H) → CommonNbrCond H F αOriginal →
      HingeCond H F αOriginal hOriginal →
      ∀ (ν : Type) [Fintype ν] (w : ν → Finset X → ℝ),
      (Fintype.card ν:ℝ) ≤ (Fintype.card X:ℝ)^qStat →
      (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
      ∃ D : Finset (Finset X), IsDecomposition H F (edges H) D ∧
        ∀ k, |(∑ Q ∈ D, w k Q)-(∑ Q ∈ allowed H F, μ Q*w k Q)| ≤ η*(Fintype.card X:ℝ)^2 := by
  let ζStat := η/4
  have hζStat : 0 < ζStat := by dsimp [ζStat]; positivity
  let α := min αOriginal (S07V49.hingeConstB αOriginal 1 hOriginal)/8
  let h := 2*hOriginal-3
  have hHinge : 0 < S07V49.hingeConstB αOriginal 1 hOriginal :=
    S07V49.hingeConstB_pos hαOriginal (by norm_num) (by omega)
  have hα : 0 < α := by dsimp [α]; positivity
  have hh : 6 ≤ h := by dsimp [h]; omega
  have hCpos : 0 < C := by linarith
  obtain ⟨nClean,hMakeClean⟩ := clean_hinge_of_H3H4 αOriginal hOriginal hαOriginal hhOriginal
  obtain ⟨ε,hε,d,T,mInner,aInner,mOuter,aOuter,δOuter,hT,hKernel,hmInner,haInner,
    hOddInner,hLenInner,hmOuter,haOuter,hδOuter,hOddOuter,hLenOuter,hRawByQ⟩ :=
      exists_outer_inner_raw_prepared_vortex F α C h hα (by omega) hCpos
  obtain ⟨εInner,γInner,ηInner,hεInner,hγInner,hηInner,hInner⟩ :=
    concrete_inner_local_layers F α C h d T mInner aInner hα hC hh
      hmInner haInner hOddInner hLenInner
  obtain ⟨εOuter,γOuter,ηOuter,hεOuter,hγOuter,hηOuter,hOuter⟩ :=
    concrete_outer_paid_layer_with_triangle_monitors F α C ζStat h d T mOuter qStat aOuter hα hC hh
      hmOuter haOuter hOddOuter hLenOuter hζStat
  let L := d+(d+1)*Nat.log 2 T
  obtain ⟨ρ,qInner,ζ,B,β,Ninner,hρ,hqInner,hqInner32,hqBank,hqρ,hqη,hqStock,hqα,
    hqInnerPaths,hqOuterPaths,hζ,hζRoute,hζPool,hB,hB8,hBα,hBInnerPaths,hBOuterPaths,
    hBPreparation,hβ,hβCap,hTotal,hSchedule⟩ :=
      exists_global_assembly_parameters F α C ε δOuter (min εInner εOuter)
        (min γInner γOuter) (min ηInner ηOuter) aInner aOuter h L mInner mOuter
        hα hC hh hε hδOuter (lt_min hεInner hεOuter) (lt_min hγInner hγOuter)
        (lt_min hηInner hηOuter) haInner haOuter hmInner hmOuter
  obtain ⟨schedule⟩ := hSchedule
  have hqηInner : qInner ≤ ηInner/16 := hqη.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hqηOuter : qInner ≤ ηOuter/16 := hqη.trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hqγInner : qInner ≤ γInner/8 := hqStock.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hqγOuter : qInner ≤ γOuter/8 := hqStock.trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  obtain ⟨Minner,hMinner,hMakeLayers⟩ := hInner ρ qInner ζ B hρ hqInner hqInner32
    (hqBank.trans (min_le_left _ _)) hqρ hqηInner hqγInner hqα hqInnerPaths
    hζ hζRoute hζPool hB.le hB8 hBα hBInnerPaths β Ninner hβ hTotal schedule
  have hqOuterPaths' : qInner*mOuter*(2:ℝ)^mOuter ≤ (aOuter/2)/64 := by
    convert hqOuterPaths using 1 <;> ring
  have hBOuterPaths' : B*mOuter*(2:ℝ)^mOuter ≤ (aOuter/2)/64 := by
    convert hBOuterPaths using 1 <;> ring
  obtain ⟨Mouter,hMouter,hMakeOuterByQ⟩ := hOuter ρ qInner ζ B hρ hqInner hqInner32
    hqρ hqηOuter hqγOuter hqα hqOuterPaths' hζ hB.le hB8 hBα hBOuterPaths'
    β Ninner hβ hTotal schedule
  obtain ⟨εRouteInner,hεRouteInner,hRawByBeta⟩ := hRawByQ qInner hqInner hqInner32
  have hPreparation := hTotal.trans hBPreparation
  obtain ⟨M,nInner,hMrequired,hM,t,ht,hRawByOuterQ⟩ :=
    hRawByBeta β hβ hPreparation Ninner (max Minner Mouter)
  let tNat := ⌈t⌉₊
  obtain ⟨qReserve,hqReserve,hqReserve32,K,Nreserve,nAbs,hReserve⟩ :=
    uniform_terminal_absorber_avoiding_outer_core (α/8) h tNat L
      (fun r : Fin (L+1) => β r) (by positivity)
      (fun r => (hβCap r (Nat.le_of_lt_succ r.isLt)).1)
  let qOuter := min qReserve (εOuter/4)
  have hqOuter : 0 < qOuter := lt_min hqReserve (by positivity)
  have hqOuter32 : qOuter ≤ 1/32 := (min_le_left _ _).trans hqReserve32
  have hqOuterBank : 4*qOuter ≤ εOuter := by
    have hs : qOuter ≤ εOuter/4 := min_le_right _ _
    linarith
  obtain ⟨θT,nOuter,hθT,hMakeOuter⟩ := hMakeOuterByQ qOuter hqOuter hqOuter32 hqOuterBank
  obtain ⟨εRouteOuter,hεRouteOuter,hRawByN⟩ := hRawByOuterQ qOuter hqOuter hqOuter32
  let Nouter := max Nreserve nAbs
  obtain ⟨nRaw,hMakeRaw⟩ := hRawByN Nouter
  let n₀ := max nClean (max nRaw (max nOuter ⌈(K:ℝ)/θT⌉₊))
  refine ⟨n₀,?_⟩
  intro X _ H μ hn hSeed hH2 hH3 hH4 ν _ w hν hw
  have hnClean : nClean ≤ Fintype.card X := by dsimp [n₀] at hn; omega
  have hnRaw : nRaw ≤ Fintype.card X := by dsimp [n₀] at hn; omega
  have hnOuter : nOuter ≤ Fintype.card X := by dsimp [n₀] at hn; omega
  have hnReserve : ⌈(K:ℝ)/θT⌉₊ ≤ Fintype.card X := by dsimp [n₀] at hn; omega
  have hOriginalDensity : 8*α ≤ αOriginal := by
    dsimp [α]
    linarith [min_le_left αOriginal (S07V49.hingeConstB αOriginal 1 hOriginal)]
  have hHingeDensity : 8*α ≤ S07V49.hingeConstB αOriginal 1 hOriginal := by
    dsimp [α]
    linarith [min_le_right αOriginal (S07V49.hingeConstB αOriginal 1 hOriginal)]
  have h3 : CommonNbrCond H F (8*α) := commonNbrCond_mono hH3 hOriginalDensity
  have hClean : CleanHingeCond H F (8*α) h :=
    (hMakeClean H F hnClean hH3 hH4).mono hHingeDensity
  obtain ⟨node,hNode⟩ := hMakeRaw H hnRaw h3 hClean μ hSeed
  letI : DecidableEq (Survivors node.trim) := Classical.decEq _
  obtain ⟨W,hWmin,hShrink,hWlo,hWhi,hWrelativeLo,hWrelativeHi,hNext,hPools,hPaths,hRoutes,
    chain,hMetadata⟩ := hNode
  let HAbs := restrictedHost H node.trim
  let ιOut := survivingVertexEmbedding node.trim
  let ιAbs := nextPreparedEmbedding W chain.head.trim
  let Uterminal := chain.terminalWindow.map ιAbs
  have hUcard : Uterminal.card ≤ tNat := by
    have hs : (Uterminal.card:ℝ) ≤ t := by
      dsimp only [Uterminal]
      rw [card_map,chain.card_terminalWindow]
      exact chain.terminalOrder_bounds.2
    exact_mod_cast hs.trans (Nat.le_ceil t)
  have hPrepared : Dispersal.PreparedCore HAbs.G HAbs.lab F (α/8) h Nouter (β node.index) := by
    simpa only [show (α/4)/2 = α/8 by ring] using node.prepared
  have hAbsOrder : Nouter ≤ Fintype.card (Survivors node.trim) := by
    have hEmpty := hPrepared.order ∅ (by
      simp only [card_empty,Nat.cast_zero]
      exact mul_nonneg (hβ node.index) (Nat.cast_nonneg _))
    have hSize : Fintype.card (Dispersal.Surv (∅ : Finset (Survivors node.trim))) ≤
        Fintype.card (Survivors node.trim) :=
      Fintype.card_le_of_injective (fun v => v.val) Subtype.val_injective
    simp only [← Nat.card_eq_fintype_card] at hEmpty hSize ⊢
    exact hEmpty.trans hSize
  have hPreparedReserve := preparedCore_lower_order HAbs F (α/8) (β node.index) h
    Nouter Nreserve hPrepared (le_max_left _ _)
  let r : Fin (L+1) := ⟨node.index,by have hs := node.index_le; dsimp [L]; omega⟩
  obtain ⟨RAbs,hRAvoid,hRCard,hRDeg,hRBasal,hAbsorb⟩ :=
    hReserve HAbs F ((le_max_right _ _).trans hAbsOrder) r hPreparedReserve W Uterminal
      (hWhi.le.trans (by gcongr; exact min_le_left _ _)) hUcard
  let R := embeddedEdges ιOut RAbs
  have hRBasalOrig : Basal H F R :=
    basal_embedding HAbs H F ιOut (fun _ _ hv => hv) (fun _ => rfl) hRBasal
  obtain ⟨DR,hDR⟩ := hRBasalOrig
  have hRAvoidOrig : Disjoint R (triEdges (liftVertexSet node.trim W)) := by
    change Disjoint (embeddedEdges ιOut RAbs) (triEdges (W.map ιOut))
    rw [triEdges_embedding]
    exact embedded_disjoint ιOut hRAvoid
  have hRDegOrig : ∀v, SparseEdge.degIn R v ≤ K := by
    intro v
    calc
      SparseEdge.degIn R v ≤ R.card := Finset.card_filter_le _ _
      _ ≤ RAbs.card := Finset.card_image_le
      _ ≤ K := hRCard
  have hRCap : (K:ℝ) ≤ θT*Fintype.card X := by
    have hnCeil : (⌈(K:ℝ)/θT⌉₊:ℝ) ≤ Fintype.card X := by exact_mod_cast hnReserve
    have hs := (Nat.le_ceil ((K:ℝ)/θT)).trans hnCeil
    have hp := (div_le_iff₀ hθT).mp hs
    simpa only [mul_comm] using hp
  obtain ⟨P₀,hData,state,Pouter,hPouter,hP₀Outer,hRestOuter,hOuterDisjoint,hReservedDisjoint,hOuterPartition⟩ :=
    hMakeOuter H μ hnOuter hSeed hH2 h3 hClean
      ((le_max_right _ _).trans hMrequired) node W hWrelativeLo hWrelativeHi hPools hPaths
      chain hMetadata R DR K (basal_subset_edges ⟨DR,hDR⟩) hDR hRAvoidOrig hRDegOrig hRCap ν w hν hw
  have hLayers := hMakeLayers M ((le_max_left _ _).trans hMrequired) chain hMetadata
  have hAdjAbs : ∀u v, state.host.G.Adj u v → HAbs.G.Adj (ιAbs u) (ιAbs v) := by
    intro u v huv
    exact state.graph_le huv
  have hLabAbs : ∀u, state.host.lab u = HAbs.lab (ιAbs u) := by
    intro u
    exact congrFun state.labels u
  have hAdjOrig : ∀u v, state.host.G.Adj u v → H.G.Adj (ιOut (ιAbs u)) (ιOut (ιAbs v)) :=
    fun u v huv => hAdjAbs u v huv
  have hLabOrig : ∀u, state.host.lab u = H.lab (ιOut (ιAbs u)) := hLabAbs
  obtain ⟨P,Lres,hP₀P,hRest,hDis,hPartition,hRL,hPhysical,hSupport,hLower,hUpper⟩ :=
    raw_paths_reserved_assembly_preserving_outer_cover chain (2*C) (α/16) ζ hLayers state
      H HAbs ιAbs ιOut hAdjOrig hLabOrig hAdjAbs hLabAbs Pouter RAbs
      (P₀.biUnion triEdges) hP₀Outer hRestOuter
      hOuterPartition hOuterDisjoint hReservedDisjoint
  have hSupportSet : support Lres ⊆ Uterminal := by
    intro v hv
    obtain ⟨_,e,he,hv⟩ := mem_filter.mp hv
    exact hSupport e he v hv
  have hAbsorbed : Basal HAbs F (RAbs ∪ Lres) := hAbsorb Lres hPhysical hSupportSet
  obtain ⟨hP₀,hSparse,hQuota⟩ := hData
  obtain ⟨D,hD,hP₀D⟩ := decomposition_of_reserved_absorption_preserving H HAbs F ιOut
    (fun _ _ huv => huv) (fun _ => rfl) P (P₀.biUnion triEdges) RAbs Lres P₀
      hP₀.isDecomposition hP₀P hRest hDis hPartition hAbsorbed
  refine ⟨D,hD,?_⟩
  intro k
  have hs := TriangleMonitors.completed_statistic_error hD hP₀D (2*ζStat) hSparse
    (w k) (hw k) (∑ Q ∈ allowed H F, μ Q*w k Q) (2*ζStat) (hQuota k)
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  dsimp only [ζStat]
  linarith only [hη]

#print axioms main_theorem_T_with_triangle_monitors
end TypedTriangle.Vortex
