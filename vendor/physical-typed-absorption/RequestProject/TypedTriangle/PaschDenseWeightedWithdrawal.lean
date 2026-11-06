module
public import RequestProject.TypedTriangle.PaschWeightedForkTupleCore
public import RequestProject.TypedTriangle.PaschDenseWeightedPaidSelector
public import RequestProject.TypedTriangle.PaschWeightedWithdrawalWindows
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SimpleGraph SelSimul SelBridge SelTyped S07V26 S07V27
open TypedTriangle.ComponentRows S07V24 S07V25 S07V45
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch

/-- Literal witnesses and the full fixed universe of a paid withdrawal. -/
def WeightedWithdrawalResult
    {V I Ambient : Type} [Fintype V] [Fintype Ambient]
    (ι : V ↪ Ambient) (H : Host V I) (F : Set (Multiset I))
    (a κ : ℝ) (m : ℕ) (W : Finset V)
    (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
    (r A qSel : ℕ) (τ : ℝ) (R0 : Finset (Finset Ambient)) (L0 : ℕ) : Prop :=
    let r1 := 3*r+forkQ κ r+4
    ∃ fk : Sym2 V → Fork V,
      let T := XZ X.edgeFinset W
      let Rf := forkUnion T fk
      let X1 := (X.edgeFinset\T)∪QU fk T
      let B1 := X.edgeFinset∪B.edgeFinset∪Rf
      let GX := SimpleGraph.fromEdgeSet (X1:Set (Sym2 V))
      let GB := SimpleGraph.fromEdgeSet (B1:Set (Sym2 V))
      ∃ (σ : V→LocalSel V) (C : Finset (Sym2 V)) (DPaid : Finset (Finset V)),
      let Z := univ\W
      let R := Rf∪(fuelU Z σ∪C)
      let U := forkModes T fk∪(selectorUniverse Z σ∪DPaid)
      ForkSystem H.G H.lab F W X.edgeFinset B.edgeFinset fk ∧
      SimulFamily H.G H.lab F GX GB Z (rootAdm H.G H.lab F GX) A qSel σ ∧
      IsDecomposition H F R (modeDec fk T ∅∪DPaid) ∧
      Basal H F (SelSimul.residual GX Z σ ∅∪C) ∧
      (SelSimul.residual GX Z σ ∅∪C) ⊆ R ∧
      (∀e ∈ SelSimul.residual GX Z σ ∅∪C, ∀v ∈ e, v ∈ W) ∧
      (∀v, (edeg (SelSimul.residual GX Z σ ∅∪C) v:ℝ)  ≤  τ*Fintype.card V) ∧
      Disjoint R (X.edgeFinset∪B.edgeFinset) ∧
      (∀e ∈ R, ∃v ∈ e, v ∈ W) ∧ (∀v, (edeg R v:ℝ)  ≤  τ*Fintype.card V) ∧
      PairCodegreeBound (mapConfiguration ι U) 63 ∧
      (∀Q ∈ U, Q.card=3) ∧
      (count (R0∪mapConfiguration ι U):ℝ)  ≤  count R0+
        (T.card:ℝ)*forkPaschPayment κ L0 (Fintype.card Ambient) (Fintype.card V)+
        ((r1*Z.card:ℕ):ℝ)*weightedCoreRoutePay a m (Fintype.card Ambient) W.card (L0+122)+
        2*((61*r1+60*qSel:ℕ):ℝ)*Fintype.card Ambient*((L0+63:ℕ):ℝ)^3/κ ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → IsPhysical H F L →
        let I0 := L∩T
        let L1 := (L\I0)∪QU fk I0
        let Dsel := (packing GX Z σ L1).image (fun x => selectorTriangle x.1 x.2)
        ∃ Ps Y : Finset (Sym2 V), R∪L=Ps∪Y ∧ Disjoint Ps Y ∧
          IsDecomposition H F Ps (Dsel∪modeDec fk T I0) ∧
          Dsel∪modeDec fk T I0 ⊆ U ∧
          (∀e ∈ Y, ∀v ∈ e, v ∈ W) ∧
          (∀v, (edeg Y v:ℝ)  ≤  τ*Fintype.card V) ∧ IsPhysical H F Y

/-- Actual fork reduction followed by the same weighted selector and common
payment. The scalar windows are construction parameters, not a host provider.
Every later paid mode is retained literally inside one fixed universe. -/
theorem weighted_withdrawal_from_core_windows
    {V I Ambient : Type} [Fintype V] [Fintype Ambient]
    (ι : V ↪ Ambient) (H : Host V I) (F : Set (Multiset I))
    (a qRate κ : ℝ) (ha : 0 < a) (hqRate : 0 < qRate) (hκ : 0 < κ)
    (m : ℕ) (hm : 0 < m) (hOdd : Odd (m+1)) (W : Finset V)
    (hOrder : 2  ≤  qRate*Fintype.card V)
    (hWindow : (W.card:ℝ)  ≤  2*qRate*Fintype.card V)
    (hWindowLower : qRate*Fintype.card V/4  ≤  (W.card:ℝ))
    (hPaths : ∀v x y, OrigAdm H.G H.lab F v x y →
      a*(Fintype.card V:ℝ)^m*qRate^m/4  ≤ 
        (pathsIn (link H.G H.lab F v) m x y W).card)
    (hpool : ∀u v, u ≠ v → ∀k, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      κ*Fintype.card V  ≤  ((TypedTriangle.commonNbrs H k u v)∩W).card)
    (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
    (r b : ℕ) (hXG : X ≤ H.G)
    (hCover : ∀e ∈ X.edgeFinset, ∃T, IsAllowed H F T ∧ e ∈ triEdges T)
    (hX : ∀v, X.degree v ≤ r) (hB : ∀v, B.degree v ≤ b)
    (hr : (r:ℝ)  ≤  forkEps κ*Fintype.card V)
    (hb : (b:ℝ)  ≤  forkEps κ*Fintype.card V)
    (hn32 : 32  ≤  κ*Fintype.card V) :
    let r1 := 3*r+forkQ κ r+4
    let b1 := b+3*r+forkQ κ r+4
    ∀ A qSel p : ℕ, ∀ τ : ℝ,
    200*m+8 ≤ A → 0 < qSel → 0 < p →
    r1+b1+A*r1*Fintype.card V/qSel+(A+1)*r1+10*r1+m*(200*r1)  ≤ 
      ⌊Vortex.windowRouteRate a qRate m*Fintype.card V⌋₊ →
    ((b1+61*r1+60*qSel+60:ℕ):ℝ)  ≤  Vortex.windowRouteRate a qRate m*Fintype.card V →
    ((Fintype.card V*(61*r1+60*qSel):ℕ):ℝ)/(p:ℝ)+
      2*((max (A*r1) (60*r1+61*qSel)+r1+b1+3*(61*r1+60*qSel)+2*p:ℕ):ℝ)  ≤ 
        (κ/2)*Fintype.card (Survivors (univ\W)) →
    ((2*r+forkQ κ r+4+max (A*r1) (60*r1+61*qSel)+2*(61*r1+60*qSel+p):ℕ):ℝ)  ≤ 
      τ*Fintype.card V →
    ((3*(61*r1+60*qSel)+2*p:ℕ):ℝ)  ≤  τ*Fintype.card V →
    ∀ R0 : Finset (Finset Ambient), ∀ L0 : ℕ, PairCodegreeBound R0 L0 →
    WeightedWithdrawalResult ι H F a κ m W X B r A qSel τ R0 L0 := by
  intro r1 b1 A qSel p τ hA hqSel hp hBud hρ hPay hFuelCap hResCap R0 L0 hCodeg
  have hXE : X.edgeFinset ⊆ edges H := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,SimpleGraph.edgeSet_mono hXG (by simpa using he)⟩
  have hXd : ∀v, SparseEdge.degIn X.edgeFinset v ≤ r := by
    intro v; change edeg X.edgeFinset v ≤ r; rw [edeg_edgeFinset]; exact hX v
  have hBd : ∀v, SparseEdge.degIn B.edgeFinset v ≤ b := by
    intro v; change edeg B.edgeFinset v ≤ b; rw [edeg_edgeFinset]; exact hB v
  obtain ⟨fk,hFS,hRfDeg,hOff,hOn,hForkCG,hForkCount,hRfInc,hX1W⟩ :=
    CorePaid.forks_on_core_pool_with_pasch_covered ι W hκ hpool X.edgeFinset B.edgeFinset hXE
      hCover hXd hBd hr hb hn32 R0 L0 hCodeg
  let T := XZ X.edgeFinset W
  let Rf := forkUnion T fk
  let X1 := (X.edgeFinset\T)∪QU fk T
  let B1 := X.edgeFinset∪B.edgeFinset∪Rf
  have hRfBas : Basal H F Rf := ⟨_,hOff⟩
  have hRfE : Rf ⊆ edges H := CorePaid.basal_subset_edges hRfBas
  have hRfAvoid : Disjoint Rf (X.edgeFinset∪B.edgeFinset) := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨f,hf,he⟩ := mem_biUnion.mp he
    exact Finset.disjoint_left.mp (hFS.2.2 f hf) he he'
  have hRfd : ∀v, edeg Rf v ≤ 2*r+forkQ κ r+4 := hRfDeg
  have hX1Deg := (hFS.fork_L (L:=∅) (empty_subset _)).2.2.2.2.2.2
  have hX1d : ∀v, edeg X1 v ≤ r1 := by
    intro v
    have h1 := hX1Deg v
    have h2 : edeg X.edgeFinset v ≤ r := by rw [edeg_edgeFinset]; exact hX v
    have h3 := hRfd v
    change edeg X1 v ≤ edeg X.edgeFinset v+edeg Rf v at h1
    dsimp only [r1]; omega
  have hB1d : ∀v, edeg B1 v ≤ b1 := by
    intro v
    have h1 := edeg_union_le (X.edgeFinset∪B.edgeFinset) Rf v
    have h2 := edeg_union_le X.edgeFinset B.edgeFinset v
    rw [edeg_edgeFinset,edeg_edgeFinset] at h2
    have h3 := hX v; have h4 := hB v; have h5 := hRfd v
    dsimp only [B1,b1]; omega
  have hX1E : X1 ⊆ edges H := union_subset (sdiff_subset.trans hXE)
    (((hFS.fork_modes (I':=T) subset_rfl).2.1).trans hRfE)
  have hDiagX : ∀e ∈ X1, ¬e.IsDiag := CorePaid.edges_diagonal_free hX1E
  have hDiagB : ∀e ∈ B1, ¬e.IsDiag := by
    intro e he
    rcases mem_union.mp he with he|he
    · rcases mem_union.mp he with he|he
      · exact X.not_isDiag_of_mem_edgeSet (by simpa using he)
      · exact B.not_isDiag_of_mem_edgeSet (by simpa using he)
    · exact CorePaid.edges_diagonal_free hRfE e he
  let GX := SimpleGraph.fromEdgeSet (X1:Set (Sym2 V))
  let GB := SimpleGraph.fromEdgeSet (B1:Set (Sym2 V))
  have hGX : GX.edgeFinset=X1 := CorePaid.edgeFinset_fromEdges X1 hDiagX
  have hGB : GB.edgeFinset=B1 := CorePaid.edgeFinset_fromEdges B1 hDiagB
  have hGXmem : ∀e, e ∈ GX.edgeSet ↔ e ∈ X1 := fun e => by
    simpa only [SimpleGraph.mem_edgeFinset] using Finset.ext_iff.mp hGX e
  have hGXW : ∀v w, GX.Adj v w → v ∈ W∨w ∈ W := by
    intro v w hvw
    obtain ⟨x,hx,hW⟩ := hX1W s(v,w) hvw.1
    rcases Sym2.mem_iff.mp hx with rfl|rfl
    · exact Or.inl hW
    · exact Or.inr hW
  let Z := univ\W
  obtain ⟨hZW,hZ⟩ := allRoots_hyps W GX hGXW
  have hCovX1 : ∀e ∈ X1, ∃Q, IsAllowed H F Q∧e ∈ triEdges Q := by
    intro e he
    rcases mem_union.mp he with he|he
    · exact hCover e (mem_sdiff.mp he).1
    · have heRf : e ∈ Rf := (hFS.fork_modes (I':=T) subset_rfl).2.1 he
      obtain ⟨Q,hQ,heQ⟩ := hOff.exists_mem heRf
      exact ⟨Q,hOff.1 Q hQ,heQ⟩
  have hLink : ∀v ∈ Z, ∀u, GX.Adj v u → ∃y, (link H.G H.lab F v).Adj u y := by
    intro v hv u hvu
    obtain ⟨Q,hQ,heQ⟩ := hCovX1 s(v,u) ((hGXmem _).mp (by simpa using hvu))
    obtain ⟨hvQ,huQ,hvuQ⟩ := mem_triEdges.mp heQ
    exact link_of_allowed hQ hvQ huQ hvuQ
  have hCore : CommonNbrCond (restrictedHost H Z) F κ :=
    CorePaid.commonNbrCond_of_core_pool H F W hκ.le hpool
  let Rfixed := R0∪mapConfiguration ι (forkModes T fk)
  have hFixed : PairCodegreeBound Rfixed (L0+2) := hCodeg.union hForkCG
  obtain ⟨σ,C,DPaid,hFamily,hAux,hCavoid,hAvoid,hDPaid,hEmpty,hCinside,hDeg,hStat,hModes⟩ :=
    dense_weighted_paid_core_selector ι a qRate ha hqRate m hm hOdd W hOrder hWindow hWindowLower
      hPaths GX GB Z hZ hZW hLink hA hqSel
      (CorePaid.fromEdges_degree_le X1 hDiagX hX1d)
      (CorePaid.fromEdges_degree_le B1 hDiagB hB1d) hBud hρ κ hκ hCore p hp hPay Rfixed (L0+2) hFixed
  letI : Fintype GX.edgeSet := GX.fintypeEdgeSet
  letI : Fintype GB.edgeSet := GB.fintypeEdgeSet
  let Rp := fuelU Z σ∪C
  let U := forkModes T fk∪(selectorUniverse Z σ∪DPaid)
  have hAvoid' : Disjoint Rp (X1∪B1) := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    apply Finset.disjoint_left.mp hAvoid he
    rcases mem_union.mp he' with he'|he'
    · exact mem_union_left _ (SimpleGraph.mem_edgeFinset.mpr ((hGXmem e).mpr he'))
    · have hGBmem : e ∈ GB.edgeSet ↔ e ∈ B1 := by
        simpa only [SimpleGraph.mem_edgeFinset] using Finset.ext_iff.mp hGB e
      exact mem_union_right _ (SimpleGraph.mem_edgeFinset.mpr (hGBmem.mpr he'))
  have hRpOld : Disjoint Rp (X.edgeFinset∪B.edgeFinset∪Rf) := hAvoid'.mono_right subset_union_right
  have hRfRp : Disjoint Rf Rp := (hRpOld.mono_right subset_union_right).symm
  have hSelectorCG : PairCodegreeBound (selectorUniverse Z σ) 60 :=
    fun x y hxy => selectorUniverse_pair_degree_le hFamily hZ x y hxy
  have hPaidCG : PairCodegreeBound DPaid 1 :=
    pairCodegreeBound_of_linear (packing_linear (show IsPacking H F DPaid from ⟨hDPaid.1,hDPaid.2.1⟩))
  have hUniverseCG : PairCodegreeBound U 63 :=
    (fork_modes_pairCodegree hFS).union (hSelectorCG.union hPaidCG)
  have hMapSet : R0∪mapConfiguration ι U =
      Rfixed∪mapConfiguration ι (selectorUniverse Z σ∪DPaid) := by
    simp only [U,Rfixed,mapConfiguration,Finset.map_union,union_assoc]
  have hForkCount' : (count Rfixed:ℝ) ≤ count R0+
      (T.card:ℝ)*forkPaschPayment κ L0 (Fintype.card Ambient) (Fintype.card V) := hForkCount
  have hCount : (count (R0∪mapConfiguration ι U):ℝ)  ≤  count R0+
      (T.card:ℝ)*forkPaschPayment κ L0 (Fintype.card Ambient) (Fintype.card V)+
      ((r1*Z.card:ℕ):ℝ)*weightedCoreRoutePay a m (Fintype.card Ambient) W.card (L0+122)+
      2*((61*r1+60*qSel:ℕ):ℝ)*Fintype.card Ambient*((L0+63:ℕ):ℝ)^3/κ := by
    rw [hMapSet]
    have hArg1 : L0+2+120=L0+122 := by omega
    have hArg2 : L0+2+61=L0+63 := by omega
    rw [hArg1,hArg2] at hStat
    linarith only [hStat,hForkCount']
  obtain ⟨hEq0,_,_,_,hIn0,hDeg0,_⟩ := hModes ∅ (empty_subset _) (isPhysical_empty H F)
  have hY0Sub : (SelSimul.residual GX Z σ ∅∪C) ⊆ Rf∪Rp := by
    have hh : Rp=packEdges (packing GX Z σ ∅)∪(SelSimul.residual GX Z σ ∅∪C) := by
      simpa only [union_empty] using hEq0
    exact (show (SelSimul.residual GX Z σ ∅∪C) ⊆ Rp from by rw [hh]; exact subset_union_right).trans subset_union_right
  have hY0Inside : ∀e ∈ SelSimul.residual GX Z σ ∅∪C, ∀v ∈ e, v ∈ W := by
    intro e he v hv
    simpa only [Z,mem_sdiff,mem_univ,true_and,not_not] using hIn0 e he v hv
  have hY0Degree : ∀v, (edeg (SelSimul.residual GX Z σ ∅∪C) v:ℝ) ≤ τ*Fintype.card V :=
    fun v => (Nat.cast_le.mpr (hDeg0 v)).trans hResCap
  refine ⟨fk,σ,C,DPaid,hFS,hFamily,hOff.union hDPaid hRfRp,hEmpty,hY0Sub,hY0Inside,hY0Degree,?_,?_,?_,
    pairCodegreeBound_mapConfiguration ι U 63 hUniverseCG,?_,hCount,?_⟩
  · exact disjoint_union_left.mpr ⟨hRfAvoid,hRpOld.mono_right subset_union_left⟩
  · intro e he
    rcases mem_union.mp he with he|he
    · exact hRfInc e he
    · rcases mem_union.mp he with he|he
      · exact weighted_selector_fuel_meets_window W _ A qSel σ hFamily hGXW e he
      · induction e using Sym2.ind with
        | h v w =>
          exact ⟨v,by simp,by simpa only [Z,mem_sdiff,mem_univ,true_and,not_not] using hCinside s(v,w) he v (by simp)⟩
  · intro v
    have h1 : (edeg (Rf∪Rp) v:ℝ)  ≤  edeg Rf v+edeg Rp v := by exact_mod_cast edeg_union_le Rf Rp v
    have h2 : (edeg Rf v:ℝ)  ≤  (2*r+forkQ κ r+4:ℕ) := Nat.cast_le.mpr (hRfd v)
    have h3 : (edeg Rp v:ℝ)  ≤  (max (A*r1) (60*r1+61*qSel)+2*(61*r1+60*qSel+p):ℕ) := by
      exact_mod_cast hDeg v
    have hh := hFuelCap
    push_cast at h2 h3 hh
    linarith only [h1,h2,h3,hh]
  · intro Q hQ
    rcases mem_union.mp hQ with hQ|hQ
    · rcases mem_union.mp hQ with hQ|hQ
      · exact hOff.1 Q hQ |>.1
      · exact hOn.1 Q hQ |>.1
    · rcases mem_union.mp hQ with hQ|hQ
      · exact selectorUniverse_allowed hFamily Q hQ |>.1
      · exact hDPaid.1 Q hQ |>.1
  · intro L hL hPhys I0 L1 Dsel
    let Pf := (Rf\QU fk I0)∪I0
    obtain ⟨hfEq,hfDisj,_,hDiff,hL1,_,_⟩ := hFS.fork_L hL
    change L∪Rf=L1∪Pf at hfEq
    change Disjoint L1 Pf at hfDisj
    have hL1Phys : IsPhysical H F L1 := SelectorEntry.physical_of_difference hPhys hDiff
    obtain ⟨hsEq,hsDisj,hDsel,hDselU,hYIn,hYDeg,hYP⟩ := hModes L1
      (fun e he => SimpleGraph.mem_edgeFinset.mpr ((hGXmem e).mpr (hL1 he))) hL1Phys
    let Ps := packEdges (packing GX Z σ L1)
    let Y := SelSimul.residual GX Z σ L1∪C
    have hPf : IsDecomposition H F Pf (modeDec fk T I0) := (hFS.fork_modes inter_subset_right).1
    have hPfSub : Pf ⊆ L∪Rf := by rw [hfEq]; exact subset_union_right
    have hRpLR : Disjoint Rp (L∪Rf) := hRpOld.mono_right
      (union_subset (hL.trans (subset_union_left.trans subset_union_left)) subset_union_right)
    have hRpPf := hRpLR.mono_right hPfSub
    have hUnionPf : Disjoint (Rp∪L1) Pf := disjoint_union_left.mpr ⟨hRpPf,hfDisj⟩
    have hPsSub : Ps ⊆ Rp∪L1 := by rw [hsEq]; exact subset_union_left
    have hYSub : Y ⊆ Rp∪L1 := by rw [hsEq]; exact subset_union_right
    have hPsPf := hUnionPf.mono_left hPsSub
    have hYPf := hUnionPf.mono_left hYSub
    refine ⟨Ps∪Pf,Y,?_,disjoint_union_left.mpr ⟨hsDisj,hYPf.symm⟩,
      hDsel.union hPf hPsPf,?_,?_,?_,hYP⟩
    · calc (Rf∪Rp)∪L=(L∪Rf)∪Rp := by ac_rfl
           _=(L1∪Pf)∪Rp := by rw [hfEq]
           _=(Rp∪L1)∪Pf := by ac_rfl
           _=(Ps∪Y)∪Pf := by rw [hsEq]
           _=(Ps∪Pf)∪Y := by ac_rfl
    · exact union_subset (hDselU.trans (subset_union_left.trans subset_union_right))
        ((fork_modes_subset_universe T I0 fk).trans subset_union_left)
    · intro e he v hv
      simpa only [Z,mem_sdiff,mem_univ,true_and,not_not] using hYIn e he v hv
    · intro v
      exact (Nat.cast_le.mpr (hYDeg v)).trans hResCap


/-- Host-independent scalar caps instantiate all windows of the actual
weighted withdrawal. The forbidden cap is independent of the requested τ
and of the stock supply; the same actual modes are returned. -/
theorem fixed_core_positive_weighted_withdrawal
    {V I Ambient : Type} [Fintype V] [Fintype Ambient]
    (ι : V ↪ Ambient) (H : Host V I) (F : Set (Multiset I))
    (a qRate κ : ℝ) (ha : 0 < a) (hqRate : 0 < qRate) (hκ : 0 < κ)
    (m : ℕ) (hm : 0 < m) (hOdd : Odd (m+1)) (W : Finset V)
    (hOrder : 2 ≤ qRate*Fintype.card V)
    (hWindow : (W.card:ℝ) ≤ 2*qRate*Fintype.card V)
    (hWindowLower : qRate*Fintype.card V/4 ≤ (W.card:ℝ))
    (hPaths : ∀v x y, OrigAdm H.G H.lab F v x y →
      a*(Fintype.card V:ℝ)^m*qRate^m/4 ≤ (pathsIn (link H.G H.lab F v) m x y W).card)
    (hpool : ∀u v, u ≠ v → ∀k, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      κ*Fintype.card V ≤ ((TypedTriangle.commonNbrs H k u v)∩W).card)
    (X B : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B.Adj]
    (r b : ℕ) (hXG : X ≤ H.G)
    (hCover : ∀e ∈ X.edgeFinset, ∃T, IsAllowed H F T∧e ∈ triEdges T)
    (hX : ∀v, X.degree v ≤ r) (hB : ∀v, B.degree v ≤ b)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : weightedWithdrawalOrder κ qRate a m τ ≤ Fintype.card V)
    (hr : (r:ℝ) ≤ weightedWithdrawalInputBudget κ qRate a m τ*Fintype.card V)
    (hb : (b:ℝ) ≤ weightedWithdrawalStockBudget κ qRate a m*Fintype.card V)
    (R0 : Finset (Finset Ambient)) (L0 : ℕ) (hCodeg : PairCodegreeBound R0 L0) :
    ∃ qSel : ℕ,
      qSel ≤ CorePaid.Explicit.selQLimit (Vortex.windowRouteRate a qRate m) (selA (m+1))*
        (3*r+forkQ κ r+4+1) ∧
      WeightedWithdrawalResult ι H F a κ m W X B r (selA (m+1)) qSel τ R0 L0 := by
  obtain ⟨qSel,p,hqSel,hqBound,hp,hBud,hρ,hPay,hFuelCap,hResCap⟩ :=
    weighted_withdrawal_windows m hκ hqRate ha hτ (Fintype.card V) W.card r b
      hn (by convert hWindowLower using 1 <;> ring) hr hb
  have hForkR : (r:ℝ) ≤ forkEps κ*Fintype.card V :=
    hr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hForkB : (b:ℝ) ≤ forkEps κ*Fintype.card V :=
    hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hn32 : 32 ≤ κ*Fintype.card V := by
    have hc : ⌈32/κ⌉₊ ≤ Fintype.card V :=
      (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have hh := (Nat.le_ceil (32/κ)).trans (Nat.cast_le.mpr hc)
    simpa only [mul_comm] using (div_le_iff₀ hκ).mp hh
  refine ⟨qSel,hqBound,?_⟩
  exact weighted_withdrawal_from_core_windows ι H F a qRate κ ha hqRate hκ m hm hOdd W
    hOrder hWindow hWindowLower hPaths hpool X B r b hXG hCover hX hB hForkR hForkB hn32
    (selA (m+1)) qSel p τ (by unfold selA; omega) hqSel hp hBud hρ
    (by simpa only [CorePaid.card_survivors_compl] using hPay)
    hFuelCap hResCap R0 L0 hCodeg

#print axioms weighted_withdrawal_from_core_windows
#print axioms fixed_core_positive_weighted_withdrawal
end TypedTriangle.Pasch
