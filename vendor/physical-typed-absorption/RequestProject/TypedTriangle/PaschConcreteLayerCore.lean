module
public import RequestProject.TypedTriangle.PaschPreparedAmbientBank
public import RequestProject.TypedTriangle.PaschModeUniverse
public import RequestProject.TypedTriangle.PaschPaidOuterPartitionRetainingDecompositions
public import RequestProject.TypedTriangle.PaschWeightedForkTupleCore
public import RequestProject.TypedTriangle.VortexNakedReferenceAtFutureCore
public import RequestProject.TypedTriangle.ActualResidualCharge
public import RequestProject.TypedTriangle.ExplicitMonitorAllocation
public import RequestProject.TypedTriangle.G4PositiveMomentBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.ConcreteLayer
open S07V40 S07V42 S07V43 S07V44 S07V46 ProtectedBank AmbientBank CatalogNative.Explicit LocalizedCover

/-- Both fixed local modes are pulled from the ACTUAL history. They are not
chosen again from a basal conclusion and map to its literal stored families. -/
theorem actual_bank_local_modes
    {X V I : Type} [Fintype X] [Fintype V]
    (H : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    {d c E Rc P q Ecell z N Ub : ℕ} {pay : ℝ}
    (C0 : CoreCompression H.G H.lab F W d c E) (ι : X ↪ V)
    (hLab : ∀x,H.lab x=Hambient.lab (ι x))
    (F0 : Finset (Sym2 V)) (R0 : Finset (Finset V))
    (es : List (RichBank.Entry V (Cat d Rc) P))
    (hInv : RichBank.Seeded.RunInv Hambient F
      (liftSetting ι (protect (childSetting C0 Rc P q Ecell z) (pullEdges ι F0))) Ub pay R0 N es) :
    ∃ Doff Don : Finset (Finset X),
      IsDecomposition H F (pullEdges ι (RichBank.offEdges es)) Doff ∧
      IsDecomposition H F (pullEdges ι (RichBank.usedEdges es)) Don ∧
      mapConfiguration ι Doff=RichBank.offFamily es ∧ mapConfiguration ι Don=RichBank.onFamily es ∧
      mapConfiguration ι (Doff∪Don)=RichBank.modes es ∧ PairCodegreeBound (Doff∪Don) 2 ∧
      (count (Doff∪Don):ℝ) ≤ es.length*pay ∧
      (count (R0∪mapConfiguration ι (Doff∪Don)):ℝ) ≤ count R0+es.length*pay := by
  have hUsed : RichBank.usedEdges es ⊆ liftEdges ι (edges H) := by
    intro f hf
    rw [←RichBank.Actual.toBank_total es] at hf
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hf
    obtain ⟨D,hD,hBas,_⟩ := (hInv.history.local_history.good (es.get i) (List.get_mem ..)).good.2.2.1
    rw [RichBank.Actual.toBank_tot,hD] at hi
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hi
    exact mem_map.mpr ⟨g,CorePaid.basal_subset_edges hBas hg,rfl⟩
  obtain ⟨Doff,hOff,hOffMap,_⟩ := decomposition_pull_of_supported H Hambient F ι hLab
    hInv.history.local_history.off ((RichBank.offEdges_subset_used es).trans hUsed)
  obtain ⟨Don,hOn,hOnMap,_⟩ := decomposition_pull_of_supported H Hambient F ι hLab
    hInv.history.local_history.on hUsed
  have hMap : mapConfiguration ι (Doff∪Don)=RichBank.modes es := by
    unfold mapConfiguration RichBank.modes
    rw [map_union]
    exact congrArg₂ (·∪·) hOffMap hOnMap
  have hCG : PairCodegreeBound (Doff∪Don) 2 :=
    pairCodegreeBound_two_modes (show IsPacking H F Doff from ⟨hOff.1,hOff.2.1⟩)
      (show IsPacking H F Don from ⟨hOn.1,hOn.2.1⟩)
  have hCount : count (Doff∪Don)=count (RichBank.modes es) := by
    rw [←count_mapConfiguration ι (Doff∪Don),hMap]
  refine ⟨Doff,Don,hOff,hOn,hOffMap,hOnMap,hMap,hCG,?_,?_⟩
  · rw [hCount]
    exact hInv.history.local_history.budget
  · rw [hMap]
    exact hInv.history.external_budget

/-- Actual saturated-prefix pullbacks are within the SAME prepared deletion
quota, so its already constructed CatalogGen witnesses apply to every stratum. -/
theorem actual_strata_catalog_generates
    {X V I Q C : Type} [Fintype X] [Fintype V] [AddCommGroup Q] [Fintype C]
    (ι : X ↪ V) (H : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    {d c E Rc N Ub : ℕ} {pay : ℝ} (C0 : CoreCompression H.G H.lab F W d c E)
    (S : MacroSetting V Q C) (R0 : Finset (Finset V))
    (es : List (RichBank.Entry V C S.P))
    (hInv : RichBank.Seeded.RunInv Hambient F S Ub pay R0 N es)
    (hq : 0 < S.q) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax)
    (hGen : ∀Z : Finset X,Z.card ≤ S.zmax → CatalogGen C0 Rc Z) :
    ∀j,CatalogGen C0 Rc (pullVertices ι (RichBank.Actual.Zstrat S es N j)) := by
  intro j
  apply hGen
  apply (pull_vertices_card_le ι _).trans
  exact RichBank.Actual.saturatedPrefix_small hInv hq hcap _
    ((RichBank.Actual.preStrat_le (S:=S) (es:=es) N j).trans (RichBank.Actual.numRounds_le N))

/-- Actual allocation monitors and their edge tests are constructed from the
same C0 and actual rich strata before the partial packing is selected. -/
theorem actual_bank_monitor_weights
    (α β qCore : ℝ) (h d c E Rc : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hqCore : 0 < qCore) (hβα : β ≤ α)
    {X V I Q C : Type} [Fintype X] [Fintype V] [AddCommGroup Q] [Fintype C]
    (ι : X ↪ V) (H : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    (C0 : CoreCompression H.G H.lab F W d c E) (S : MacroSetting V Q C)
    {N Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (RichBank.Entry V C S.P)}
    (hInv : RichBank.Seeded.RunInv Hambient F S Ub pay R0 N es)
    (hq : 0 < S.q) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax)
    (hGen : ∀Z : Finset X,Z.card ≤ S.zmax → CatalogGen C0 Rc Z)
    (hn : nativeWeightOrder α β qCore h ≤ Fintype.card X)
    (hWlo : qCore*Fintype.card X/2 ≤ W.card)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hCore3 : SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W}→X))
      (H.lab ∘ Subtype.val) F β)
    (hCore4 : SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W}→X))
      (H.lab ∘ Subtype.val) F β h)
    (hzCore : (S.zmax:ℝ) ≤ coreDelta β h*W.card)
    (hz3 : (S.zmax:ℝ) ≤ β/2*W.card)
    (hz4 : (S.zmax:ℝ)*2^Nat.choose (h+1) 2 ≤ β/2*W.card)
    (hzDel : (S.zmax:ℝ) ≤ S07V37.delOf (β/2) h*W.card) :
    let A := S07V34.Explicit.paymentCost d (monR Rc E)
    let M := S07V34.Explicit.monitorMagnitude d (monR Rc E)
    let K := S07V34.Explicit.monitorDimension d (monR Rc E)
    ∃ (Mon : ∀Z : Finset X,CatalogGen C0 Rc Z → PhysicalMonitors C0 Rc Z A M K)
      (Fm : FullMonitor C0 Rc A M K),
    ∃ (loc : ℕ → Fin K → Sym2 X → ℝ) (full : Fin K → Sym2 X → ℝ),
      (∀ ℓ j (x : MCore H.G H.lab F W)
        (hg : CatalogGen C0 Rc (pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1)))),
        ∑e,loc ℓ j e*((x.1 e:ℤ):ℝ)=physMonReal C0
          (Dset C0 Rc (pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1)))) (Mon _ hg).psi j x) ∧
      (∀ j (x : MCore H.G H.lab F W),∑e,full j e*((x.1 e:ℤ):ℝ)=physMonReal C0 ∅ Fm.psi j x) ∧
      (∀ ℓ j T,IsAllowed H F T → |triSum (loc ℓ j) T| ≤
        3*physicalWeightMagnitude (α/2) (β/2) h d c M*(T∩pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card) ∧
      (∀ j T,IsAllowed H F T → |triSum (full j) T| ≤
        3*physicalWeightMagnitude (α/2) (β/2) h d c M*T.card) := by
  dsimp only
  obtain ⟨hMon,hFm⟩ := S07V46.Explicit.uniform_monitors_with_full_explicit d c E Rc C0
  let Mon := fun Z hg => Classical.choice (hMon Z hg)
  let Fm := Classical.choice hFm
  have hgen := actual_strata_catalog_generates ι H Hambient F W C0 S R0 es hInv hq hcap hGen
  obtain ⟨loc,full,hLocRep,hFullRep,hLocTri,hFullTri⟩ :=
    ActualAllocation.choose_weights_on_rich_bank_core α β qCore h d c E Rc
      (S07V34.Explicit.paymentCost d (monR Rc E))
      (S07V34.Explicit.monitorMagnitude d (monR Rc E))
      (S07V34.Explicit.monitorDimension d (monR Rc E)) hα hβ hqCore hβα
      ι H Hambient F W C0 S hInv hq hcap (fun ℓ => Mon _ (hgen (ℓ+1))) Fm
      hn hWlo h3 h4 hCore3 hCore4 hzCore hz3 hz4 hzDel
  exact ⟨Mon,Fm,loc,full,fun ℓ j x _ => hLocRep ℓ j x,hFullRep,hLocTri,hFullTri⟩

/-- Moment transfer for the cover selected by the weighted stock operation.
This is a pure consequence of THAT cover; it does not construct another one. -/
theorem same_cover_moment {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I))
    (J Stock : Finset (Sym2 X)) (C : Finset (Finset X)) (hC : IsPacking H F C)
    (hStock : Stock ⊆ J) (hCJ : C.biUnion triEdges ⊆ J)
    (hLeft : J\C.biUnion triEdges ⊆ Stock)
    (load Λ E0 : ℝ) (hΛ : 0 ≤ Λ)
    (hCdeg : ∀v,(((C.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ load)
    (bad : Finset X) (lam : Sym2 X → ℝ)
    (hTri : ∀T,IsAllowed H F T → |triSum lam T| ≤ 3*Λ*(T∩bad).card)
    (hMoment : |edgeSum lam (J\Stock)| ≤ E0) :
    |edgeSum lam (J\C.biUnion triEdges)-edgeSum lam Stock| ≤ E0+(3*Λ*bad.card)*load/2 := by
  have hCov : J\Stock ⊆ C.biUnion triEdges := by
    intro e he
    by_contra hc
    exact (mem_sdiff.mp he).2 (hLeft (mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,hc⟩))
  have hSub : C.biUnion triEdges ⊆ (J\Stock)∪Stock := by
    intro e he
    by_cases hs : e ∈ Stock
    · exact mem_union_right _ hs
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hCJ he,hs⟩)
  have hEq : J\C.biUnion triEdges=Stock\C.biUnion triEdges := by
    apply subset_antisymm
    · intro e he
      exact mem_sdiff.mpr ⟨hLeft he,(mem_sdiff.mp he).2⟩
    · intro e he
      exact mem_sdiff.mpr ⟨hStock (mem_sdiff.mp he).1,(mem_sdiff.mp he).2⟩
  rw [hEq]
  exact localized_cover_down_entry (J\Stock) Stock C hC sdiff_disjoint hCov hSub
    load Λ E0 hΛ hCdeg bad lam hTri hMoment

/-- A fixed cover and a fixed literal withdrawal mode preserve all the
already selected packing's moments, with the actual load and stock terms. -/
theorem same_cover_positive_moment {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I)) (D : Finset (Finset X))
    (hD : IsDecomposition H F (BasalIncidence.cover D) D)
    (J R Ps Y : Finset (Sym2 X)) (C : Finset (Finset X)) (hC : IsPacking H F C)
    (hStock : BasalIncidence.cover D ⊆ J) (hCJ : C.biUnion triEdges ⊆ J)
    (hLeft : J\C.biUnion triEdges ⊆ BasalIncidence.cover D)
    (hRStock : Disjoint R (BasalIncidence.cover D))
    (hPY : Disjoint Ps Y) (hMove : R∪(J\C.biUnion triEdges)=Ps∪Y)
    (Dps : Finset (Finset X)) (hR : Basal H F R) (hPs : IsDecomposition H F Ps Dps)
    (n ρ τSel ηCover τ Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hStockDeg : ∀v,((BasalIncidence.cover D).filter (fun e => v ∈ e)).card ≤ ρ*n)
    (hRDeg : ∀v,((R.filter (fun e => v ∈ e)).card:ℝ) ≤ τSel*n)
    (hCdeg : ∀v,(((C.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ ηCover*n)
    (bad : Finset X) (lam : Sym2 X → ℝ)
    (hTri : ∀T,IsAllowed H F T → |triSum lam T| ≤ 3*Λ*(T∩bad).card)
    (hMoment : |edgeSum lam (J\BasalIncidence.cover D)| ≤ τ*n*bad.card) :
    |edgeSum lam Y| ≤ (τ+(3*Λ/2)*(ηCover+2*ρ+2*τSel))*n*bad.card := by
  have hRJ : Disjoint R (J\C.biUnion triEdges) := hRStock.mono_right hLeft
  have hLeftDeg : ∀v,(((J\C.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ ρ*n := by
    intro v
    exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter (p:=fun e => v ∈ e) hLeft))).trans (hStockDeg v)
  have hRelative := same_cover_moment H F J (BasalIncidence.cover D) C hC hStock hCJ hLeft
    (ηCover*n) Λ (τ*n*bad.card) hΛ hCdeg bad lam hTri hMoment
  have hPositive := StockEntry.g4_actual_positive_moment_budget H F D hD R
    (J\C.biUnion triEdges) Ps Y hRJ hPY hMove hR ⟨Dps,hPs⟩
    (ρ*n) (τSel*n) (ρ*n) (ηCover*n) (τ*n*bad.card) Λ hΛ
    hStockDeg hRDeg hLeftDeg bad lam hTri hRelative
  exact hPositive.trans (StockEntry.actual_moment_factor_bound Λ n bad.card τ ηCover ρ τSel
    (ηCover*n) hΛ (by positivity) le_rfl)

end TypedTriangle.Pasch.ConcreteLayer
#print axioms TypedTriangle.Pasch.ConcreteLayer.actual_bank_local_modes
#print axioms TypedTriangle.Pasch.ConcreteLayer.actual_strata_catalog_generates

#print axioms TypedTriangle.Pasch.ConcreteLayer.actual_bank_monitor_weights

#print axioms TypedTriangle.Pasch.ConcreteLayer.same_cover_moment
#print axioms TypedTriangle.Pasch.ConcreteLayer.same_cover_positive_moment

namespace TypedTriangle.Pasch
open ProtectedNibble LocalizedCover

/-- Reserve precision precedes the final degree and physical-moment precisions.
Only ONE exact residual seed and ONE partial packing are constructed. -/
theorem protected_joint_packing_deferred_precisions {I : Type} (F : Set (Multiset I))
    (C α τStat L σ εAmbient : ℝ) (h q bankL : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hτStat : 0 < τStat) (hL : 0 < L) (hσ : 0 < σ) (hεAmbient : 0 < εAmbient) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ η τ : ℝ, 0 < η → 0 < τ → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ ε*Fintype.card V →
      ∀ (κ ι ν : Type) [Fintype κ] [Fintype ι] [Fintype ν]
        (bad : κ → Finset V) (loc : κ → Sym2 V → ℝ) (full : ι → Sym2 V → ℝ)
        (w : ν → Finset V → ℝ),
        ((Fintype.card κ+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (loc k) T| ≤ 3*L*(T∩bad k).card) →
        (∀ k T, IsAllowed H F T → |triSum (full k) T| ≤ 3*L*T.card) →
        (∀ k T, IsAllowed H F T → |w k T| ≤ 1) →
        ∀ B : Finset (Finset V), PairCodegreeBound B bankL → (∀ T ∈ B, T.card = 3) →
        ∀ (X : Type) [Fintype X] (e : V ↪ X) (Rprev : Finset (Finset X)) (Lprev : ℕ),
        PairCodegreeBound Rprev Lprev →
        ∃ ψ : Finset V → ℝ, IsDiffuseSeed (residual H R) F (2*C) ψ ∧
          (∀ T, ψ T ≠ 0 → IsAllowed (residual H R) F T) ∧
          (∀ T, IsAllowed (residual H R) F T →
            |ψ T-φ T| ≤ ExplicitSeed.seedPointwiseCost α C h*d/(Fintype.card V:ℝ)^2) ∧
        ∀ (ω : Type) [Fintype ω] (Yextra : ℕ → ω → Finset (Finset V) → ℝ),
        Fintype.card ω ≤ (Fintype.card V)^q →
        (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k S, 0 ≤ Yextra ℓ k S) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          (∀ k, |edgeSum (loc k) ((edges H\R)\P.biUnion triEdges)| ≤ τ*Fintype.card V*(bad k).card) ∧
          (∀ k, |edgeSum (full k) ((edges H\R)\P.biUnion triEdges)| ≤ τ*(Fintype.card V:ℝ)^2) ∧
          (∀ k, |(∑ T ∈ P, w k T)-(∑ T ∈ allowed H F, φ T*w k T)| ≤ (τ+τStat/2)*(Fintype.card V:ℝ)^2) ∧
          |(count P:ℝ)-target φ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 ∧
          (|(∑ T ∈ P, childPaddedWeight e Rprev Lprev T)-
             (∑ T ∈ allowed (residual H R) F, ψ T*childPaddedWeight e Rprev Lprev T)| ≤
            εAmbient*(∑ T ∈ allowed (residual H R) F, ψ T*childPaddedWeight e Rprev Lprev T)) ∧
          (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
            let A := allowed (residual H R) F
            let n := (Fintype.card V:ℝ)
            let θ := floorWeights A ψ n
            |PatternStatistics.statistic (completionWeight B) ℓ P-mixedMass A B θ ℓ| ≤
              (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A B θ ℓ)) ∧
          ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 → ∀ k : ω,
            floorTupleTestControl (allowed (residual H R) F) ψ P (Yextra ℓ k) ℓ := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let K := ExplicitSeed.seedPointwiseCost α C h
  have hK : 0 ≤ K := ExplicitSeed.seedPointwiseCost_nonneg h hα hC0
  let δ := targetPaymentBudget C K σ
  have hδ : 0 < δ := targetPaymentBudget_pos hC0 hK hσ
  have hδbounds := targetPaymentBudget_bounds hC0 hK hσ
  let εS := ExplicitSeed.seedExactBudget C α h
  have hεS : 0 < εS := by
    change 0 < RawReference.Explicit.seedBudget (1/C) C α h
    exact RawReference.Explicit.seedBudget_pos h (by positivity)
      (by rw [div_le_iff₀ hC0]; nlinarith only [hC]) hα
  let ε := min εS (min (α/4) (min δ (τStat/(2*(K+1)))))
  have hε : 0 < ε := lt_min hεS (lt_min (by positivity) (lt_min hδ (by positivity)))
  have hεSeed : ε ≤ εS := min_le_left _ _
  have hεGeometry : ε ≤ α/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεPasch : ε ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεMoment : (K+1)*ε ≤ τStat/2 := by
    have hh : ε ≤ τStat/(2*(K+1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp hh
    nlinarith only [hh']
  refine ⟨ε,hε,?_⟩
  intro η τ hη hτ
  obtain ⟨NP,hPack⟩ := joint_packing_with_triangle_monitors_pasch_bank_ambient_and_tuple_tests
    (2*C) (α/2) η τ L (σ/2) εAmbient q bankL (by linarith only [hC]) (by positivity)
      hη hτ hL (by positivity) hεAmbient
  refine ⟨max (ExplicitSeed.seedExactOrder C) (max NP 1),?_⟩
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ ι ν _ _ _ bad loc full w hcount hloc hfull hw B hBankL hBank X _ e Rprev Lprev hPrev
  have hnNat : 0 < Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hnNat
  have hRsub : R ⊆ edges H := by
    rw [←hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hdS : (d:ℝ) ≤ εS*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεSeed hn0.le)
  have hd3 : (d:ℝ) ≤ α/4*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεGeometry hn0.le)
  have hdδ : (d:ℝ) ≤ δ*Fintype.card V := hd.trans (mul_le_mul_of_nonneg_right hεPasch hn0.le)
  obtain ⟨ψ,hψ,hSupp,hClose⟩ := ExplicitSeed.seed_persistence_exact_with_pointwise_bound_explicit
    (F:=F) hC hα h H φ R D d ((le_max_left _ _).trans hn) hφ h4 hRsub hD hdeg hdS
  have hres3 := residual_commonNbrCond h3 R d hdeg hd3
  refine ⟨ψ,hψ,hSupp,hClose,?_⟩
  intro ω _ Yextra hω hExtra
  obtain ⟨P,hPsub,hP,hSparse,hLocal,hGlobal,hTriangles,hPasch,hAmbient,hMixed,hControls⟩ :=
    hPack (residual H R) F ψ ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) hψ hres3 X e Rprev Lprev hPrev
      κ ι ν bad loc full w hcount
      (fun k T hT => hloc k T (isAllowed_mono (subHost_le H _) rfl hT))
      (fun k T hT => hfull k T (isAllowed_mono (subHost_le H _) rfl hT))
      (fun k T hT => hw k T (isAllowed_mono (subHost_le H _) rfl hT)) B hBankL hBank
        ω Yextra hω hExtra
  have hPH : IsPacking H F P := ⟨fun T hT =>
    isAllowed_mono (subHost_le H _) rfl (hP.1 T hT),hP.2⟩
  have hJ : edges (residual H R) = edges H\R := Residual.edges_subHost_eq sdiff_subset
  have hPE : P.biUnion triEdges ⊆ edges H\R := by
    rw [←hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hDis : Disjoint (P.biUnion triEdges) R :=
    disjoint_left.mpr fun e he hR => (mem_sdiff.mp (hPE he)).2 hR
  have hPhys := isPhysical_sdiff (isPhysical_sdiff_of_decomposition h2 hD hRsub)
    (isPhysical_of_isDecomposition hPH.isDecomposition) hPE
  have hTransfer := protected_target_transfer hC0 hφ R hRsub K δ (d:ℝ) hK hδ.le hdδ
    hδbounds.1 (fun v => (show (degIn R v:ℝ) ≤ d by exact_mod_cast hdeg v).trans hdδ) hClose hn0
  have hPaid : |target ψ (allowed (residual H R) F)-target φ (allowed H F)| ≤
      (σ/2)*(Fintype.card V:ℝ)^2 := hTransfer.trans
    (mul_le_mul_of_nonneg_right hδbounds.2 (sq_nonneg _))
  have hClose' : ∀ T, IsAllowed (residual H R) F T → |ψ T-φ T| ≤ (K*ε)/Fintype.card V := by
    intro T hT
    calc
      _ ≤ K*d/(Fintype.card V:ℝ)^2 := hClose T hT
      _ ≤ K*(ε*Fintype.card V)/(Fintype.card V:ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hn0] <;> ring
  have hDegreeε (v : V) : (degIn R v:ℝ) ≤ ε*Fintype.card V :=
    (show (degIn R v:ℝ) ≤ d by exact_mod_cast hdeg v).trans hd
  have hRcard := TriangleMonitors.edge_card_le_of_degree_bound R ε hDegreeε
  refine ⟨P,hPH,hDis,hPhys,?_,?_,?_,?_,?_,hAmbient,hMixed,hControls⟩
  · simpa only [hJ] using hSparse
  · intro k
    simpa only [hJ] using hLocal k
  · intro k
    simpa only [hJ] using hGlobal k
  · intro k
    have hb := TriangleMonitors.triangle_seed_statistic_comparison hC0 hφ R hRsub (K*ε)
      (mul_nonneg hK hε.le) hnNat hClose' (w k) (hw k)
    have hb' : |(∑ T ∈ allowed (residual H R) F, ψ T*w k T)-
        (∑ T ∈ allowed H F, φ T*w k T)| ≤ (τStat/2)*(Fintype.card V:ℝ)^2 := by
      calc
        _ ≤ (K*ε)*(Fintype.card V:ℝ)^2+R.card := hb
        _ ≤ (K*ε)*(Fintype.card V:ℝ)^2+ε*(Fintype.card V:ℝ)^2 := add_le_add (le_refl _) hRcard
        _ = ((K+1)*ε)*(Fintype.card V:ℝ)^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hεMoment (sq_nonneg _)
    calc
      _ ≤ |(∑ T ∈ P, w k T)-(∑ T ∈ allowed (residual H R) F, ψ T*w k T)|+
          |(∑ T ∈ allowed (residual H R) F, ψ T*w k T)-(∑ T ∈ allowed H F, φ T*w k T)| := abs_sub_le _ _ _
      _ ≤ τ*(Fintype.card V:ℝ)^2+(τStat/2)*(Fintype.card V:ℝ)^2 := add_le_add (hTriangles k) hb'
      _ = _ := by ring
  · calc
      _ ≤ |(count P:ℝ)-target ψ (allowed (residual H R) F)|+
          |target ψ (allowed (residual H R) F)-target φ (allowed H F)| := abs_sub_le _ _ _
      _ ≤ (σ/2)*(Fintype.card V:ℝ)^2+(σ/2)*(Fintype.card V:ℝ)^2 := add_le_add hPasch hPaid
      _ = _ := by ring

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.protected_joint_packing_deferred_precisions
