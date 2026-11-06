module
public import RequestProject.TypedTriangle.PaschConcreteLayerReference
public import RequestProject.TypedTriangle.PaschConcreteLayerActivation
public import RequestProject.TypedTriangle.PaschChildExceptionTupleControl
public import RequestProject.TypedTriangle.PaschProtectedPackingUniformReserve
public import RequestProject.TypedTriangle.ExplicitResourceCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.ConcreteLayer
open S07V40 S07V42 S07V43 S07V44 S07V46 ProtectedBank AmbientBank
open CatalogNative CatalogNative.Explicit LocalizedCover BasalIncidence

private theorem inter_change_decEq {Y : Type*}
    (S E : Finset Y) (P : Finset Y → Prop) (d₁ d₂ : DecidableEq Y)
    (hh : P (@Inter.inter _ (@Finset.instInter _ d₁) S E)) :
    P (@Inter.inter _ (@Finset.instInter _ d₂) S E) := by
  cases Subsingleton.elim d₁ d₂
  exact hh

private theorem degree_sdiff_change_decEq {Y : Type*}
    (S E : Finset (Sym2 Y)) (v : Y) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 Y))
    (hh : (TypedTriangle.degIn (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) S E) v : ℝ) ≤ b) :
    (TypedTriangle.degIn (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) S E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hh

/-- A pair-codegree certificate on the actual embedded universe restricts
back to the same literal local family. -/
theorem pairCodegreeBound_of_mapConfiguration {X V : Type*} (ι : X ↪ V)
    (R : Finset (Finset X)) (L : ℕ) (hR : PairCodegreeBound (mapConfiguration ι R) L) :
    PairCodegreeBound R L := by
  intro x y hxy
  have hh := hR (ι x) (ι y) (fun h => hxy (ι.injective h))
  have hFilter : (mapConfiguration ι R).filter (fun T => ι x∈T ∧ ι y∈T)=
      mapConfiguration ι (R.filter (fun T => x∈T ∧ y∈T)) := by
    unfold mapConfiguration
    rw [filter_map]
    congr 1
    apply filter_congr
    intro T _
    exact and_congr (mem_map' ι) (mem_map' ι)
  rw [hFilter,mapConfiguration,card_map] at hh
  exact hh

/-- These are output certificates of ONE partial packing. In particular the
mixed tests use the entire local stock/withdrawal/bank universe, while the
ambient monitor and Bool extra tests keep the full previous universe. -/
structure MainPackingStatistics {X V I ν ω : Type} [Fintype X] [Fintype V]
    [Fintype ν] [Fintype ω]
    (H : Host X I) (F : Set (Multiset I)) (ι : X ↪ V)
    (φ ψ : Finset X → ℝ) (Removed : Finset (Sym2 X))
    (Rpast : Finset (Finset V)) (Lpast : ℕ) (Bfull P0 : Finset (Finset X))
    (w : ν → Finset X → ℝ) (Yextra : ℕ → ω → Finset (Finset X) → ℝ)
    (τStat σ εAmbient : ℝ) : Prop where
  complement_degree : ∀x,(degIn (edges H\P0.biUnion triEdges) x:ℝ) ≤ τStat*Fintype.card X
  triangles : ∀k,|(∑T∈P0,w k T)-(∑T∈allowed H F,φ T*w k T)| ≤ τStat*(Fintype.card X:ℝ)^2
  pasch : |(count P0:ℝ)-target φ (allowed H F)| ≤ σ*(Fintype.card X:ℝ)^2
  previous_relative :
    |(∑T∈P0,childPaddedWeight ι Rpast Lpast T)-
      (∑T∈allowed (residual H Removed) F,ψ T*childPaddedWeight ι Rpast Lpast T)| ≤
      εAmbient*(∑T∈allowed (residual H Removed) F,ψ T*childPaddedWeight ι Rpast Lpast T)
  mixed : ∀ℓ,1 ≤ ℓ → ℓ ≤ 3 →
    let A := allowed (residual H Removed) F
    let n := (Fintype.card X:ℝ)
    let θ := floorWeights A ψ n
    |PatternStatistics.statistic (completionWeight Bfull) ℓ P0-mixedMass A Bfull θ ℓ| ≤
      (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ:ℝ)*target θ A+mixedMass A Bfull θ ℓ)
  extras : ∀ℓ,1 ≤ ℓ → ℓ ≤ 4 → ∀k,
    floorTupleTestControl (allowed (residual H Removed) F) ψ P0 (Yextra ℓ k) ℓ

/-- Cardinality comes from the actual decompositions and run edge quota,
not from a Pasch-potential estimate. -/
theorem actual_bank_modes_card_le {V I Q C : Type} [Fintype V] [AddCommGroup Q] [Fintype C]
    {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub N : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (RichBank.Entry V C S.P)}
    (hInv : RichBank.Seeded.RunInv H F S Ub pay R0 N es) :
    (RichBank.modes es).card ≤ 2*(S.E*S.Bstar*N) := by
  have hOff := TypedTriangle.decomp_card hInv.history.local_history.off
  have hOn := TypedTriangle.decomp_card hInv.history.local_history.on
  have hEdge := card_le_card (RichBank.offEdges_subset_used es)
  have hUnion : (RichBank.modes es).card ≤ (RichBank.offFamily es).card+(RichBank.onFamily es).card :=
    card_union_le _ _
  calc
    _ ≤ 2*(RichBank.usedEdges es).card := by omega
    _ ≤ _ := Nat.mul_le_mul_left 2 hInv.edges

theorem same_layer_literal_ledger {X V I : Type} [Fintype X] [Fintype V]
    (H : Host X I) (F : Set (Multiset I)) (ι : X ↪ V)
    (D Ures Bbank P0 Ccover Dps Dclocal : Finset (Finset X))
    (Rpast : Finset (Finset V)) (Lpast : ℕ) (pay : ℝ)
    (hD : PairCodegreeBound D 1) (hU : PairCodegreeBound Ures 63)
    (hB : PairCodegreeBound Bbank 2) (hPast : PairCodegreeBound Rpast Lpast)
    (hDtri : ∀ Q ∈ D, Q.card = 3) (hUtri : ∀ Q ∈ Ures, Q.card = 3)
    (hBtri : ∀ Q ∈ Bbank, Q.card = 3) (hPastTri : ∀ Q ∈ Rpast, Q.card = 3)
    (hQ : IsPacking H F (P0∪Ccover)) (hDps : Dps ⊆ Ures)
    (hDc : mapConfiguration ι Dclocal ⊆ mapConfiguration ι Bbank)
    (hCost :
      (count ((Rpast∪mapConfiguration ι ((D∪Ures)∪Bbank))∪mapConfiguration ι P0 ∪
        mapConfiguration ι (((P0∪Ccover)∪Dps)∪Dclocal)) : ℝ) ≤
      count ((Rpast∪mapConfiguration ι ((D∪Ures)∪Bbank))∪mapConfiguration ι P0)+pay) :
    let Pre := Rpast∪mapConfiguration ι ((D∪Ures)∪Bbank)
    let Q := P0∪Ccover
    let Dpaid := (Q∪Dps)∪Dclocal
    let Next := Pre∪mapConfiguration ι Q
    let CoverFixed := Pre∪mapConfiguration ι P0
    PairCodegreeBound Pre (Lpast+66) ∧ (∀ T ∈ Pre, T.card = 3) ∧
    PairCodegreeBound Next (Lpast+67) ∧ (∀ T ∈ Next, T.card = 3) ∧
    mapConfiguration ι Dpaid ⊆ Next ∧
    Next = CoverFixed∪mapConfiguration ι Dpaid ∧
    (count Next : ℝ) ≤ count CoverFixed+pay := by
  intro Pre Q Dpaid Next CoverFixed
  have hFull : PairCodegreeBound ((D∪Ures)∪Bbank) 66 := (hD.union hU).union hB
  have hPre : PairCodegreeBound Pre (Lpast+66) :=
    hPast.union (pairCodegreeBound_mapConfiguration ι _ 66 hFull)
  have hQCodeg : PairCodegreeBound Q 1 := pairCodegreeBound_of_linear (packing_linear hQ)
  have hNext : PairCodegreeBound Next (Lpast+67) := by
    simpa only [Nat.add_assoc] using
      hPre.union (pairCodegreeBound_mapConfiguration ι Q 1 hQCodeg)
  have hFullTri : ∀ T ∈ (D∪Ures)∪Bbank, T.card = 3 := by
    intro T hT
    rcases mem_union.mp hT with hT | hT
    · rcases mem_union.mp hT with hT | hT
      · exact hDtri T hT
      · exact hUtri T hT
    · exact hBtri T hT
  have hPreTri : ∀ T ∈ Pre, T.card = 3 := by
    intro T hT
    rcases mem_union.mp hT with hT | hT
    · exact hPastTri T hT
    · obtain ⟨Q,hQ,rfl⟩ := mem_mapConfiguration.mp hT
      simpa only [card_map] using hFullTri Q hQ
  have hNextTri : ∀ T ∈ Next, T.card = 3 := by
    intro T hT
    rcases mem_union.mp hT with hT | hT
    · exact hPreTri T hT
    · obtain ⟨Q,hQmem,rfl⟩ := mem_mapConfiguration.mp hT
      simpa only [card_map] using (hQ.1 Q hQmem).1
  have hUPre : mapConfiguration ι Ures ⊆ Pre := by
    intro Q hQmem
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQmem
    exact mem_union_right _ (mem_mapConfiguration.mpr
      ⟨T,mem_union_left _ (mem_union_right _ hT),rfl⟩)
  have hBPre : mapConfiguration ι Bbank ⊆ Pre := by
    intro Q hQmem
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQmem
    exact mem_union_right _ (mem_mapConfiguration.mpr ⟨T,mem_union_right _ hT,rfl⟩)
  have hDpsNext : mapConfiguration ι Dps ⊆ Next := by
    intro Q hQmem
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQmem
    exact mem_union_left _ (hUPre (mem_mapConfiguration.mpr ⟨T,hDps hT,rfl⟩))
  have hDcNext : mapConfiguration ι Dclocal ⊆ Next :=
    (hDc.trans hBPre).trans subset_union_left
  have hPaidNext : mapConfiguration ι Dpaid ⊆ Next := by
    dsimp only [Dpaid]
    unfold mapConfiguration
    rw [map_union,map_union]
    exact union_subset (union_subset subset_union_right hDpsNext) hDcNext
  have hP0Next : mapConfiguration ι P0 ⊆ Next := by
    intro Q hQmem
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQmem
    exact mem_union_right _ (mem_mapConfiguration.mpr ⟨T,mem_union_left _ hT,rfl⟩)
  have hQPaid : mapConfiguration ι Q ⊆ mapConfiguration ι Dpaid := by
    unfold mapConfiguration
    exact map_subset_map.mpr (subset_union_left.trans subset_union_left)
  have hNextEq : Next = CoverFixed∪mapConfiguration ι Dpaid := by
    apply subset_antisymm
    · exact union_subset (subset_union_left.trans subset_union_left)
        (hQPaid.trans subset_union_right)
    · exact union_subset (union_subset subset_union_left hP0Next) hPaidNext
  refine ⟨hPre,hPreTri,hNext,hNextTri,hPaidNext,hNextEq,?_⟩
  rw [hNextEq]
  exact hCost

/-- The literal carrier used by the raw child profile and reference. -/
def referenceHost {X I : Type} (H : Host X I) (W : Finset X) : Host {x // x∈W} I :=
  ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩

def futureEdges {X I : Type} [Fintype X] (H : Host X I) (W : Finset X)
    (U : Finset {x // x∈W}) : Finset (Sym2 X) :=
  SampledResource.lift W (edges (referenceHost H W)∩triEdges U)

/-- The real input resources are bound once to one native bank, one reference,
one protected partial packing, one stock entry and one literal activation.
The reserve precision precedes all later sampling and packing precisions. -/
theorem concrete_same_bank_layer {I : Type} (F : Set (Multiset I))
    (C α τStat σ εAmbient : ℝ) (h : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hτStat : 0 < τStat) (hσ : 0 < σ) (hAmbient : 0 < εAmbient) :
    ∃ εReserve : ℝ,0 < εReserve ∧
    ∀ (βBank αRef a b ρFuture ηRef εRef γRef q εcap δcap : ℝ)
      (nRef t qStats : ℕ),
    0 < βBank → βBank ≤ α → 0 < γRef → 0 < q → 4*q ≤ εReserve →
    0 < εcap → εcap ≤ min (γRef/4) (1/4) → 0 < δcap →
    δcap ≤ min (ExplicitGeometry.deletionBudget βBank h) (S07V37.delOf (βBank/2) h) →
    Odd t → 3 ≤ t → Vortex.NakedReferenceAt F a b αRef ρFuture ηRef εRef γRef h nRef →
    let d := catalogDimension βBank h
    let c := catalogCoefficient βBank h
    let E := catalogColumn βBank h
    let Rc := bankCatalogRadius α βBank h
    let Lbank := bankCatalogSize α βBank h
    let Ecell := bankCellSize α βBank h
    let AM := S07V34.Explicit.paymentCost d (monR Rc E)
    let MM := S07V34.Explicit.monitorMagnitude d (monR Rc E)
    let KM := S07V34.Explicit.monitorDimension d (monR Rc E)
    let P := 2*gammaL AM MM Lbank
    let Bstar := 2*Lbank*P
    let Λ := physicalWeightMagnitude (α/2) (βBank/2) h d c MM
    let κBank := bankRoundRate α βBank εcap δcap h P
    let εBank := bankTolerance α βBank εcap h
    let γPay := StockEntry.Explicit.bankGamma (q/2) εBank
    let ηPay := StockEntry.Explicit.bankEta κBank (q/2) εBank (2*Ecell*Bstar)
    let δ := StockEntry.Explicit.monitorCap Λ ηPay KM
    ∀ (ρ τSel κStock u : ℝ),0 < ρ → 0 < τSel → 0 < κStock → 0 < u →
    ρ ≤ min δ (min (q/64) (γRef*q/64)) →
    τSel ≤ min δ (min (q/64) (γRef*q/64)) →
    ∃ N : ℕ,
    ∀ {X V : Type} [Fintype X] [Fintype V] (ι : X ↪ V)
      (H : Host X I) (Hambient : Host V I) (φ : Finset X → ℝ)
      (W Wcore : Finset X) (D DR DT Ures : Finset (Finset X))
      (R T : Finset (Sym2 X)) (Ufuture : Finset {x // x∈W})
      (μ : Finset {x // x∈W} → ℝ) (F0 : Finset (Sym2 V))
      (Rpast : Finset (Finset V)) (Lpast : ℕ),
    N ≤ Fintype.card X →
    (∀x y,H.G.Adj x y → Hambient.G.Adj (ι x) (ι y)) →
    (∀x,H.lab x=Hambient.lab (ι x)) →
    IsDiffuseSeed H F C φ → IsPhysical H F (edges H) → CommonNbrCond H F α → HingeCond H F α h →
    SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x∈Wcore}→X)) (H.lab ∘ Subtype.val) F βBank →
    SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x∈Wcore}→X)) (H.lab ∘ Subtype.val) F βBank h →
    Wcore ⊆ W → q*Fintype.card X/2 ≤ W.card → (W.card:ℝ) ≤ 2*q*Fintype.card X →
    (q/2)*Fintype.card X/2 ≤ Wcore.card →
    CommonNbrCond (referenceHost H W) F αRef → HingeCond (referenceHost H W) F αRef h →
    (∀Q,IsAllowed (referenceHost H W) F Q → a/W.card ≤ μ Q ∧ μ Q ≤ b/W.card) →
    (∀e∈edges (referenceHost H W),|bdry (referenceHost H W) F μ e-1| ≤ εRef) →
    (Ufuture.card:ℝ) ≤ ρFuture*W.card →
    IsDecomposition H F (cover D) D → IsDecomposition H F R DR → IsDecomposition H F T DT →
    Disjoint (cover D) T → Disjoint R (cover D∪T) →
    Disjoint (cover D) (futureEdges H W Ufuture) → Disjoint R (futureEdges H W Ufuture) →
    Disjoint T (futureEdges H W Ufuture) →
    liftEdges ι ((((cover D∪R)∪T)∪futureEdges H W Ufuture)) ⊆ F0 →
    (∀x,(degIn (pullEdges ι F0) x:ℝ) ≤ bankProtectionBudget α βBank h*Wcore.card) →
    (∀x,(degIn (cover D) x:ℝ) ≤ ρ*Fintype.card X) →
    (∀x,(degIn R x:ℝ) ≤ τSel*Fintype.card X) →
    (∀x,(degIn T x:ℝ) ≤ min (q/64) (γRef*q/64)*Fintype.card X) →
    (∀x y,H.G.Adj x y → κStock*Fintype.card X ≤ (good H F D x y).card) →
    PairCodegreeBound (mapConfiguration ι Ures) 63 → (∀Q∈Ures,Q.card=3) →
    PairCodegreeBound Rpast Lpast → (∀Q∈Rpast,Q.card=3) →
    S07V45.CorePathContract H.G H.lab F Wcore t →
    (∀ L : Finset (Sym2 X),L ⊆ cover D → IsPhysical H F L →
      ∃ Ps Y Dps,R∪L=Ps∪Y ∧ Disjoint Ps Y ∧ IsDecomposition H F Ps Dps ∧ Dps ⊆ Ures ∧
        (∀e∈Y,∀x∈e,x∈Wcore) ∧ (∀x,(SelSimul.edeg Y x:ℝ) ≤ τSel*Fintype.card X) ∧ IsPhysical H F Y) →
    ∀ (ν : Type) [Fintype ν] (w : ν → Finset X → ℝ),
    ((Lbank+2)*KM+Fintype.card ν:ℕ) ≤ (Fintype.card X)^qStats →
    (∀k Q,IsAllowed H F Q → |w k Q| ≤ 1) →
    ∃ (Bbank : Finset (Finset X)) (E0 : Finset (Sym2 {x // x∈W}))
      (D0 : Finset (Finset {x // x∈W})),
    let Eref := SampledResource.lift W E0
    let Removed := (((cover D∪R)∪T)∪(Bbank.biUnion triEdges))∪Eref
    let Bfull := (D∪Ures)∪Bbank
    let RbankSeed := Rpast∪mapConfiguration ι (D∪Ures)
    let Pre := Rpast∪mapConfiguration ι Bfull
    let Nbank := ⌊κBank*(Wcore.card:ℝ)^2⌋₊
    let payBank := Ambient.orderRatio ι*catalogCellPotentialCost α βBank h d c E
      (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h) (Lpast+66)
    PairCodegreeBound Bbank 2 ∧ (∀Q∈Bbank,Q.card=3) ∧
    Bbank.card ≤ 2*(Ecell*Bstar*Nbank) ∧
    (count Pre:ℝ) ≤ count RbankSeed+(Bstar*Nbank:ℕ)*payBank ∧
    PairCodegreeBound Pre (Lpast+66) ∧ (∀Q∈Pre,Q.card=3) ∧
    IsDecomposition (referenceHost H W) F E0 D0 ∧
    edges (referenceHost H W)∩triEdges Ufuture ⊆ E0 ∧
    (∀x,(degIn (edges (referenceHost H W)\E0) x:ℝ) ≤ ηRef*W.card) ∧
    ∃ ψ : Finset X → ℝ,IsDiffuseSeed (residual H Removed) F (2*C) ψ ∧
      CommonNbrCond (residual H Removed) F (α/2) ∧
      (∀Q,ψ Q ≠ 0 → IsAllowed (residual H Removed) F Q) ∧
      (∀Q,IsAllowed (residual H Removed) F Q →
        |ψ Q-φ Q| ≤ ExplicitSeed.seedPointwiseCost α C h*εReserve/Fintype.card X) ∧
    ∀ (ω : Type) [Fintype ω] (Yextra : ℕ → ω → Finset (Finset X) → ℝ),
    Fintype.card ω ≤ (Fintype.card X)^qStats →
    (∀ℓ,1 ≤ ℓ → ℓ ≤ 4 → ∀k S,0 ≤ Yextra ℓ k S) →
    ∃ (P0 Ccover Dps Dclocal : Finset (Finset X)) (Ytot : Finset (Sym2 X)),
    let Q := P0∪Ccover
    let Dpaid := (Q∪Dps)∪Dclocal
    let Rnext := Pre∪mapConfiguration ι Q
    IsPacking H F P0 ∧ IsPacking H F Q ∧
    MainPackingStatistics H F ι φ ψ Removed Pre (Lpast+66) Bfull P0 w Yextra τStat σ εAmbient ∧
    Ytot ⊆ edges H ∧ Ytot ⊆ childEdges H.G Wcore ∧ SparseEdge.ind Ytot ∈ LamCore H.G H.lab F Wcore ∧
    Disjoint Eref Ytot ∧ Disjoint T (Eref∪Ytot) ∧
    IsDecomposition H F (edges H\(T∪(Eref∪Ytot))) Dpaid ∧ P0 ⊆ Dpaid ∧
    PairCodegreeBound Rnext (Lpast+67) ∧ (∀Q∈Rnext,Q.card=3) ∧
    mapConfiguration ι Dpaid ⊆ Rnext ∧
    (count Rnext:ℝ) ≤ count (Pre∪mapConfiguration ι P0)+
      u*Fintype.card V*Fintype.card X*((Lpast+68:ℕ):ℝ)^3 := by
  obtain ⟨εRaw,hεRaw,hPackReserve⟩ := protected_joint_packing_uniform_reserve F
    C α τStat σ εAmbient h hC hα hτStat hσ hAmbient
  let εReserve := min εRaw (min (α/4) (τStat/2))
  have hReserve : 0 < εReserve := lt_min hεRaw (lt_min (by positivity) (by positivity))
  refine ⟨εReserve,hReserve,?_⟩
  intro βBank αRef a b ρFuture ηRef εRef γRef q εcap δcap nRef t qStats
    hβ hβα hγRef hq hqReserve hεcap hεCap hδcap hδBound ht ht3 hReference
  dsimp only
  let d := catalogDimension βBank h
  let c := catalogCoefficient βBank h
  let E := catalogColumn βBank h
  let Rc := bankCatalogRadius α βBank h
  let Lbank := bankCatalogSize α βBank h
  let Ecell := bankCellSize α βBank h
  let AM := S07V34.Explicit.paymentCost d (monR Rc E)
  let MM := S07V34.Explicit.monitorMagnitude d (monR Rc E)
  let KM := S07V34.Explicit.monitorDimension d (monR Rc E)
  let P := 2*gammaL AM MM Lbank
  let Bstar := 2*Lbank*P
  let Λ := physicalWeightMagnitude (α/2) (βBank/2) h d c MM
  let κBank := bankRoundRate α βBank εcap δcap h P
  let εBank := bankTolerance α βBank εcap h
  let γPay := StockEntry.Explicit.bankGamma (q/2) εBank
  let ηPay := StockEntry.Explicit.bankEta κBank (q/2) εBank (2*Ecell*Bstar)
  let δ := StockEntry.Explicit.monitorCap Λ ηPay KM
  have hΛ : 0 < Λ := physicalWeightMagnitude_pos _ _ _ _ _ _
  have hκBank : 0 < κBank := bankRoundRate_pos h P hα hβ hεcap hδcap
  have hεBank : 0 < εBank := bankTolerance_pos h hα hβ hεcap
  have hCat : Fintype.card (Cat d Rc)=Lbank := by
    simpa only [d,Rc,Lbank,bankCatalogSize] using card_Cat d Rc
  obtain ⟨hγPay,hηPay,hδ,hηκ,hCapacity,hqn,hKB,hBankLarge⟩ :=
    StockEntry.Explicit.native_bank_scale_cap_explicit κBank (q/2) εBank Λ (2*Ecell*Bstar) KM
      hκBank (by positivity) hεBank hΛ.le
  intro ρ τSel κStock u hρ hτSel hκStock hu hρCap hτCap
  let ηCover := δ/2
  let τMom := min (δ/2) (τStat/2)
  let ηPack := min (τStat/2) (min (δ/2) (min (StockEntry.Explicit.coverDownBudget κStock ηCover) (κStock*u/2)))
  have hηCover : 0 < ηCover := by dsimp [ηCover]; positivity
  have hτMom : 0 < τMom := lt_min (by positivity) (by positivity)
  have hCoverBudget : 0 < StockEntry.Explicit.coverDownBudget κStock ηCover :=
    StockEntry.Explicit.coverDownBudget_pos hκStock hηCover
  have hηPack : 0 < ηPack := lt_min (by positivity) (lt_min (by positivity) (lt_min hCoverBudget (by positivity)))
  have hηPackStat : ηPack ≤ τStat/2 := min_le_left _ _
  have hτMomStat : τMom ≤ τStat/2 := min_le_right _ _
  have hPackCover : ηPack ≤ StockEntry.Explicit.coverDownBudget κStock ηCover :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hPackCost : ηPack ≤ κStock*u/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨NP,hPack⟩ := hPackReserve Λ hΛ qStats 66 ηPack τMom hηPack hτMom
  let nWeights := nativeWeightOrder α βBank (q/2) h
  let nBank := StockEntry.Explicit.bankOrder κBank (q/2)
  let nFactory := ⌈4*(bankOrder α βBank εcap δcap h P:ℝ)/q⌉₊
  let nRefCut := ⌈2*(nRef:ℝ)/q⌉₊
  let nLarge := ⌈4/(γRef*q)⌉₊
  let nCover := StockEntry.Explicit.coverDownOrder κStock ηCover
  let N0 := NP+nWeights+nBank+nFactory+nRefCut+nLarge+nCover+1
  refine ⟨N0,?_⟩
  intro X V _ _ ι H Hambient φ W Wcore D DR DT Ures R T Ufuture μ F0 Rpast Lpast
    hn hAdj hLab hSeed hPhys h3 h4 hCore3 hCore4 hCore hWlo hWhi hWcore
    hRef3 hRef4 hμ hLoad hFutureCard hD hR hT hDT hRDT hDFuture hRFuture hTFuture
    hProtected hF0cap hDcap hRcap hTcap hSupply hUCGmap hUThree hPastCG hPastThree hPath hMode
    ν _ w hCount hw
  dsimp only [N0] at hn
  have hnP : NP ≤ Fintype.card X := by omega
  have hnWeights : nWeights ≤ Fintype.card X := by omega
  have hnBank : nBank ≤ Fintype.card X := by omega
  have hnFactory : nFactory ≤ Fintype.card X := by omega
  have hnRefCut : nRefCut ≤ Fintype.card X := by omega
  have hnLarge : nLarge ≤ Fintype.card X := by omega
  have hnCover : nCover ≤ Fintype.card X := by omega
  have hnPos : 0 < (Fintype.card X:ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card X)
  have hFactoryW : bankOrder α βBank εcap δcap h P ≤ Wcore.card := by
    have hc := (Nat.le_ceil (4*(bankOrder α βBank εcap δcap h P:ℝ)/q)).trans (Nat.cast_le.mpr hnFactory)
    have hh := (div_le_iff₀ hq).mp hc
    have hCoreReal := hWcore
    exact_mod_cast (show (bankOrder α βBank εcap δcap h P:ℝ) ≤ Wcore.card by nlinarith only [hh,hCoreReal])
  have hnRef : nRef ≤ W.card := by
    have hc := (Nat.le_ceil (2*(nRef:ℝ)/q)).trans (Nat.cast_le.mpr hnRefCut)
    have hh := (div_le_iff₀ hq).mp hc
    exact_mod_cast (show (nRef:ℝ) ≤ W.card by nlinarith only [hh,hWlo])
  have hLarge : 2 ≤ γRef*W.card := by
    have hc := (Nat.le_ceil (4/(γRef*q))).trans (Nat.cast_le.mpr hnLarge)
    have hh := (div_le_iff₀ (mul_pos hγRef hq)).mp hc
    have hwScaled := mul_le_mul_of_nonneg_left hWlo hγRef.le
    nlinarith only [hh,hwScaled]
  have hDpack : IsPacking H F D := ⟨hD.1,hD.2.1⟩
  have hDCG : PairCodegreeBound D 1 := pairCodegreeBound_of_linear (packing_linear hDpack)
  have hUCG := pairCodegreeBound_of_mapConfiguration ι Ures 63 hUCGmap
  let RbankSeed := Rpast∪mapConfiguration ι (D∪Ures)
  have hSeedCG : PairCodegreeBound RbankSeed (Lpast+64) := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hPastCG.union
      (pairCodegreeBound_mapConfiguration ι (D∪Ures) (1+63) (hDCG.union hUCG))
  obtain ⟨C0,CZ,hqBank,hqLow,hzBank,hzCap,hGen,hChain,hRunCap,es,hInv,hValid,hBankAvoid,hBankDeg,
    hBankAmbientCG,hLocalBankCount,hExtBankCG,hExtBankCount,hSat,hSatCard⟩ :=
    prepared_native_ambient_bank α βBank h hα hβ P εcap δcap hεcap hδcap
      ι H Hambient F hAdj hLab Wcore hFactoryW h3 h4 hCore3 hCore4 F0 hF0cap RbankSeed (Lpast+64) hSeedCG
  let qm := ⌊εBank*Wcore.card/2⌋₊
  let zm := ⌊bankDeletionBudget α βBank δcap h*Wcore.card⌋₊
  let Sloc := protect (childSetting C0 Rc P qm Ecell zm) (pullEdges ι F0)
  let S := liftSetting ι Sloc
  let Nbank := ⌊κBank*(Wcore.card:ℝ)^2⌋₊
  have hStar : S.Bstar=Bstar := by
    change 2*Fintype.card (Cat d Rc)*P=Bstar
    rw [hCat]
  have hChain' : ChainBound S Lbank := by
    change ChainBound S (Fintype.card (Cat d Rc)) at hChain
    rwa [hCat] at hChain
  obtain ⟨Doff,Don,hOff,hOn,hOffMap,hOnMap,hModesMap,hBbankCG,hBbankCount,hBbankExternal⟩ :=
    actual_bank_local_modes H Hambient F Wcore C0 ι hLab F0 RbankSeed es hInv
  let Bbank := Doff∪Don
  let Bank := pullEdges ι (RichBank.usedEdges es)
  have hBankCover : Bbank.biUnion triEdges=Bank := by
    dsimp only [Bbank,Bank]
    rw [union_biUnion,hOff.2.2,hOn.2.2]
    apply union_eq_right.mpr
    intro e he
    exact mem_preimage.mpr (RichBank.offEdges_subset_used es (mem_preimage.mp he))
  have hBbankThree : ∀Q∈Bbank,Q.card=3 := by
    intro Q hQ
    rcases mem_union.mp hQ with hh | hh
    · exact (hOff.1 Q hh).1
    · exact (hOn.1 Q hh).1
  have hBbankCard : Bbank.card ≤ 2*(Ecell*Bstar*Nbank) := by
    have hc := actual_bank_modes_card_le hInv
    rw [←hModesMap,mapConfiguration,card_map] at hc
    change Bbank.card ≤ 2*(Ecell*S.Bstar*Nbank) at hc
    rwa [hStar] at hc
  let Bfull := (D∪Ures)∪Bbank
  let Pre := Rpast∪mapConfiguration ι Bfull
  have hFullCG : PairCodegreeBound Bfull 66 := by
    simpa only [Nat.reduceAdd] using (hDCG.union hUCG).union hBbankCG
  have hPreCG : PairCodegreeBound Pre (Lpast+66) :=
    hPastCG.union (pairCodegreeBound_mapConfiguration ι Bfull 66 hFullCG)
  have hFullThree : ∀Q∈Bfull,Q.card=3 := by
    intro Q hQ
    rcases mem_union.mp hQ with hDU | hB
    · rcases mem_union.mp hDU with hQD | hQU
      · exact (hD.1 Q hQD).1
      · exact hUThree Q hQU
    · exact hBbankThree Q hB
  have hPreThree : ∀Q∈Pre,Q.card=3 := by
    intro Q hQ
    rcases mem_union.mp hQ with hp | hp
    · exact hPastThree Q hp
    · obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hp
      simpa only [card_map] using hFullThree A hA
  have hPreEq : Pre=RbankSeed∪RichBank.modes es := by
    dsimp only [Pre,Bfull,RbankSeed]
    change Rpast∪((D∪Ures)∪Bbank).map (Finset.mapEmbedding ι).toEmbedding=
      (Rpast∪mapConfiguration ι (D∪Ures))∪RichBank.modes es
    rw [map_union,←union_assoc]
    exact congrArg (fun Z => (Rpast∪mapConfiguration ι (D∪Ures))∪Z) hModesMap
  have hPreCount : (count Pre:ℝ) ≤ count RbankSeed+(Bstar*Nbank:ℕ)*
      (Ambient.orderRatio ι*catalogCellPotentialCost α βBank h d c E
        (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h) (Lpast+66)) := by
    rw [hPreEq]
    change (count (RbankSeed∪RichBank.modes es):ℝ) ≤ count RbankSeed+(S.Bstar*Nbank:ℕ)*
      (Ambient.orderRatio ι*catalogCellPotentialCost α βBank h d c E
        (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h) (Lpast+64+2)) at hExtBankCount
    simpa only [hStar,Nat.add_assoc,Nat.reduceAdd] using hExtBankCount
  have hBankProtected : Disjoint Bank (((cover D∪R)∪T)∪futureEdges H W Ufuture) := by
    rw [disjoint_left]
    intro e he hf
    exact disjoint_left.mp hBankAvoid (mem_preimage.mp he) (hProtected (mem_map.mpr ⟨e,hf,rfl⟩))
  have hBankDis : Disjoint Bank ((cover D∪R)∪T) := hBankProtected.mono_right subset_union_left
  have hFuture : Disjoint (futureEdges H W Ufuture) (((cover D∪R)∪T)∪Bank) :=
    disjoint_union_right.mpr ⟨disjoint_union_right.mpr
      ⟨disjoint_union_right.mpr ⟨hDFuture.symm,hRFuture.symm⟩,hTFuture.symm⟩,
      (hBankProtected.mono_right subset_union_right).symm⟩
  have hBankCap : ∀x,(degIn Bank x:ℝ) ≤ εBank*Wcore.card := by
    intro x
    exact (Nat.cast_le.mpr (pull_degree_le ι (RichBank.usedEdges es) x)).trans (hBankDeg (ι x)).le
  have hεRef : εBank ≤ γRef/4 := (min_le_right _ _).trans (hεCap.trans (min_le_left _ _))
  have hεQuarter : εBank ≤ 1/4 := (min_le_right _ _).trans (hεCap.trans (min_le_right _ _))
  have hρRef : ρ ≤ γRef*q/64 := hρCap.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτRef : τSel ≤ γRef*q/64 := hτCap.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρSmall : ρ ≤ q/64 := hρCap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτSmall : τSel ≤ q/64 := hτCap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRateSum : ρ+τSel+γRef*q/64 ≤ γRef*q/8 := by nlinarith only [hρRef,hτRef,mul_pos hγRef hq]
  obtain ⟨E0,D0,dTotal,hFutureIn,hRefEdges,hRefDec,hRefAvoid,hTotalDec,hTotalDeg,hTotalCap,hRefHole,hRefGraph⟩ :=
    same_bank_reference_with_literal_reserve H F W Wcore D DR DT Don R T Bank hD hR hT hOn hDT hRDT hBankDis
      a b αRef ρFuture ηRef εRef γRef q εBank ρ τSel (γRef*q/64) εReserve h nRef hReference
      hq hγRef hεBank.le hεRef hεQuarter hRateSum hWlo hWhi hCore hLarge hqReserve
      hDcap hRcap (fun x => (hTcap x).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))
      hBankCap
      (fun x => (hDcap x).trans (mul_le_mul_of_nonneg_right hρSmall (Nat.cast_nonneg _)))
      (fun x => (hRcap x).trans (mul_le_mul_of_nonneg_right hτSmall (Nat.cast_nonneg _)))
      (fun x => (hTcap x).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
      μ Ufuture hnRef hRef3 hRef4 hμ hLoad hFutureCard (by
        exact inter_change_decEq (edges (referenceHost H W)) (triEdges Ufuture)
          (fun Z => Disjoint (SampledResource.lift W Z) (((cover D∪R)∪T)∪Bank))
          (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b))
          (@Sym2.instDecidableEq _ (Classical.decEq _))
          (by simpa only [futureEdges] using hFuture))
  let Eref := SampledResource.lift W E0
  let Removed := (((cover D∪R)∪T)∪Bank)∪Eref
  let Rtail := ((R∪T)∪Bank)∪Eref
  have hSplit : Removed=cover D∪Rtail := by dsimp only [Removed,Rtail]; ac_rfl
  have hzGeom : (zm:ℝ) ≤ ExplicitGeometry.deletionBudget βBank h*Wcore.card :=
    hzCap.trans (mul_le_mul_of_nonneg_right (hδBound.trans (min_le_left _ _)) (Nat.cast_nonneg _))
  have hGeomBudget := (ExplicitGeometry.deletionBudget_spec hβ h).2.2 (Nat.cast_nonneg Wcore.card) hzGeom
  have hzDel : (zm:ℝ) ≤ S07V37.delOf (βBank/2) h*Wcore.card :=
    hzCap.trans (mul_le_mul_of_nonneg_right (hδBound.trans (min_le_right _ _)) (Nat.cast_nonneg _))
  have hzCore : (zm:ℝ) ≤ coreDelta βBank h*Wcore.card := hzBank.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))) (Nat.cast_nonneg _))
  obtain ⟨Mon,Fm,loc,full,hLocRep,hFullRep,hLocTri,hFullTri⟩ :=
    actual_bank_monitor_weights α βBank (q/2) h d c E Rc hα hβ (by positivity) hβα
      ι H Hambient F Wcore C0 S hInv hqBank hRunCap hGen hnWeights hWcore h3 h4 hCore3 hCore4 hzCore
      (by change (zm:ℝ) ≤ βBank/2*Wcore.card
          nlinarith only [hGeomBudget.1]) hGeomBudget.2 hzDel
  let bad : Fin (Lbank+1)×Fin KM → Finset X := fun k => pullVertices ι (RichBank.Actual.Zstrat S es Nbank (k.1.val+1))
  let locF : Fin (Lbank+1)×Fin KM → Sym2 X → ℝ := fun k => loc k.1.val k.2
  have hTestCount : ((Fintype.card (Fin (Lbank+1)×Fin KM)+Fintype.card (Fin KM)+Fintype.card ν:ℕ):ℝ) ≤
      (Fintype.card X:ℝ)^qStats := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact_mod_cast (show (Lbank+1)*KM+KM+Fintype.card ν ≤ (Fintype.card X)^qStats by nlinarith only [hCount])
  have hTotalRaw : (dTotal:ℝ) ≤ εRaw*Fintype.card X := hTotalCap.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  obtain ⟨ψ,hψ,hSupp,hClose,hContinue⟩ := hPack H φ Removed _ dTotal hnP hSeed hPhys h3 h4 hTotalDec hTotalDeg hTotalRaw
    (Fin (Lbank+1)×Fin KM) (Fin KM) ν bad locF full w hTestCount
    (fun k Q hQ => hLocTri k.1.val k.2 Q hQ) hFullTri hw Bfull hFullCG hFullThree
    V ι Pre (Lpast+66) hPreCG
  have hRes3 : CommonNbrCond (residual H Removed) F (α/2) :=
    TypedTriangle.residual_commonNbrCond h3 Removed dTotal hTotalDeg
      (hTotalCap.trans (mul_le_mul_of_nonneg_right
        ((min_le_right _ _).trans (min_le_left _ _)) (Nat.cast_nonneg _)))
  have hKSeed : 0 ≤ ExplicitSeed.seedPointwiseCost α C h :=
    ExplicitSeed.seedPointwiseCost_nonneg h hα (lt_of_lt_of_le zero_lt_one hC)
  have hCloseSmall : ∀Q,IsAllowed (residual H Removed) F Q →
      |ψ Q-φ Q| ≤ ExplicitSeed.seedPointwiseCost α C h*εReserve/Fintype.card X := by
    intro Q hQ
    calc
      _ ≤ ExplicitSeed.seedPointwiseCost α C h*dTotal/(Fintype.card X:ℝ)^2 := hClose Q hQ
      _ ≤ ExplicitSeed.seedPointwiseCost α C h*(εReserve*Fintype.card X)/(Fintype.card X:ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hTotalCap hKSeed) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hnPos] <;> ring
  refine ⟨Bbank,E0,D0,?_⟩
  rw [hBankCover]
  refine ⟨hBbankCG,hBbankThree,hBbankCard,hPreCount,hPreCG,hPreThree,hRefDec,?_,?_,
    ψ,hψ,hRes3,hSupp,hCloseSmall,?_⟩
  · exact inter_change_decEq (edges (referenceHost H W)) (triEdges Ufuture)
      (fun Z => Z ⊆ E0)
      (@Sym2.instDecidableEq _ (Classical.decEq _))
      (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b))
      (by simpa only [referenceHost] using hFutureIn)
  · intro x
    exact degree_sdiff_change_decEq (edges (referenceHost H W)) E0 x (ηRef*W.card)
      (@Sym2.instDecidableEq _ (Classical.decEq _))
      (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b))
      (by simpa only [referenceHost] using hRefHole x)
  intro ω _ Yextra hω hExtra
  obtain ⟨P0,hP0,hP0Dis,hPhysicalLeft,hSparseP0,hLocalP0,hFullP0,hTrianglesP0,hPaschP0,
    hAmbientP0,hMixedP0,hControlsP0⟩ := hContinue ω Yextra hω hExtra
  have hResidEdges : edges (residual H Removed)=edges H\Removed := Residual.edges_subHost_eq sdiff_subset
  have hRemovedDegree : ∀x,(degIn Removed x:ℝ) ≤ εReserve*Fintype.card X :=
    fun x => (Nat.cast_le.mpr (hTotalDeg x)).trans hTotalCap
  have hOriginalSparse : ∀x,(degIn (edges H\P0.biUnion triEdges) x:ℝ) ≤ τStat*Fintype.card X := by
    have hh := TriangleMonitors.original_complement_degree Removed P0 εReserve ηPack hRemovedDegree
      (fun x => by rw [hResidEdges]; exact hSparseP0 x)
    intro x
    exact (hh x).trans (mul_le_mul_of_nonneg_right
      (by have hr : εReserve ≤ τStat/2 := (min_le_right _ _).trans (min_le_right _ _)
          linarith only [hηPackStat,hr]) (Nat.cast_nonneg _))
  have hTriangles : ∀k,|(∑Q∈P0,w k Q)-(∑Q∈allowed H F,φ Q*w k Q)| ≤ τStat*(Fintype.card X:ℝ)^2 := by
    intro k
    exact (hTrianglesP0 k).trans (mul_le_mul_of_nonneg_right
      (by linarith only [hτMomStat]) (sq_nonneg _))
  have hStats : MainPackingStatistics H F ι φ ψ Removed Pre (Lpast+66) Bfull P0 w Yextra τStat σ εAmbient :=
    ⟨hOriginalSparse,hTriangles,hPaschP0,hAmbientP0,hMixedP0,hControlsP0⟩
  have hStockE : cover D ⊆ edges H := CorePaid.basal_subset_edges ⟨D,hD⟩
  have hStockBank : Disjoint (cover D) Bank :=
    (hBankDis.mono_right (subset_union_left.trans subset_union_left)).symm
  have hStockRef : Disjoint (cover D) Eref :=
    (hRefAvoid.mono_right ((subset_union_left.trans subset_union_left).trans subset_union_left)).symm
  have hStockTail : Disjoint (cover D) Rtail := disjoint_union_right.mpr
    ⟨disjoint_union_right.mpr ⟨disjoint_union_right.mpr
      ⟨(hRDT.mono_right subset_union_left).symm,hDT⟩,hStockBank⟩,hStockRef⟩
  have hP0Stock : Disjoint (P0.biUnion triEdges) (cover D) := hP0Dis.mono_right (by rw [hSplit]; exact subset_union_left)
  have hP0Tail : Disjoint (P0.biUnion triEdges) Rtail := hP0Dis.mono_right (by rw [hSplit]; exact subset_union_right)
  let J0 := edges H\(Rtail∪P0.biUnion triEdges)
  have hStockJ : cover D ⊆ J0 := by
    intro e he
    exact mem_sdiff.mpr ⟨hStockE he,fun hm => by
      rcases mem_union.mp hm with ht | hp
      · exact disjoint_left.mp hStockTail he ht
      · exact disjoint_left.mp hP0Stock hp he⟩
  have hRawEq : J0\cover D=(edges H\Removed)\P0.biUnion triEdges := by
    rw [hSplit]
    dsimp only [J0]
    ext e
    simp only [mem_sdiff,mem_union]
    tauto
  have hJSplit : J0=cover D∪((edges H\Removed)\P0.biUnion triEdges) := by
    rw [←hRawEq]
    exact (union_sdiff_of_subset hStockJ).symm
  have hJPhys : IsPhysical H F J0 := by
    rw [hJSplit]
    apply isPhysical_union (isPhysical_of_isDecomposition hD) hPhysicalLeft
    rw [←hRawEq]
    exact sdiff_disjoint.symm
  let dUncovered := ⌊ηPack*Fintype.card X⌋₊
  have hUncoveredDeg : ∀x,((J0\cover D).filter (fun e => x∈e)).card ≤ dUncovered := by
    intro x
    rw [hRawEq]
    exact Nat.le_floor (hSparseP0 x)
  have hUncoveredDiag : ∀e∈J0\cover D,¬e.IsDiag := by
    intro e he
    have heH : e∈edges H := (mem_sdiff.mp (mem_sdiff.mp he).1).1
    exact H.G.not_isDiag_of_mem_edgeSet (mem_filter.mp heH).2
  have hUncoveredCard : (J0\cover D).card ≤ Fintype.card X*dUncovered := by
    have hh := Envelope.two_card_le_card_mul_degree (J0\cover D) hUncoveredDiag hUncoveredDeg
    omega
  have hFloorPack : (dUncovered:ℝ) ≤ ηPack*Fintype.card X := Nat.floor_le (by positivity)
  have hSparseCover : (dUncovered:ℝ) ≤ StockEntry.Explicit.coverDownBudget κStock ηCover*Fintype.card X :=
    hFloorPack.trans (mul_le_mul_of_nonneg_right hPackCover (Nat.cast_nonneg _))
  let CoverFixed := Pre∪mapConfiguration ι P0
  have hCoverCG : PairCodegreeBound CoverFixed (Lpast+67) := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hPreCG.union
      (pairCodegreeBound_mapConfiguration ι P0 1 (pairCodegreeBound_of_linear (packing_linear hP0)))
  have hUFixed : mapConfiguration ι Ures ⊆ CoverFixed := by
    intro Q hQ
    obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hQ
    exact mem_union_left _ (mem_union_right _ (mem_mapConfiguration.mpr
      ⟨A,mem_union_left _ (mem_union_right _ hA),rfl⟩))
  obtain ⟨Ccover,Ps,Y,Dps,hC,hQ,hQR,hLeft,hLeftPhys,hMove,hPY,hDps,hDpsU,hYInside,hYDeg,hYPhys,hCJ,hCdeg,hQCost⟩ :=
    same_packing_ambient_stock_transition ι H F D P0 hP0 R Rtail J0 rfl hP0Tail hStockJ hJPhys
      κStock ηCover hκStock hηCover (fun x y _ hxy => hSupply x y hxy)
      dUncovered hUncoveredDeg hnCover hUncoveredCard hSparseCover Ures Wcore τSel hMode
      CoverFixed (Lpast+67) hCoverCG subset_union_right hUFixed
  have hPriceRate : 2*ηPack/κStock ≤ u := (div_le_iff₀ hκStock).mpr (by nlinarith only [hPackCost])
  have hSmallCard : ((J0\cover D).card:ℝ) ≤ ηPack*(Fintype.card X:ℝ)^2 := by
    have hc : ((J0\cover D).card:ℝ) ≤ Fintype.card X*(dUncovered:ℝ) := by exact_mod_cast hUncoveredCard
    have hd := mul_le_mul_of_nonneg_left hFloorPack hnPos.le
    have hh : (Fintype.card X:ℝ)*dUncovered ≤ ηPack*(Fintype.card X:ℝ)^2 := by convert hd using 1 <;> ring
    exact hc.trans hh
  let payCover := u*Fintype.card V*Fintype.card X*((Lpast+68:ℕ):ℝ)^3
  have hPrice : 2*((J0\cover D).card:ℝ)*((Fintype.card V:ℝ)/Fintype.card X)*((Lpast+68:ℕ):ℝ)^3/κStock ≤ payCover := by
    have hc := mul_le_mul_of_nonneg_right hSmallCard
      (by positivity : 0 ≤ 2*((Fintype.card V:ℝ)/Fintype.card X)*((Lpast+68:ℕ):ℝ)^3/κStock)
    calc
      _ ≤ 2*(ηPack*(Fintype.card X:ℝ)^2)*((Fintype.card V:ℝ)/Fintype.card X)*((Lpast+68:ℕ):ℝ)^3/κStock := by
        convert hc using 1 <;> ring
      _ = (2*ηPack/κStock)*Fintype.card V*Fintype.card X*((Lpast+68:ℕ):ℝ)^3 := by
        field_simp [ne_of_gt hnPos,ne_of_gt hκStock] <;> ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hPriceRate
          (by positivity : 0 ≤ (Fintype.card V:ℝ)*Fintype.card X*((Lpast+68:ℕ):ℝ)^3)
        convert hh using 1 <;> ring
  have hQCostPaid : (count (CoverFixed∪mapConfiguration ι ((P0∪Ccover)∪Dps)):ℝ) ≤ count CoverFixed+payCover := by
    have hc := hQCost
    simp only [Nat.add_assoc,Nat.reduceAdd] at hc
    linarith only [hc,hPrice]
  have hFixedBank : RichBank.modes es ⊆ CoverFixed := by
    intro Q hQ
    rw [←hModesMap] at hQ
    obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hQ
    exact mem_union_left _ (mem_union_right _ (mem_mapConfiguration.mpr ⟨A,mem_union_right _ hA,rfl⟩))
  have hRB : Disjoint R Bank := (hBankDis.mono_right (subset_union_right.trans subset_union_left)).symm
  have hTB : Disjoint T Bank := (hBankDis.mono_right subset_union_right).symm
  have hLiftDR : liftEdges ι (cover D∪R) ⊆ F0 := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    exact hProtected (mem_map.mpr ⟨f,mem_union_left _ (mem_union_left _ hf),rfl⟩)
  have hqLow' : εBank*(Wcore.card:ℝ)/4 ≤ (qm:ℝ) := by
    change εBank/4*(Wcore.card:ℝ) ≤ (qm:ℝ) at hqLow
    simpa only [div_mul_eq_mul_div] using hqLow
  have hQN : γPay*Fintype.card X ≤ qm := hqn _ _ _ hWcore hqLow' 
  have hCapActual : ηPay*((2*Ecell*(childSetting C0 Rc P qm Ecell zm).Bstar:ℕ):ℝ)/γPay ≤ 1 := by
    change ηPay*((2*Ecell*S.Bstar:ℕ):ℝ)/γPay ≤ 1
    rw [hStar]
    exact hCapacity
  have hCompact : (KM:ℝ)*(τMom+(3*Λ/2)*(ηCover+2*ρ+2*τSel)) ≤ ηPay :=
    hKB τMom ηCover ρ τSel
      ((min_le_left _ _).trans (by linarith only [hδ]))
      (by dsimp only [ηCover]; linarith only [hδ])
      (hρCap.trans (min_le_left _ _)) (hτCap.trans (min_le_left _ _))
  have hFinalCap : 1+ηPay*(Fintype.card X:ℝ)^2 ≤ 2*Nbank :=
    StockEntry.final_bank_capacity_of_sample_size κBank (q/2) ηPay (Fintype.card X) Wcore.card
      hκBank (by positivity) hWcore hηκ (hBankLarge _ hnBank)
  have hLocMom : ∀ℓ ≤ Lbank,∀j,|edgeSum (loc ℓ j) (J0\cover D)| ≤
      τMom*Fintype.card X*(pullVertices ι (RichBank.Actual.Zstrat S es Nbank (ℓ+1))).card := by
    intro ℓ hℓ j
    rw [hRawEq]
    exact hLocalP0 (⟨⟨ℓ,Nat.lt_succ_iff.mpr hℓ⟩,j⟩)
  have hFullMom : ∀j,|edgeSum (full j) (J0\cover D)| ≤ τMom*(Fintype.card X:ℝ)^2 := by
    intro j
    rw [hRawEq]
    exact hFullP0 j
  obtain ⟨Ytot,Yb,Dclocal,hYtot,hYtotE,hYtotCore,hLam,hErefY,hTerminal,hPaid,hP0Paid,hDcBank,hPaidCost⟩ :=
    activate_same_packing_paid_partition H Hambient F Wcore C0 ι hLab F0 RbankSeed es hInv
      D P0 Ccover Dps R T Eref J0 Ps Y hD ⟨DR,hR⟩ (hRDT.mono_right subset_union_left)
      (hRDT.mono_right subset_union_right) hRB hTB hLiftDR hRefAvoid rfl hC hQ hQR hStockJ hCJ hLeft
      hMove hPY hDps hYInside hYPhys hPath ht ht3 hqBank hChain' hRunCap hGen Mon Fm loc full
      hLocRep hFullRep Λ ηCover τMom ρ τSel γPay ηPay hΛ.le hγPay hηPay.le hLocTri hFullTri
      hLocMom hFullMom hDcap hRcap hCdeg hQN hCapActual (by exact le_rfl) hCompact
      (fun _ => hFinalCap) CoverFixed payCover hFixedBank hQCostPaid
  have hDcB : mapConfiguration ι Dclocal ⊆ mapConfiguration ι Bbank := by rw [hModesMap]; exact hDcBank
  obtain ⟨_,_,hNextCG,hNextThree,hPaidNext,_,hNextCount⟩ :=
    same_layer_literal_ledger H F ι D Ures Bbank P0 Ccover Dps Dclocal Rpast Lpast payCover
      hDCG hUCG hBbankCG hPastCG (fun Q hQ => (hD.1 Q hQ).1) hUThree hBbankThree hPastThree
      hQ hDpsU hDcB hPaidCost
  exact ⟨P0,Ccover,Dps,Dclocal,Ytot,hP0,hQ,hStats,hYtotE,hYtotCore,hLam,hErefY,hTerminal,hPaid,hP0Paid,
    hNextCG,hNextThree,hPaidNext,hNextCount⟩

end TypedTriangle.Pasch.ConcreteLayer
#print axioms TypedTriangle.Pasch.ConcreteLayer.pairCodegreeBound_of_mapConfiguration

#print axioms TypedTriangle.Pasch.ConcreteLayer.actual_bank_modes_card_le
#print axioms TypedTriangle.Pasch.ConcreteLayer.same_layer_literal_ledger
#print axioms TypedTriangle.Pasch.ConcreteLayer.concrete_same_bank_layer
