module
public import RequestProject.TypedTriangle.ExplicitExactComplement
public import RequestProject.TypedTriangle.ExplicitMonitoredPackingCore
public import RequestProject.TypedTriangle.ExplicitPhysicalMonitorWeights
public import RequestProject.TypedTriangle.VortexActualBankNativePartitionResult
public import RequestProject.TypedTriangle.VortexPartitionBankActivation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open CatalogNative StockEntry BasalIncidence S07V42 LocalizedCover
theorem g34_native_partition_result_on_fixed_prepared_window_explicit {I : Type}
    (F : Set (Multiset I)) (C α κ ηPack τ Λ qCore ρ τSel : ℝ)
    (h t : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
    (hη : 0 < ηPack) (hτ : 0 < τ) (hΛ : 0 < Λ)
    (ht : Odd t) (ht3 : 3 ≤ t) :
    ∀ {V : Type} [Fintype V]
      (H : Host V I) (ψ : Finset V → ℝ)
      (W : Finset V) (D DT : Finset (Finset V))
      (R T Bank E : Finset (Sym2 V)),
      fixedPackingOrder C α κ ηPack τ Λ h ≤ Fintype.card V →
      let B := (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E
      let Jhost := subHost H (edges H \ B)
      S07V45.CorePathContract H.G H.lab F W t →
      IsDiffuseSeed Jhost F C ψ → IsPhysical Jhost F (edges Jhost) →
      CommonNbrCond Jhost F α → HingeCond Jhost F α h →
      IsPhysical H F (edges H) →
      IsDecomposition H F (cover D) D →
      Basal H F R → IsDecomposition H F T DT →
      Basal H F Bank → Basal H F E →
      Disjoint (cover D) T → Disjoint R (cover D ∪ T) →
      Disjoint Bank ((cover D ∪ R) ∪ T) →
      Disjoint E (((cover D ∪ R) ∪ T) ∪ Bank) →
      (∀ u v, H.G.Adj u v →
        κ * Fintype.card V ≤ (good H F D u v).card) →
      (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
        ∃ Ps Y : Finset (Sym2 V), R ∪ L = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          IsPhysical H F Y) →
      (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤
        qCore / 64 * Fintype.card V) →
      (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤
        ρ * Fintype.card V) →
      (∀ v, (SelSimul.edeg R v : ℝ) ≤ τSel * Fintype.card V) →
      G34NativePartitionResult H F W D R B qCore ρ ηPack τ Λ τSel := by
  intro V _ H ψ W D DT R T Bank E hn
  dsimp only
  intro hPath hSeed hPhysJ h3 h4 hPhys hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply hMode hDq hDcap hRd
  intro κi ι _ _ bad loc full hCount hLoc hFull
  have hCount' : ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
      Fintype.card V := by simpa using hCount
  obtain ⟨DR,Q,Rtail,Ps,Y,x,d,q,hDR,hDtail,hEq,hQ,hQR,hRes,
    hPhysRes,hMove,hPY,hPs,hYphys,hYin,hYdeg,hx,hCharge,hLoad,
    hLocOut,hFullOut⟩ :=
    positive_packing_on_fixed_prepared_window_explicit F C α κ ηPack τ Λ τSel h t
      hC hα hκ hη hτ hΛ ht ht3 H ψ W D DT R T Bank E hn hPath hSeed hPhysJ h3 h4 hPhys
      hD hR hT hBank hE hDT hRDT hBankDis hEDis hSupply hMode
      κi ι bad loc full hCount' hLoc hFull
  have hRL : Disjoint R (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
    apply disjoint_left.mpr
    intro e heR heL
    apply disjoint_left.mp hRDT heR
    exact mem_union.mpr (Or.inl (hRes heL))
  have hStockDeg : ∀ v,
      (((cover D).filter (fun e => v ∈ e)).card : ℝ) ≤
        ρ * Fintype.card V := by
    intro v
    simpa only [SparseEdge.degIn] using hDcap v
  have hRDeg : ∀ v,
      ((R.filter (fun e => v ∈ e)).card : ℝ) ≤
        τSel * Fintype.card V := by
    intro v
    simpa only [SelSimul.edeg] using hRd v
  have hJDeg : ∀ v,
      (((edges H \ (Rtail ∪ Q.biUnion triEdges)).filter
        (fun e => v ∈ e)).card : ℝ) ≤ ρ * Fintype.card V := by
    intro v
    have hc := Finset.card_le_card
      (Finset.filter_subset_filter (p := fun e => v ∈ e) hRes)
    have hc' : (((edges H \ (Rtail ∪ Q.biUnion triEdges)).filter
        (fun e => v ∈ e)).card : ℝ) ≤
        (((cover D).filter (fun e => v ∈ e)).card : ℝ) := by
      exact_mod_cast hc
    exact hc'.trans (hStockDeg v)
  have hLocY : ∀ k, |edgeSum (loc k) Y| ≤
      τ * Fintype.card V * (bad k).card +
      (3 * Λ * (bad k).card) *
        (((2*d+2*q : ℕ) : ℝ) + ρ * Fintype.card V +
          2 * (τSel * Fintype.card V) + ρ * Fintype.card V) / 2 := by
    intro k
    exact g4_actual_positive_moment_budget H F D hD R
      (edges H \ (Rtail ∪ Q.biUnion triEdges)) Ps Y hRL hPY hMove
      hR hPs (ρ * Fintype.card V) (τSel * Fintype.card V)
      (ρ * Fintype.card V) ((2*d+2*q : ℕ) : ℝ)
      (τ * Fintype.card V * (bad k).card) Λ hΛ.le
      hStockDeg hRDeg hJDeg (bad k) (loc k) (hLoc k) (hLocOut k)
  have hFullY : ∀ j, |edgeSum (full j) Y| ≤
      τ * (Fintype.card V : ℝ)^2 +
      (3 * Λ * Fintype.card V) *
        (((2*d+2*q : ℕ) : ℝ) + ρ * Fintype.card V +
          2 * (τSel * Fintype.card V) + ρ * Fintype.card V) / 2 := by
    intro j
    have htri : ∀ A, IsAllowed H F A →
        |triSum (full j) A| ≤
          3 * Λ * (A ∩ (univ : Finset V)).card := by
      intro A hA
      simpa using hFull j A hA
    simpa only [card_univ] using
      (g4_actual_positive_moment_budget H F D hD R
        (edges H \ (Rtail ∪ Q.biUnion triEdges)) Ps Y hRL hPY hMove
        hR hPs (ρ * Fintype.card V) (τSel * Fintype.card V)
        (ρ * Fintype.card V) ((2*d+2*q : ℕ) : ℝ)
        (τ * (Fintype.card V : ℝ)^2) Λ hΛ.le
        hStockDeg hRDeg hJDeg univ (full j) htri
        (by simpa only [card_univ] using hFullOut j))
  exact ⟨DR,Q,Rtail,Ps,Y,hD,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR,hRL,hDq,hDcap,hRd,hMove,hPY,hPs,hYin,hYdeg,hYphys,
    ⟨x,hx,hCharge⟩,d,q,hLoad,hLocOut,hFullOut,hLocY,hFullY⟩
def paidGeometryDensity (α : ℝ) (h : ℕ) : ℝ :=
  min (α/2) (S07V49.hingeConstB α 1 h)

def nativePartitionOrder (C α κ ηPack τ Λ : ℝ) (h : ℕ) : ℕ :=
  max (complementOrder C α h)
    (fixedPackingOrder (2*C) (paidGeometryDensity α h) κ ηPack τ Λ (2*h-3))

theorem native_partition_result_after_actual_bank_reference_explicit {I : Type}
    (F : Set (Multiset I)) (C α : ℝ) (h : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h) :
    ∀ (κ ηPack τ Λ qCore ρ τSel : ℝ) (t : ℕ),
        0 < κ → 0 < ηPack → 0 < τ → 0 < Λ → Odd t → 3 ≤ t →
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (W Wcore : Finset V) (D DT : Finset (Finset V))
        (R T Bank : Finset (Sym2 V))
        (E₀ : Finset (Sym2 {x // x ∈ W}))
        (D₀ : Finset (Finset {x // x ∈ W})) (dU : ℕ),
        nativePartitionOrder C α κ ηPack τ Λ h ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) →
        CommonNbrCond H F α → HingeCond H F α h →
        S07V45.CorePathContract H.G H.lab F Wcore t →
        IsDecomposition H F (cover D) D → Basal H F R →
        IsDecomposition H F T DT → Basal H F Bank →
        Disjoint (cover D) T → Disjoint R (cover D ∪ T) →
        Disjoint Bank ((cover D ∪ R) ∪ T) →
        IsDecomposition
          (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
            Host {x // x ∈ W} I) F E₀ D₀ →
        let U := ((cover D ∪ R) ∪ T) ∪ Bank
        Disjoint (SampledResource.lift W E₀) U →
        Basal H F (U ∪ SampledResource.lift W E₀) →
        (∀ v, SparseEdge.degIn U v ≤ dU) →
        ((dU + W.card : ℕ) : ℝ) ≤ complementBudget C α h * Fintype.card V →
        (∀ u v, H.G.Adj u v →
          κ * Fintype.card V ≤ (good H F D u v).card) →
        (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
          ∃ Ps Y : Finset (Sym2 V), R ∪ L = Ps ∪ Y ∧
            Disjoint Ps Y ∧ Basal H F Ps ∧
            (∀ e ∈ Y, ∀ v ∈ e, v ∈ Wcore) ∧
            (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
            IsPhysical H F Y) →
        (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤
          qCore / 64 * Fintype.card V) →
        (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤ ρ * Fintype.card V) →
        (∀ v, (SelSimul.edeg R v : ℝ) ≤ τSel * Fintype.card V) →
        G34NativePartitionResult H F Wcore D R (U ∪ SampledResource.lift W E₀) qCore ρ ηPack τ Λ τSel := by
  let nExact := complementOrder C α h
  intro κ ηPack τ Λ qCore ρ τSel t hκ hη hτ hΛ ht ht3
  let α' := min (α / 2) (S07V49.hingeConstB α 1 h)
  have hα' : 0 < α' := lt_min (by positivity)
    (S07V49.hingeConstB_pos hα (by norm_num) (by omega))
  let nFixed := fixedPackingOrder (2*C) α' κ ηPack τ Λ (2*h-3)
  intro V _ H φ W Wcore D DT R T Bank E₀ D₀ dU hn hSeed hPhys h3 h4
    hPath hD hR hT hBank hDT hRdis hBankdis hEDec U hAvoid hBasal
    hUdeg hSmall hSupply hMode hDq hDcap hRdeg
  change max nExact nFixed ≤ Fintype.card V at hn
  have hE : E₀ ⊆ edges
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I) := by
    intro e he
    obtain ⟨S,hS,heS⟩ := hEDec.exists_mem he
    exact triEdges_subset_edges (hEDec.1 S hS) heS
  obtain ⟨ψ,hSeedJ,hPhysJ,h3J,h4J⟩ :=
    exact_complement_after_sampled_reference_explicit F C α h hC hα hh H φ W U E₀ dU ((le_max_left _ _).trans hn)
      hSeed hPhys h3 h4 hBasal hE hUdeg hSmall
  have h3J' : CommonNbrCond
      (subHost H (edges H \ (U ∪ SampledResource.lift W E₀))) F α' :=
    commonNbrCond_mono h3J (min_le_left _ _)
  have h4J' : HingeCond
      (subHost H (edges H \ (U ∪ SampledResource.lift W E₀))) F α' (2*h-3) :=
    hingeCond_mono h4J (min_le_right _ _)
  have hLift : Basal H F (SampledResource.lift W E₀) :=
    SampledResource.basal_lift H F W ⟨D₀,hEDec⟩
  exact g34_native_partition_result_on_fixed_prepared_window_explicit F (2*C) α' κ ηPack τ Λ
    qCore ρ τSel (2*h-3) t (by linarith) hα' hκ hη hτ hΛ ht ht3 H ψ Wcore D DT R T Bank (SampledResource.lift W E₀)
    ((le_max_right _ _).trans hn) hPath hSeedJ hPhysJ h3J' h4J'
    hPhys hD hR hT hBank hLift hDT hRdis hBankdis hAvoid
    hSupply hMode hDq hDcap hRdeg
#print axioms g34_native_partition_result_on_fixed_prepared_window_explicit
#print axioms native_partition_result_after_actual_bank_reference_explicit
end TypedTriangle.Vortex.Explicit
namespace TypedTriangle.CatalogNative.Explicit
open BasalIncidence S07V40 S07V42 S07V43 S07V44 S07V46 S07V47 LocalizedCover
theorem activate_partition_bank_after_g34_result_explicit (α β qCore : ℝ)
    (h d c E Rc A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hqCore : 0 < qCore)
    (hβα : β ≤ α) :
    let Λ := physicalWeightMagnitude (α/2) (β/2) h d c M
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W : Finset V)
        (D : Finset (Finset V)) (R B : Finset (Sym2 V))
        (C0 : CoreCompression H.G H.lab F W d c E)
        (P q Ecell z N L : ℕ)
        (Mon : ∀ Z : Finset V, CatalogGen C0 Rc Z →
          PhysicalMonitors C0 Rc Z A M K)
        (Fm : FullMonitor C0 Rc A M K)
        (hP : P = 2 * gammaL A M L)
        (F0 : Finset (Sym2 V))
        (hF0 : cover D ∪ R ⊆ F0)
        (hBank : MacroBank (protSetting C0 Rc P q Ecell z F0) L N)
        (hgen : ∀ j, CatalogGen C0 Rc
          (Zstrat (protSetting C0 Rc P q Ecell z F0) N j))
        (γ η ηPack τ ρ τSel : ℝ),
        nativeWeightOrder α β qCore h ≤ Fintype.card V →
        qCore * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        (L+2)*K ≤ Fintype.card V →
        0 ≤ η → 0 < γ →
        γ * Fintype.card V ≤ q →
        η * ((2 * Ecell *
          (childSetting C0 Rc P q Ecell z).Bstar : ℕ) : ℝ) / γ ≤ 1 →
        (K : ℝ) *
          (τ + (3 * Λ / 2) * (ηPack + 2 * ρ + 2 * τSel)) ≤ η →
        ((protSetting C0 Rc P q Ecell z F0).K
          (Zr (protSetting C0 Rc P q Ecell z F0) N) ≠ ⊥ →
          1 + η * (Fintype.card V : ℝ) ^ 2 ≤ 2 * N) →
        G34NativePartitionResult H F W D R B qCore ρ ηPack τ Λ τSel →
        ∃ (DR Q : Finset (Finset V)) (Rtail Ps Y : Finset (Sym2 V))
          (x : MCore H.G H.lab F W) (J : ℕ),
          IsDecomposition H F Rtail DR ∧
          Disjoint (cover D) Rtail ∧ cover D ∪ Rtail = B ∧
          IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) Rtail ∧
          (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
          IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
          Basal H F R ∧ Disjoint R (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
          R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧ IsPhysical H F Y ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          Y ⊆ F0 ∧ Y ⊆ edges H ∧
          J ≤ L ∧ (x : Sym2 V → ℤ) = ind Y ∧
          ProtOutcome C0 Rc P q Ecell z F0 N J x ∧
          ((protSetting C0 Rc P q Ecell z F0).K
            (Zr (protSetting C0 Rc P q Ecell z F0) N) ≠ ⊥ → J = L) := by
  intro magnitudeTarget
  let Λ := physicalWeightMagnitude (α/2) (β/2) h d c M
  have hΛ : 0 < Λ := physicalWeightMagnitude_pos _ _ _ _ _ _
  intro V I _ H F W D R B C0 P q Ecell z N L Mon Fm hP F0 hF0 hBank hgen
    γ η ηPack τ ρ τSel hn hWlo h3 h4 hCore3 hCore4
    hzCore hz3 hz4 hzDel hsize hη hγ hqn hcapacity hKB hN hNative
  let S := protSetting C0 Rc P q Ecell z F0
  let MonS : ∀ ℓ, PhysicalMonitors C0 Rc (Zstrat S N (ℓ+1)) A M K :=
    fun ℓ => Mon _ (hgen (ℓ+1))
  obtain ⟨loc,full,hLocRep,hFullRep,hLocTri,hFullTri⟩ :=
    choose_weights_on_actual_bank_core_explicit α β qCore h d c E Rc A M K
      hα hβ hqCore hβα H F W C0 S N L z MonS Fm hBank rfl hn hWlo h3 h4
      hCore3 hCore4 hzCore hz3 hz4 hzDel
  let badF : Fin (L+1) × Fin K → Finset V :=
    fun k => Zstrat S N (k.1.val+1)
  let locF : Fin (L+1) × Fin K → Sym2 V → ℝ :=
    fun k => loc k.1.val k.2
  have hCount :
      ((Fintype.card (Fin (L+1) × Fin K) + Fintype.card (Fin K) : ℕ) : ℝ) ≤
        Fintype.card V := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast (show (L+1)*K+K ≤ Fintype.card V from by nlinarith only [hsize])
  have hTri : ∀ k T, IsAllowed H F T →
      |triSum (locF k) T| ≤ 3 * Λ * (T ∩ badF k).card := by
    intro k T hT
    exact hLocTri k.1.val k.2 T hT
  obtain ⟨DR,Q,Rtail,Ps,Y,hD,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR,hRL,hDq,hDcap,hRd,hMove,hPY,hPs,hYin,hYdeg,hYphys,
    hCharge,d',q',hLoad,hLocOut,hFullOut,hLocY,hFullY⟩ :=
    hNative (Fin (L+1) × Fin K) (Fin K) badF locF full
      (by simpa using hCount) hTri hFullTri
  obtain ⟨x,hxY,hx⟩ := hCharge
  let load : ℝ := ((2*d'+2*q' : ℕ) : ℝ)
  have hLoc : ∀ ℓ ≤ L, ∀ j,
      |edgeSum (loc ℓ j) Y| ≤
        τ * Fintype.card V * (Zstrat S N (ℓ+1)).card +
        (3 * Λ * (Zstrat S N (ℓ+1)).card) *
          (load + ρ*Fintype.card V + 2*(τSel*Fintype.card V) +
            ρ*Fintype.card V) / 2 := by
    intro ℓ hℓ j
    exact hLocY ⟨⟨ℓ, Nat.lt_succ_iff.mpr hℓ⟩,j⟩
  obtain ⟨J,hJ,hOutcome,hFinish,_⟩ :=
    activate_bank_from_native_packing_moments C0 Rc A M K P q Ecell z N L
      Mon Fm hP F0 Y hBank hgen (Fintype.card V) Λ η γ ηPack τ ρ τSel load
      hΛ.le hη hγ hqn hcapacity hLoad hKB x hxY hx loc full
      (fun ℓ hg j => by simpa only [S,MonS] using hLocRep ℓ j x)
      (fun j => hFullRep j x) hLoc hFullY hN
  have hYDR : Y ⊆ cover D ∪ R := by
    intro e he
    have hm : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ he
    rcases mem_union.mp hm with heR | heL
    · exact mem_union_right _ heR
    · exact mem_union_left _ (hRes heL)
  have hYE : Y ⊆ edges H := hYDR.trans (Finset.union_subset
    (CorePaid.basal_subset_edges ⟨D,hD⟩) (CorePaid.basal_subset_edges hR))
  exact ⟨DR,Q,Rtail,Ps,Y,x,J,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR,hRL,hMove,hPY,hPs,hYphys,hYin,hYdeg,hYDR.trans hF0,hYE,hJ,hxY,
    hOutcome,hFinish⟩
#print axioms activate_partition_bank_after_g34_result_explicit
end TypedTriangle.CatalogNative.Explicit
