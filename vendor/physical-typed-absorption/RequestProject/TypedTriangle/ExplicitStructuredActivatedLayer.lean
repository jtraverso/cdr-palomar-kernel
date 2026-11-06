module
public import RequestProject.TypedTriangle.ExplicitStructuredBank
public import RequestProject.TypedTriangle.ExplicitNativePartition
public import RequestProject.TypedTriangle.ExplicitMonitorAllocation
public import RequestProject.TypedTriangle.VortexStructuredActivatedNakedLayerBeforeReference
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open CatalogNative CorePaid BasalIncidence SelSimul S07V40 S07V42 S07V43 S07V44 S07V47

def layerTerminalBudget (α C βBank γRef q αPool εRoute : ℝ) (h t : ℕ) : ℝ :=
  min (resourceTerminalBudget α C h αPool (q/2) εRoute
      (CatalogNative.Explicit.bankProtectionBudget α βBank h/2) t)
    (min γRef 1*q/64)

theorem layerTerminalBudget_pos (α C βBank γRef q αPool εRoute : ℝ) (h t : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hβ : 0 < βBank) (hγ : 0 < γRef)
    (hq : 0 < q) (hPool : 0 < αPool) (hRoute : 0 < εRoute) :
    0 < layerTerminalBudget α C βBank γRef q αPool εRoute h t := by
  have hBank := CatalogNative.Explicit.bankProtectionBudget_pos h hα hβ
  have hStock := (resource_parameters_pos α C h αPool (q/2) εRoute
    (CatalogNative.Explicit.bankProtectionBudget α βBank h/2) t 1 1 hα hC hPool
    (by positivity) hRoute (by positivity) (by norm_num) (by norm_num)).2.1
  exact lt_min hStock (by have := lt_min hγ one_pos; positivity)

def layerThreshold (α C βBank γRef q αPool εRoute : ℝ) (h t nRef : ℕ) : ℕ :=
  let εOuter := complementBudget C α h
  let γStock := resourceStockBudget α C
  let ηBank := CatalogNative.Explicit.bankProtectionBudget α βBank h
  let d := CatalogNative.Explicit.catalogDimension βBank h
  let c := CatalogNative.Explicit.catalogCoefficient βBank h
  let E := CatalogNative.Explicit.catalogColumn βBank h
  let Rc := CatalogNative.Explicit.bankCatalogRadius α βBank h
  let Lbank := CatalogNative.Explicit.bankCatalogSize α βBank h
  let Ecell := CatalogNative.Explicit.bankCellSize α βBank h
  let AM := S07V34.Explicit.paymentCost d (S07V44.monR Rc E)
  let MM := S07V34.Explicit.monitorMagnitude d (S07V44.monR Rc E)
  let KM := S07V34.Explicit.monitorDimension d (S07V44.monR Rc E)
  let P := 2*S07V46.gammaL AM MM Lbank
  let δgeom := ExplicitGeometry.deletionBudget βBank h
  let δcap := min δgeom (min (coreDelta βBank h) (S07V37.delOf (βBank/2) h))
  let γ := min γRef 1
  let κBank := preparedBankRoundRate α βBank (γ/4) δcap h P
  let εBank := CatalogNative.Explicit.bankTolerance α βBank (γ/4) h
  let Λ := CatalogNative.Explicit.physicalWeightMagnitude (α/2) (βBank/2) h d c MM
  let Bstatic := 2*Ecell*(2*Lbank*P)
  let γPay := StockEntry.Explicit.bankGamma (q/2) εBank
  let ηPay := StockEntry.Explicit.bankEta κBank (q/2) εBank Bstatic
  let δ := StockEntry.Explicit.monitorCap Λ ηPay KM
  let εPack := δ/2
  let ρcap := min εPack (min (q/128) (γ*q/64))
  let τcap := min εPack (min (q/64) (γ*q/64))
  let ρ := resourceInputBudget αPool (q/2) εRoute (ηBank/2) t ρcap τcap
  let κStock := BasalIncidence.Explicit.rawStockCompletion α ρ
  let τR := resourceOutputBudget (q/2) (ηBank/2) τcap
  let nResource := stockBankOrder α C βBank (γ/4) δcap αPool (q/2) εRoute h P t ρcap τcap
  let nNative := nativePartitionOrder C α κStock εPack εPack Λ h
  let nWeights := CatalogNative.Explicit.nativeWeightOrder α βBank (q/2) h
  let nBank := StockEntry.Explicit.bankOrder κBank (q/2)
  max nResource (max nNative (max nWeights (max nBank
    (max ((Lbank+2)*KM) (max ⌈2*(nRef:ℝ)/q⌉₊ ⌈4/(γ*q)⌉₊)))))

theorem structured_activated_naked_layer_before_reference_explicit {I : Type}
    (F : Set (Multiset I)) (α C βBank βRef : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hβBank : 0 < βBank)
    (hβα : βBank ≤ α) (hh : 6 ≤ h) :
    let εOuter := complementBudget C α h
    let γStock := resourceStockBudget α C
    let ηBank := CatalogNative.Explicit.bankProtectionBudget α βBank h
      ∀ (a b ρFuture ηRef εRef γRef : ℝ) (nRef : ℕ), 0 < γRef →
      NakedReferenceAt F a b βRef ρFuture ηRef εRef γRef h nRef →
      ∀ q : ℝ, 0 < q → 4*q ≤ εOuter →
      ∀ (αPool εRoute : ℝ) (t : ℕ),
        0 < αPool → 0 < εRoute → Odd t → 3 ≤ t →
        let θT := layerTerminalBudget α C βBank γRef q αPool εRoute h t
        let n₀ := layerThreshold α C βBank γRef q αPool εRoute h t nRef
        ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
          (W : Finset V) (A : Finset (Survivors (univ \ W)))
          (U : Finset {x // x ∈ W}) (T : Finset (Sym2 V))
          (DT : Finset (Finset V)) (dT dS : ℕ) (μ : Finset {x // x ∈ W} → ℝ),
          let W0 := W \ liftVertexSet (univ \ W) A
          letI : DecidableEq {x // x ∈ W} := Classical.decEq _
          let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
          let S := SampledResource.lift W (edges JW ∩ triEdges U)
          n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
          CommonNbrCond H F α → HingeCond H F α h →
          q*Fintype.card V/2 ≤ W.card → (W.card:ℝ) < 2*q*Fintype.card V →
          (q/2)*Fintype.card V/2 ≤ W0.card →
          (∀ u v : V, u ≠ v → ∀ k : I,
            ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
            (q/2)*αPool*Fintype.card V/2 ≤ ((commonNbrs H k u v) ∩ W0).card) →
          S07V27.RouteProp H.G H.lab F t εRoute W0 →
          CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F βBank →
          HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F βBank h →
          CommonNbrCond JW F βRef → HingeCond JW F βRef h →
          (∀ Q, IsAllowed JW F Q → a/W.card ≤ μ Q ∧ μ Q ≤ b/W.card) →
          (∀ e ∈ edges JW, |bdry JW F μ e-1| ≤ εRef) →
          (U.card:ℝ) ≤ ρFuture*W.card →
          Disjoint W0 (U.image Subtype.val) →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ γStock*Fintype.card V →
          (dS:ℝ) ≤ (ηBank/2)*W0.card →
          IsDecomposition H F T DT → Disjoint T S →
          (∀ v, degIn T v ≤ dT) → (dT:ℝ) ≤ θT*Fintype.card V →
          ∃ (E₀ : Finset (Sym2 {x // x ∈ W}))
            (D₀ : Finset (Finset {x // x ∈ W})) (Ytot : Finset (Sym2 V)),
            IsDecomposition JW F E₀ D₀ ∧ edges JW ∩ triEdges U ⊆ E₀ ∧
            (∀ v, (SparseEdge.degIn (edges JW \ E₀) v:ℝ) ≤ ηRef*W.card) ∧
            Ytot ⊆ edges H ∧ Ytot ⊆ childEdges H.G W0 ∧
            SparseEdge.ind Ytot ∈ LamCore H.G H.lab F W0 ∧
            Disjoint (SampledResource.lift W E₀) Ytot ∧
            Basal H F (edges H \ (T ∪ (SampledResource.lift W E₀ ∪ Ytot))) ∧
            Disjoint T (SampledResource.lift W E₀ ∪ Ytot) := by
  intro earlyOuter earlyStock earlyBank
  let εOuter := complementBudget C α h
  have hεOuter : 0 < εOuter := complementBudget_pos h hC hα
  let γStock := resourceStockBudget α C
  let ηBank := CatalogNative.Explicit.bankProtectionBudget α βBank h
  have hηBank : 0 < ηBank := CatalogNative.Explicit.bankProtectionBudget_pos h hα hβBank
  let d := CatalogNative.Explicit.catalogDimension βBank h
  let c := CatalogNative.Explicit.catalogCoefficient βBank h
  let E := CatalogNative.Explicit.catalogColumn βBank h
  let Rc := CatalogNative.Explicit.bankCatalogRadius α βBank h
  let Lbank := CatalogNative.Explicit.bankCatalogSize α βBank h
  let Ecell := CatalogNative.Explicit.bankCellSize α βBank h
  have hCatCard : Fintype.card (Cat d Rc) = Lbank := by
    simpa only [d,Rc,Lbank,CatalogNative.Explicit.bankCatalogSize] using card_Cat d Rc
  let AM := S07V34.Explicit.paymentCost d (S07V44.monR Rc E)
  let MM := S07V34.Explicit.monitorMagnitude d (S07V44.monR Rc E)
  let KM := S07V34.Explicit.monitorDimension d (S07V44.monR Rc E)
  let P := 2*S07V46.gammaL AM MM Lbank
  have hP : P = 2*S07V46.gammaL AM MM Lbank := rfl
  let δgeom := ExplicitGeometry.deletionBudget βBank h
  obtain ⟨hδgeom,_,hGeom⟩ := ExplicitGeometry.deletionBudget_spec hβBank h
  let δcap := min δgeom (min (coreDelta βBank h) (S07V37.delOf (βBank/2) h))
  have hδcap : 0 < δcap := lt_min hδgeom
    (lt_min (by unfold coreDelta; positivity) (S07V37.delOf_pos (by positivity) h))
  intro a b ρFuture ηRef εRef γRef nRef hγRef hReference
  let γ := min γRef 1
  have hγ : 0 < γ := lt_min hγRef one_pos
  have hγone : γ ≤ 1 := min_le_right _ _
  let κBank := preparedBankRoundRate α βBank (γ/4) δcap h P
  let εBank := CatalogNative.Explicit.bankTolerance α βBank (γ/4) h
  have hκBank : 0 < κBank := CatalogNative.Explicit.bankRoundRate_pos h P hα hβBank
    (by positivity) (lt_min hδcap (by unfold coreDelta; positivity))
  have hεBank : 0 < εBank := CatalogNative.Explicit.bankTolerance_pos h hα hβBank (by positivity)
  have hεBankCap : εBank ≤ γ/4 := min_le_right _ _
  intro q hq hqε αPool εRoute t hαPool hεRoute ht ht3
  let θStock := resourceTerminalBudget α C h αPool (q/2) εRoute (ηBank/2) t
  have hθStock : 0 < θStock :=
    (resource_parameters_pos α C h αPool (q/2) εRoute (ηBank/2) t 1 1 hα hC hαPool
      (by positivity) hεRoute (by positivity) (by norm_num) (by norm_num)).2.1
  let θT := min θStock (γ*q/64)
  have hθT : 0 < θT := lt_min hθStock (by positivity)
  let Λ := CatalogNative.Explicit.physicalWeightMagnitude (α/2) (βBank/2) h d c MM
  have hΛ : 0 < Λ := CatalogNative.Explicit.physicalWeightMagnitude_pos _ _ _ _ _ _
  let nWeights := CatalogNative.Explicit.nativeWeightOrder α βBank (q/2) h
  let Bstatic := 2*Ecell*(2*Lbank*P)
  let γPay := StockEntry.Explicit.bankGamma (q/2) εBank
  let ηPay := StockEntry.Explicit.bankEta κBank (q/2) εBank Bstatic
  let δ := StockEntry.Explicit.monitorCap Λ ηPay KM
  let nBank := StockEntry.Explicit.bankOrder κBank (q/2)
  obtain ⟨hγPay,hηPay,hδ,hηκ,hcapacity,hqn,hKB,hlarge⟩ :=
    StockEntry.Explicit.native_bank_scale_cap_explicit κBank (q/2) εBank Λ Bstatic KM
      hκBank (by positivity) hεBank hΛ.le
  let εPack := δ/2
  have hεPack : 0 < εPack := by dsimp [εPack]; positivity
  have hεδ : εPack ≤ δ := by dsimp [εPack]; linarith
  let ρcap := min εPack (min (q/128) (γ*q/64))
  let τcap := min εPack (min (q/64) (γ*q/64))
  have hρcap : 0 < ρcap := lt_min hεPack (lt_min (by positivity) (by positivity))
  have hτcap : 0 < τcap := lt_min hεPack (lt_min (by positivity) (by positivity))
  let ρ := resourceInputBudget αPool (q/2) εRoute (ηBank/2) t ρcap τcap
  let κStock := BasalIncidence.Explicit.rawStockCompletion α ρ
  let τR := resourceOutputBudget (q/2) (ηBank/2) τcap
  obtain ⟨_,_,hρ,hκStock,hτR⟩ := resource_parameters_pos α C h αPool (q/2) εRoute (ηBank/2) t
    ρcap τcap hα hC hαPool (by positivity) hεRoute (by positivity) hρcap hτcap
  obtain ⟨hρCap,hτCap,hρτ⟩ := resource_rate_caps αPool (q/2) εRoute (ηBank/2) t ρcap τcap
  let nResource := stockBankOrder α C βBank (γ/4) δcap αPool (q/2) εRoute h P t ρcap τcap
  have hρδ : ρ ≤ δ := hρCap.trans ((min_le_left _ _).trans hεδ)
  have hτδ : τR ≤ δ := hτCap.trans ((min_le_left _ _).trans hεδ)
  have hρRef : ρ ≤ γ*q/64 := hρCap.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hτRef : τR ≤ γ*q/64 := hτCap.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hρq : ρ ≤ (q/2)/64 := by
    have hc := hρCap.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hτq : τR ≤ q/64 := hτCap.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  let nNative := nativePartitionOrder C α κStock εPack εPack Λ h
  intro θTarget nTarget
  intro V _ H φ W A U T DT dT dS μ W0
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  dsimp only
  let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let S := SampledResource.lift W (edges JW ∩ triEdges U)
  intro hn hSeed hPhys h3 h4 hWlo hWhi hWcore hPool hRoute h3A h4A
    h3W h4W hμ hLoad hU hWU hSd hScap hSMacro hT hTS hTd hTcap
  change max nResource (max nNative (max nWeights (max nBank
    (max ((Lbank+2)*KM) (max ⌈2*(nRef:ℝ)/q⌉₊ ⌈4/(γ*q)⌉₊))))) ≤ Fintype.card V at hn
  have hnResource : nResource ≤ Fintype.card V := by omega
  have hnNative : nNative ≤ Fintype.card V := by omega
  have hnWeights : nWeights ≤ Fintype.card V := by omega
  have hnBank : nBank ≤ Fintype.card V := by omega
  have hsize : (Lbank+2)*KM ≤ Fintype.card V := by omega
  have hnRef : nRef ≤ W.card := by
    have hnCeil : ⌈2*(nRef:ℝ)/q⌉₊ ≤ Fintype.card V := by omega
    have hce : (⌈2*(nRef:ℝ)/q⌉₊:ℝ) ≤ Fintype.card V := by exact_mod_cast hnCeil
    have ht := (div_le_iff₀ hq).mp (Nat.le_ceil (2*(nRef:ℝ)/q))
    have hs := mul_le_mul_of_nonneg_right hce hq.le
    exact_mod_cast (show (nRef:ℝ) ≤ W.card by nlinarith only [hWlo,ht,hs])
  have hLarge : 2 ≤ γ*W.card := by
    have hnCeil : ⌈4/(γ*q)⌉₊ ≤ Fintype.card V := by omega
    have hce : (⌈4/(γ*q)⌉₊:ℝ) ≤ Fintype.card V := by exact_mod_cast hnCeil
    have ht := (div_le_iff₀ (mul_pos hγ hq)).mp (Nat.le_ceil (4/(γ*q)))
    have hs := mul_le_mul_of_nonneg_right hce (mul_pos hγ hq).le
    have hw := mul_le_mul_of_nonneg_left hWlo hγ.le
    nlinarith only [ht,hs,hw]
  have hTStock : (dT:ℝ) ≤ θStock*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hTref : (dT:ℝ) ≤ (γ*q/64)*Fintype.card V :=
    hTcap.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have hSU : ∀ e ∈ S, ∀ v ∈ e, v ∈ U.image Subtype.val := by
    intro e he v hv
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    induction f using Sym2.ind with
    | _ u w =>
      obtain ⟨hu,hw,huw⟩ := mem_triEdges.mp (mem_inter.mp hf).2
      obtain ⟨v',hv',rfl⟩ := Sym2.mem_map.mp hv
      rcases Sym2.mem_iff.mp hv' with rfl | rfl
      · exact mem_image.mpr ⟨_,hu,rfl⟩
      · exact mem_image.mpr ⟨_,hw,rfl⟩
  obtain ⟨D,R,C0,qm,z,hD,hDT,hDd,hSupply,hRdis,hR,hRinc,hRS,hRd,hY0,hMode,
    hqm,hql,hz,hCZ,hMacro,hBdis,hBd,hCat⟩ :=
    stock_bank_on_prepared_window_with_structured_future_early_protection_explicit F α C βBank h hα hC hβBank
      P (γ/4) δcap (by positivity) hδcap αPool (q/2) εRoute t hαPool (by positivity) hεRoute ht ht3
      ρcap τcap hρcap hτcap H φ W A (U.image Subtype.val) T S DT dT dS hnResource hSeed hPhys h3 h4
      hWcore hPool hRoute h3A h4A hT hTS hWU hSU hSd hScap hSMacro hTd hTStock
  let F0 := ((cover D ∪ R) ∪ T) ∪ S
  let Setting := protSetting C0 Rc P qm Ecell z F0
  let Mbank := ⌊κBank*(W0.card:ℝ)^2⌋₊
  change MacroBank Setting (Fintype.card (Cat d Rc)) Mbank at hMacro
  rw [hCatCard] at hMacro
  let Bank := Br Setting Mbank
  have hBankLt : ∀ v, (degIn Bank v : ℝ) < εBank*W0.card := by
    intro v
    simpa only [Bank,Setting,Mbank,degIn,S07V40.deg,F0,Rc,Ecell,κBank,εBank,W0,
      CatalogNative.Explicit.bankCatalogRadius] using hBd v
  let Actual := ((cover D ∪ R) ∪ T) ∪ Bank
  have hDTactual : Disjoint (cover D) T := hDT.mono_right Finset.subset_union_left
  have hBactual : Disjoint Bank ((cover D ∪ R) ∪ T) := hBdis.mono_right Finset.subset_union_left
  have hBankBasal : Basal H F Bank := protected_bank_basal C0 F0 hMacro
  have hBasal : Basal H F Actual := prepared_resource_union_basal
    ⟨DT,hT⟩ ⟨D,hD⟩ hR hDTactual hRdis hBankBasal hBactual
  have hSdis : Disjoint S Actual := Finset.disjoint_union_right.mpr
    ⟨Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_union_right.mpr
        ⟨(hDT.mono_right Finset.subset_union_right).symm,hRS.symm⟩,hTS.symm⟩,
      (hBdis.mono_right Finset.subset_union_right).symm⟩
  have hDcap : ∀ v, (degIn (cover D) v:ℝ) ≤ ρ*Fintype.card V := fun v => (hDd v).le
  have hRcap : ∀ v, (degIn R v:ℝ) ≤ τR*Fintype.card V := by
    intro v
    simpa only [degIn,SelSimul.edeg] using hRd v
  have hTcapRef : ∀ v, (degIn T v:ℝ) ≤ (γ*q/64)*Fintype.card V := by
    intro v
    exact (by exact_mod_cast hTd v : (degIn T v:ℝ) ≤ dT).trans hTref
  have hBcap : ∀ v, (degIn Bank v:ℝ) ≤ εBank*W.card := by
    intro v
    have hb : (degIn Bank v:ℝ) ≤ εBank*W0.card := (hBankLt v).le
    exact hb.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (Finset.card_le_card (Finset.sdiff_subset : W0 ⊆ W))) hεBank.le)
  obtain ⟨dB,hBdegCap,hBRefCap⟩ := four_resource_reference_window W
    (cover D) R T Bank q γ ρ τR (γ*q/64) εBank hq hγ hWlo
    (by nlinarith only [hρRef,hτRef,mul_pos hγ hq]) hεBankCap
    hDcap hRcap hTcapRef hBcap hLarge
  obtain ⟨E₀,D₀,hFuture,hEdges,hEDec,hAvoid,hUnion,hHole,hGraph⟩ :=
    naked_reference_at_preserving_future_core F a b βRef ρFuture ηRef εRef γRef h nRef
      hReference H W μ U Actual dB hnRef h3W h4W hμ hLoad hU hSdis hBasal hBdegCap
      (hBRefCap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
  have hPath : S07V45.CorePathContract H.G H.lab F W0 t := by
    letI : ∀ v, DecidableRel (ComponentRows.link H.G H.lab F v).Adj :=
      fun _ => Classical.decRel _
    apply S07V45.contract_of_route (by omega)
    intro v x y hxy
    obtain ⟨p,hp,hW,-,-⟩ := hRoute ∅ ⊥ 0 (by simp; positivity)
      (fun u => by simp) (by simp; positivity) v x y hxy
    exact ⟨p,hp,hW⟩
  have hDcore : ∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤
      (q/2)/64 * Fintype.card V := by
    intro v
    have hd : (SparseEdge.degIn (cover D) v : ℝ) ≤ ρ * Fintype.card V := by
      simpa only [SparseEdge.degIn, TypedTriangle.degIn] using le_of_lt (hDd v)
    exact hd.trans (mul_le_mul_of_nonneg_right hρq (Nat.cast_nonneg _))
  have hDcap : ∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤ ρ * Fintype.card V := by
    intro v
    simpa only [SparseEdge.degIn, TypedTriangle.degIn] using le_of_lt (hDd v)
  have hDsmall : ∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤ q/64 * Fintype.card V := by
    intro v
    exact (hDcore v).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Nat.cast_nonneg _))
  have hRsmall : ∀ v, (SparseEdge.degIn R v : ℝ) ≤ q/64 * Fintype.card V := by
    intro v
    have hd : (SparseEdge.degIn R v : ℝ) ≤ τR * Fintype.card V := by
      simpa only [SparseEdge.degIn, SelSimul.edeg] using hRd v
    exact hd.trans (mul_le_mul_of_nonneg_right hτq (Nat.cast_nonneg _))
  have hTsmall : ∀ v, (SparseEdge.degIn T v : ℝ) ≤ q/64 * Fintype.card V := by
    intro v
    have hd : (SparseEdge.degIn T v : ℝ) ≤ dT := by
      exact_mod_cast (show SparseEdge.degIn T v ≤ dT by
        simpa only [SparseEdge.degIn, TypedTriangle.degIn] using hTd v)
    have hg : γ * q/64 ≤ q/64 := by nlinarith
    exact hd.trans (hTref.trans (mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg _)))
  have hBankSmall : ∀ v, (SparseEdge.degIn Bank v : ℝ) ≤ (W0.card : ℝ)/4 := by
    intro v
    have hd : (SparseEdge.degIn Bank v : ℝ) ≤ εBank * W0.card := by
      simpa only [SparseEdge.degIn,degIn] using (hBankLt v).le
    have hc : εBank ≤ 1/4 := by linarith
    have hn : (0 : ℝ) ≤ W0.card := by positivity
    nlinarith
  obtain ⟨dU,hUdeg,hSmall⟩ := actual_bank_union_budget D R T Bank W W0 q εOuter hq hqε
    Finset.sdiff_subset hWhi.le hDsmall hRsmall hTsmall hBankSmall
  have hNativeResult := native_partition_result_after_actual_bank_reference_explicit F C α h hC hα hh
    κStock εPack εPack Λ (q/2) ρ τR t hκStock hεPack hεPack hΛ ht ht3 H φ W W0 D DT R T Bank E₀ D₀ dU
    hnNative hSeed hPhys h3 h4 hPath hD hR hT
    hBankBasal hDTactual hRdis hBactual hEDec hAvoid hUnion hUdeg hSmall
    hSupply hMode hDcore hDcap hRd
  obtain ⟨Mon,Fm,_⟩ := S07V47.Explicit.protSetting_allocation_constants_explicit.{0,0}
    d c E Rc Lbank C0
  have hc3 : SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {x // x ∈ W0} → V)) (H.lab ∘ Subtype.val) F βBank :=
    nested_prepared_commonNbrCond_direct H F W A βBank h3A
  have hc4 : SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {x // x ∈ W0} → V)) (H.lab ∘ Subtype.val) F βBank h :=
    nested_prepared_hingeCond_direct H F W A βBank h h4A
  have hw0 : (0:ℝ) ≤ W0.card := Nat.cast_nonneg _
  have hzGeom : (z:ℝ) ≤ δgeom * W0.card :=
    hz.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hw0)
  have hzCore : (z:ℝ) ≤ coreDelta βBank h * W0.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hw0)
  have hzDel : (z:ℝ) ≤ S07V37.delOf (βBank/2) h * W0.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hw0)
  have hGeomBudget := hGeom hw0 hzGeom
  have hBstar : (childSetting C0 Rc P qm Ecell z).Bstar = 2*Lbank*P := by
    change 2*Fintype.card (Cat d Rc)*P = 2*Lbank*P
    rw [hCatCard]
  have hCap : ηPay * ((2 * Ecell *
      (childSetting C0 Rc P qm Ecell z).Bstar : ℕ) : ℝ) / γPay ≤ 1 := by
    rw [hBstar]
    exact hcapacity
  have hQn : γPay * Fintype.card V ≤ qm := hqn _ _ _ hWcore (by
    convert hql using 1 <;> ring)
  have hKB' : (KM:ℝ) * (εPack + (3*Λ/2) * (εPack+2*ρ+2*τR)) ≤ ηPay :=
    hKB εPack εPack ρ τR hεδ hεδ (hρδ) (hτδ)
  have hCapacity : Setting.K (Zr Setting Mbank) ≠ ⊥ →
      1 + ηPay * (Fintype.card V:ℝ)^2 ≤ 2*Mbank := by
    intro _
    exact StockEntry.final_bank_capacity_of_sample_size κBank (q/2) ηPay
      (Fintype.card V) W0.card hκBank (by positivity) hWcore hηκ (hlarge _ hnBank)
  obtain ⟨DR,Q,Rtail,Ps,Y,x,J,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR',hRL,hMove,hPY,hPs,hYphys,hYin,hYdeg,hYF,hYE,hJ,hx,hOut,hFinish⟩ :=
    CatalogNative.Explicit.activate_partition_bank_after_g34_result_explicit α βBank (q/2) h d c E Rc AM MM KM
      hα hβBank (by positivity) hβα H F W0 D R (((((cover D ∪ R) ∪ T) ∪ Bank)) ∪ SampledResource.lift W E₀)
      C0 P qm Ecell z Mbank Lbank Mon Fm hP F0 (Finset.subset_union_left.trans Finset.subset_union_left)
      hMacro hCat γPay ηPay εPack εPack ρ τR hnWeights hWcore h3 h4 hc3 hc4
      hzCore (by convert hGeomBudget.1 using 1 <;> ring) hGeomBudget.2 hzDel
      hsize hηPay.le hγPay hQn hCap hKB' hCapacity hNativeResult
  have hYDR : Y ⊆ cover D ∪ R := by
    intro e he
    have hm : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ he
    rcases mem_union.mp hm with heR | heL
    · exact mem_union_right _ heR
    · exact mem_union_left _ (hRes heL)
  have hYU : Y ⊆ Actual := hYDR.trans
    (Finset.subset_union_left.trans Finset.subset_union_left)
  obtain ⟨Ytot,Yb,Bc,hYtot,hYtotE,hYtotU,hEY,hBank,hBc,hBcF,hBcYb,hYYb,hLam,hYbCore⟩ :=
    activated_mode_avoiding_actual_reference H F W0 C0 F0 Actual Y
      (SampledResource.lift W E₀) x hMacro hJ hYF hYE hx hOut
      hYU Finset.subset_union_right hAvoid
  have hYCore : Y ⊆ childEdges H.G W0 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      change s(u,v) ∈ SparseEdge.edges (indG H.G W0)
      exact SparseEdge.mem_edges.mpr ⟨SparseEdge.mem_edges.mp (hYE he),
        hYin s(u,v) he u (by simp),hYin s(u,v) he v (by simp)⟩
  have hYtotCore : Ytot ⊆ childEdges H.G W0 := by
    rw [hYtot]
    exact Finset.union_subset hYCore hYbCore
  have hEbasal := SampledResource.basal_lift H F W (show Basal _ F E₀ from ⟨D₀,hEDec⟩)
  obtain ⟨hTail,_,_⟩ := reserved_terminal_remainder H F D DT R T Bank
    (SampledResource.lift W E₀) Rtail hR hT hBankBasal hEbasal
    hDTactual hRdis hBactual hAvoid hDtail hEq
  have hRT : Disjoint R T := hRdis.mono_right Finset.subset_union_right
  have hRB : Disjoint R Bank := (hBactual.mono_right
    (Finset.subset_union_right.trans Finset.subset_union_left)).symm
  have hRE : Disjoint R (SampledResource.lift W E₀) := (hAvoid.mono_right
    ((Finset.subset_union_right.trans Finset.subset_union_left).trans
      Finset.subset_union_left)).symm
  have hTB : Disjoint T Bank := (hBactual.mono_right Finset.subset_union_right).symm
  have hTE : Disjoint T (SampledResource.lift W E₀) := (hAvoid.mono_right
    (Finset.subset_union_right.trans Finset.subset_union_left)).symm
  have hBE : Disjoint Bank (SampledResource.lift W E₀) :=
    (hAvoid.mono_right Finset.subset_union_right).symm
  obtain ⟨hOuter,hTerminal,hOuterEq⟩ := paid_outer_partition H F Q R T Bank
    (SampledResource.lift W E₀) Rtail Ps Y Yb Bc
    hQ hQR hTail hRT hRB hRE hTB hTE hBE hMove hPY hPs hBank hBc hBcYb hYYb
  rw [← hYtot] at hOuter hTerminal hOuterEq
  exact ⟨E₀,D₀,Ytot,hEDec,hFuture,hHole,hYtotE,hYtotCore,hLam,hEY,hOuter,hTerminal⟩
#print axioms structured_activated_naked_layer_before_reference_explicit
end TypedTriangle.Vortex.Explicit
