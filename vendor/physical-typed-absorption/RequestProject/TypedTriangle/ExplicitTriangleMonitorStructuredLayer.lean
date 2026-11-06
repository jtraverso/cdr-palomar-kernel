module
public import RequestProject.TypedTriangle.ExplicitTriangleMonitorPartition
public import RequestProject.TypedTriangle.ExplicitStructuredActivatedLayer
public import RequestProject.TypedTriangle.TriangleMonitorStructuredActivatedLayer
public import RequestProject.TypedTriangle.TriangleMonitorStructuredCleanLayerState
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open CatalogNative CorePaid BasalIncidence SelSimul S07V40 S07V42 S07V43 S07V44 S07V47
def monitorLayerThreshold (α C βBank γRef q αPool εRoute ζStat : ℝ) (h t nRef qStat : ℕ) : ℕ :=
  let εOuter := monitorComplementBudget C α h ζStat
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
  let εPack := min (δ/2) ζStat
  let ρcap := min εPack (min (q/128) (γ*q/64))
  let τcap := min εPack (min (q/64) (γ*q/64))
  let ρ := resourceInputBudget αPool (q/2) εRoute (ηBank/2) t ρcap τcap
  let κStock := BasalIncidence.Explicit.rawStockCompletion α ρ
  let τR := resourceOutputBudget (q/2) (ηBank/2) τcap
  let nResource := stockBankOrder α C βBank (γ/4) δcap αPool (q/2) εRoute h P t ρcap τcap
  let nNative := monitorNativePartitionOrder C α h qStat κStock εPack εPack Λ
  let nWeights := CatalogNative.Explicit.nativeWeightOrder α βBank (q/2) h
  let nBank := StockEntry.Explicit.bankOrder κBank (q/2)
  max nResource (max nNative (max nWeights (max nBank
    (max ((Lbank+2)*KM) (max ⌈2*(nRef:ℝ)/q⌉₊ ⌈4/(γ*q)⌉₊)))))

theorem structured_activated_naked_layer_before_reference_with_triangle_monitors_explicit {I : Type}
    (F : Set (Multiset I)) (α C βBank βRef ζStat : ℝ) (h qStat : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hβBank : 0 < βBank)
    (hβα : βBank ≤ α) (hh : 6 ≤ h) (hζStat : 0 < ζStat) :
    let εOuter := monitorComplementBudget C α h ζStat
    let γStock := resourceStockBudget α C
    let ηBank := CatalogNative.Explicit.bankProtectionBudget α βBank h
      ∀ (a b ρFuture ηRef εRef γRef : ℝ) (nRef : ℕ), 0 < γRef →
      NakedReferenceAt F a b βRef ρFuture ηRef εRef γRef h nRef →
      ∀ q : ℝ, 0 < q → 4*q ≤ εOuter →
      ∀ (αPool εRoute : ℝ) (t : ℕ),
        0 < αPool → 0 < εRoute → Odd t → 3 ≤ t →
        let θT := layerTerminalBudget α C βBank γRef q αPool εRoute h t
        let n₀ := monitorLayerThreshold α C βBank γRef q αPool εRoute ζStat h t nRef qStat
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
          ∀ (ν : Type) [Fintype ν] (w : ν → Finset V → ℝ),
          (Fintype.card ν:ℝ) ≤ (Fintype.card V:ℝ)^qStat →
          (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
          ∃ (P₀ : Finset (Finset V)) (E₀ : Finset (Sym2 {x // x ∈ W}))
            (D₀ : Finset (Finset {x // x ∈ W})) (Ytot : Finset (Sym2 V)),
            OriginalTriangleMonitorData H F φ w (2*ζStat) (2*ζStat) P₀ ∧
            P₀.biUnion triEdges ⊆ edges H \ (T ∪ (SampledResource.lift W E₀ ∪ Ytot)) ∧
            Basal H F ((edges H \ (T ∪ (SampledResource.lift W E₀ ∪ Ytot))) \ P₀.biUnion triEdges) ∧
            IsDecomposition JW F E₀ D₀ ∧ edges JW ∩ triEdges U ⊆ E₀ ∧
            (∀ v, (SparseEdge.degIn (edges JW \ E₀) v:ℝ) ≤ ηRef*W.card) ∧
            Ytot ⊆ edges H ∧ Ytot ⊆ childEdges H.G W0 ∧
            SparseEdge.ind Ytot ∈ LamCore H.G H.lab F W0 ∧
            Disjoint (SampledResource.lift W E₀) Ytot ∧
            Basal H F (edges H \ (T ∪ (SampledResource.lift W E₀ ∪ Ytot))) ∧
            Disjoint T (SampledResource.lift W E₀ ∪ Ytot) := by
  intro earlyOuter earlyStock earlyBank
  let εOuter := monitorComplementBudget C α h ζStat
  have hεOuter : 0 < εOuter := monitorComplementBudget_pos h hC hα hζStat
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
  let εPack := min (δ/2) ζStat
  have hεPack : 0 < εPack := lt_min (by positivity) hζStat
  have hεδ : εPack ≤ δ := (min_le_left _ _).trans (by linarith only [hδ])
  have hεStat : εPack ≤ ζStat := min_le_right _ _
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
    linarith only [hc]
  have hτq : τR ≤ q/64 := hτCap.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  let nNative := monitorNativePartitionOrder C α h qStat κStock εPack εPack Λ
  intro θTarget nTarget
  intro V _ H φ W A U T DT dT dS μ W0
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  dsimp only
  let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let S := SampledResource.lift W (edges JW ∩ triEdges U)
  intro hn hSeed hPhys h3 h4 hWlo hWhi hWcore hPool hRoute h3A h4A
    h3W h4W hμ hLoad hU hWU hSd hScap hSMacro hT hTS hTd hTcap ν _ w hν hw
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
    exact (hDcore v).trans (mul_le_mul_of_nonneg_right (by linarith only [hq])
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
    have hg : γ * q/64 ≤ q/64 := by nlinarith only [hγone,hq]
    exact hd.trans (hTref.trans (mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg _)))
  have hBankSmall : ∀ v, (SparseEdge.degIn Bank v : ℝ) ≤ (W0.card : ℝ)/4 := by
    intro v
    have hd : (SparseEdge.degIn Bank v : ℝ) ≤ εBank * W0.card := by
      simpa only [SparseEdge.degIn,degIn] using (hBankLt v).le
    have hc : εBank ≤ 1/4 := by linarith only [hεBankCap,hγone]
    have hn : (0 : ℝ) ≤ W0.card := by positivity
    nlinarith only [hd,hc,hn]
  obtain ⟨dU,hUdeg,hSmall⟩ := actual_bank_union_budget D R T Bank W W0 q εOuter hq hqε
    Finset.sdiff_subset hWhi.le hDsmall hRsmall hTsmall hBankSmall
  have hNativeResult := native_partition_result_after_actual_bank_reference_with_triangle_monitors_explicit F C α ζStat h qStat hC hα hh hζStat
    κStock εPack εPack Λ (q/2) ρ τR t hκStock hεPack hεPack hΛ ht ht3 H φ W W0 D DT R T Bank E₀ D₀ dU
    hnNative hSeed hPhys h3 h4 hPath hD hR hT
    hBankBasal hDTactual hRdis hBactual hEDec hAvoid hUnion hUdeg hSmall
    hSupply hMode hDcore hDcap hRd ν w hν hw
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
  obtain ⟨P₀,DR,Q,Rtail,Ps,Y,x,J,hPQ,hData,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR',hRL,hMove,hPY,hPs,hYphys,hYin,hYdeg,hYF,hYE,hJ,hx,hOut,hFinish⟩ :=
    CatalogNative.Explicit.activate_partition_bank_after_g34_result_retaining_packing_explicit α βBank (q/2) h d c E Rc AM MM KM
      hα hβBank (by positivity) hβα H F W0 D R (((((cover D ∪ R) ∪ T) ∪ Bank)) ∪ SampledResource.lift W E₀)
      (OriginalTriangleMonitorData H F φ w (εPack+ζStat) (εPack+ζStat))
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
  obtain ⟨hOuter,hTerminal,hOuterEq,Douter,hDouter,hPouter⟩ :=
    paid_outer_partition_retaining_initial_packing H F Q P₀ R T Bank
    (SampledResource.lift W E₀) Rtail Ps Y Yb Bc
    hQ hPQ hQR hTail hRT hRB hRE hTB hTE hBE hMove hPY hPs hBank hBc hBcYb hYYb
  rw [← hYtot] at hOuter hTerminal hOuterEq hDouter
  have hP₀E : P₀.biUnion triEdges ⊆ edges H \ (T ∪ (SampledResource.lift W E₀ ∪ Ytot)) := by
    intro e he
    obtain ⟨A,hA,heA⟩ := mem_biUnion.mp he
    exact hDouter.subset (hPouter hA) heA
  have hRest : Basal H F ((edges H \ (T ∪ (SampledResource.lift W E₀ ∪ Ytot))) \ P₀.biUnion triEdges) :=
    ⟨Douter\P₀,TriangleMonitors.decomposition_sdiff_of_subfamily hDouter hPouter⟩
  have hData' : OriginalTriangleMonitorData H F φ w (2*ζStat) (2*ζStat) P₀ := by
    obtain ⟨hP₀,hSp,hQu⟩ := hData
    refine ⟨hP₀,?_,?_⟩
    · intro v
      exact (hSp v).trans (mul_le_mul_of_nonneg_right (by linarith only [hεStat]) (Nat.cast_nonneg _))
    · intro k
      exact (hQu k).trans (mul_le_mul_of_nonneg_right (by linarith only [hεStat]) (sq_nonneg _))
  exact ⟨P₀,E₀,D₀,Ytot,hData',hP₀E,hRest,hEDec,hFuture,hHole,hYtotE,hYtotCore,hLam,hEY,hOuter,hTerminal⟩


#print axioms structured_activated_naked_layer_before_reference_with_triangle_monitors_explicit
end TypedTriangle.Vortex.Explicit

namespace TypedTriangle.Vortex.Explicit
open CatalogNative CorePaid BasalIncidence SelSimul S07V40 S07V42 S07V43 S07V44 S07V47

def monitorCleanLayerThreshold (α C βBank γRef q αPool εRoute ζStat : ℝ)
    (h t nRef nPaid nGeometry qStat : ℕ) : ℕ :=
  max (monitorLayerThreshold α (2*C) βBank γRef q αPool εRoute ζStat h t nRef qStat)
    ⌈2*((max 1 (max nPaid nGeometry):ℕ):ℝ)/q⌉₊

private theorem degree_sdiff_le_change_decEq {X : Type}
    (S E : Finset (Sym2 X)) (v : X) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 X))
    (hBound : (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) S E) v : ℝ) ≤ b) :
    (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) S E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hBound

private theorem lift_pull_of_core_support {V : Type} [Fintype V]
    (H : SimpleGraph V) (W0 W : Finset V) (Y : Finset (Sym2 V))
    (hW : W0 ⊆ W) (hY : Y ⊆ childEdges H W0) :
    SampledResource.lift W (SampledResource.pull W Y) = Y := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact mem_preimage.mp hf
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hc : (indG H W0).Adj u v := SparseEdge.mem_edges.mp (hY he)
      let uW : {x // x ∈ W} := ⟨u,hW hc.2.1⟩
      let vW : {x // x ∈ W} := ⟨v,hW hc.2.2⟩
      exact mem_image.mpr ⟨s(uW,vW),mem_preimage.mpr he,rfl⟩

/-- The concrete structured bank layer and its exact clean H1 child use
one prepared raw window and the globally chosen reference precision. -/
theorem structured_clean_paid_layer_state_with_triangle_monitors_explicit {I : Type}
    (F : Set (Multiset I)) (α C βBank αRaw ζStat : ℝ) (h qStat : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hβBank : 0 < βBank)
    (hβα : βBank ≤ α) (hh : 6 ≤ h) (hζStat : 0 < ζStat) :
    let εOuter := monitorComplementBudget (2*C) α h ζStat
    let γStock := resourceStockBudget α (2*C)
    let ηBank := CatalogNative.Explicit.bankProtectionBudget α βBank h
      ∀ (β K ηSpec a b ρFuture ζ εRef γRef : ℝ)
        (nRef Nbase Ns nPaid nGeometry : ℕ),
      0 < γRef → a ≤ 3/(4*C) → 5*C/4 ≤ b → 0 ≤ ζ → ζ ≤ ηSpec →
      ζ ≤ αRaw/(10*(2:ℝ)^h.choose 2) →
      PaidReferenceCap αRaw h ηSpec nGeometry →
      PaidSmoothAt αRaw β K ηSpec h Nbase Ns nPaid →
      NakedReferenceAt F a b αRaw ρFuture ζ εRef γRef h nRef →
      ∀ q : ℝ, 0 < q → 4*q ≤ εOuter →
      ∀ (αPool εRoute : ℝ) (t : ℕ),
        0 < αPool → 0 < εRoute → Odd t → 3 ≤ t →
        let θT := layerTerminalBudget α (2*C) βBank γRef q αPool εRoute h t
        let n₀ := monitorCleanLayerThreshold α C βBank γRef q αPool εRoute ζStat h t nRef nPaid nGeometry qStat
        ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
          (W : Finset V) (A : Finset (Survivors (univ \ W)))
          (U : Finset {x // x ∈ W}) (T : Finset (Sym2 V))
          (DT : Finset (Finset V)) (dT dS : ℕ) (μ : Finset {x // x ∈ W} → ℝ) (ξ : ℝ),
          let W0 := W \ liftVertexSet (univ \ W) A
          letI : DecidableEq {x // x ∈ W} := Classical.decEq _
          let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
          let S := SampledResource.lift W (edges JW ∩ triEdges U)
          n₀ ≤ Fintype.card V → IsDiffuseSeed H F (2*C) φ → IsPhysical H F (edges H) →
          CommonNbrCond H F α → HingeCond H F α h →
          q*Fintype.card V/2 ≤ W.card → (W.card:ℝ) < 2*q*Fintype.card V →
          (q/2)*Fintype.card V/2 ≤ W0.card →
          (∀ u v : V, u ≠ v → ∀ k : I,
            ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
            (q/2)*αPool*Fintype.card V/2 ≤ ((commonNbrs H k u v) ∩ W0).card) →
          S07V27.RouteProp H.G H.lab F t εRoute W0 →
          CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F βBank →
          HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F βBank h →
          Dispersal.PreparedCore JW.G JW.lab F αRaw h (max Nbase Ns) β →
          CommonNbrCond JW F αRaw → CleanHingeCond JW F αRaw h →
          (∀ Q, IsAllowed JW F Q → (3/(4*C))/W.card ≤ μ Q ∧
            μ Q ≤ (5*C/4)/W.card) →
          0 ≤ ξ → ξ ≤ εRef →
          (∀ e ∈ edges JW, |bdry JW F μ e-1| ≤ ξ) →
          K*(ξ+(5*C/2)*⌊ζ*W.card⌋₊/W.card) ≤ 1/(4*C) →
          (U.card:ℝ) ≤ ρFuture*W.card →
          Disjoint W0 (U.image Subtype.val) →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ γStock*Fintype.card V →
          (dS:ℝ) ≤ (ηBank/2)*W0.card →
          IsDecomposition H F T DT → Disjoint T S →
          (∀ v, degIn T v ≤ dT) → (dT:ℝ) ≤ θT*Fintype.card V →
          ∀ (ν : Type) [Fintype ν] (w : ν → Finset V → ℝ),
          (Fintype.card ν:ℝ) ≤ (Fintype.card V:ℝ)^qStat →
          (∀ k Q, IsAllowed H F Q → |w k Q| ≤ 1) →
          ∃ (P₀ : Finset (Finset V)) (E₀ : Finset (Sym2 {x // x ∈ W}))
            (D₀ : Finset (Finset {x // x ∈ W})) (Ytot : Finset (Sym2 V)),
            OriginalTriangleMonitorData H F φ w (2*ζStat) (2*ζStat) P₀ ∧
            IsDecomposition JW F E₀ D₀ ∧ edges JW ∩ triEdges U ⊆ E₀ ∧
            let Jchild := subHost JW (E₀ ∪ SampledResource.pull W Ytot)
            ∃ ψ : Finset {x // x ∈ W} → ℝ,
              IsDiffuseSeed Jchild F (2*C) ψ ∧
              (∀ Q, |ψ Q-μ Q| ≤ K*(ξ+(5*C/2)*⌊ζ*W.card⌋₊/W.card)/W.card) ∧
              IsPhysical Jchild F (edges Jchild) ∧
              CommonNbrCond Jchild F (αRaw/2) ∧ CleanHingeCond Jchild F (αRaw/2) h ∧
              E₀ ⊆ edges Jchild ∧
              (∀ v, (SparseEdge.degIn (edges JW \ edges Jchild) v : ℝ) ≤ ζ*W.card) ∧
              Jchild.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) =
                JW.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) ∧
              SampledResource.lift W (edges Jchild) = SampledResource.lift W E₀ ∪ Ytot ∧
              Basal H F (edges H \ (T ∪ SampledResource.lift W (edges Jchild))) ∧
              P₀.biUnion triEdges ⊆ edges H \ (T ∪ SampledResource.lift W (edges Jchild)) ∧
              Basal H F ((edges H \ (T ∪ SampledResource.lift W (edges Jchild))) \ P₀.biUnion triEdges) ∧
              Disjoint T (SampledResource.lift W (edges Jchild)) := by
  intro earlyOuter earlyStock earlyBank
  intro β K ηSpec a b ρFuture ζ εRef γRef nRef Nbase Ns nPaid nGeometry
    hγRef hLower hUpper hζ hζSpec hζClean hCap hPaid hReference
  intro q hq hqε αPool εRoute t hαPool hεRoute ht ht3
  let nLayer := monitorLayerThreshold α (2*C) βBank γRef q αPool εRoute ζStat h t nRef qStat
  let nChild := max 1 (max nPaid nGeometry)
  intro θTarget nTarget
  intro V _ H φ W A U T DT dT dS μ ξ W0
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  dsimp only
  let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let S := SampledResource.lift W (edges JW ∩ triEdges U)
  intro hn hSeed hPhys h3 h4 hWlo hWhi hWcore hPool hRoute h3A h4A
    hPc h3W hClean hμ hξ hξRef hLoad hBudget hU hWU hSd hScap hSMacro hT hTS hTd hTcap ν _ w hν hw
  change max nLayer ⌈2*(nChild:ℝ)/q⌉₊ ≤ Fintype.card V at hn
  have hnLayer : nLayer ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnChild : nChild ≤ W.card := by
    have hce : (⌈2*(nChild:ℝ)/q⌉₊:ℝ) ≤ Fintype.card V := by
      exact_mod_cast (le_max_right _ _).trans hn
    have ht := (div_le_iff₀ hq).mp (Nat.le_ceil (2*(nChild:ℝ)/q))
    have hs := mul_le_mul_of_nonneg_right hce hq.le
    exact_mod_cast (show (nChild:ℝ) ≤ W.card by nlinarith only [hWlo,ht,hs])
  have hWeights : ∀ Q, IsAllowed JW F Q → a/W.card ≤ μ Q ∧ μ Q ≤ b/W.card := by
    intro Q hQ
    exact ⟨(div_le_div_of_nonneg_right hLower (Nat.cast_nonneg W.card)).trans (hμ Q hQ).1,
      (hμ Q hQ).2.trans (div_le_div_of_nonneg_right hUpper (Nat.cast_nonneg W.card))⟩
  have hRefLoad : ∀ e ∈ edges JW, |bdry JW F μ e-1| ≤ εRef :=
    fun e he => (hLoad e he).trans hξRef
  obtain ⟨P₀,E₀,D₀,Ytot,hData,hP₀E,hRest,hEDec,hFuture,hHole,hYE,hYCore,hLam,hAvoid,hOuter,hTerminal⟩ :=
    structured_activated_naked_layer_before_reference_with_triangle_monitors_explicit
      F α (2*C) βBank αRaw ζStat h qStat hα (by linarith only [hC]) hβBank hβα hh hζStat
      a b ρFuture ζ εRef γRef nRef hγRef hReference q hq hqε
      αPool εRoute t hαPool hεRoute ht ht3 H φ W A U T DT dT dS μ hnLayer hSeed hPhys h3 h4 hWlo hWhi hWcore
      hPool hRoute h3A h4A h3W hClean.hingeCond hWeights hRefLoad hU hWU hSd hScap
      hSMacro hT hTS hTd hTcap ν w hν hw
  obtain ⟨ψ,hψ,hClose,hPhysical,h3Child,hCleanChild,hEkeep⟩ :=
    structured_reference_clean_child αRaw β K ηSpec C ζ ξ h Nbase Ns nPaid nGeometry
      hC hζ hζSpec hξ hCap hPaid H F W0 W Finset.sdiff_subset μ E₀ D₀ Ytot hnChild
      hPc h3W hClean hμ hLoad hEDec hYE hLam hAvoid
      (by
        intro v
        exact degree_sdiff_le_change_decEq (edges JW) E₀ v (ζ*W.card)
          (@Sym2.instDecidableEq _ (Classical.decEq _))
          (@Sym2.instDecidableEq _ (fun a b => a.instDecidableEq b)) (hHole v))
      hζClean hBudget
  let Jchild := subHost JW (E₀ ∪ SampledResource.pull W Ytot)
  have hFutureGraph : Jchild.G.comap
      (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) =
      JW.G.comap (Subtype.val : {v // v ∈ U} → {x // x ∈ W}) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change Jchild.G.Adj x.val y.val ↔ JW.G.Adj x.val y.val
    constructor
    · intro hxy
      exact subHost_le JW _ hxy
    · intro hxy
      have he : s(x.val,y.val) ∈ E₀ := hFuture (mem_inter.mpr
        ⟨by simpa [edges,JW] using hxy,mem_triEdges.mpr ⟨x.property,y.property,hxy.ne⟩⟩)
      exact ⟨⟨mem_union_left _ he,hxy.ne⟩,hxy⟩
  have hEedges : E₀ ⊆ edges JW := by
    intro e he
    obtain ⟨Q,hQ,heQ⟩ := hEDec.exists_mem he
    exact triEdges_subset_edges (hEDec.1 Q hQ) heQ
  have hYpull : SampledResource.pull W Ytot ⊆ edges JW :=
    CatalogNative.paid_pull_subset_sampled_edges H W Ytot hYE
  have hLiftPull := lift_pull_of_core_support H.G W0 W Ytot Finset.sdiff_subset hYCore
  have hChildAmbient : SampledResource.lift W (edges Jchild) =
      SampledResource.lift W E₀ ∪ Ytot := by
    rw [Residual.edges_subHost_eq (Finset.union_subset hEedges hYpull)]
    change (E₀ ∪ SampledResource.pull W Ytot).image (SampledResource.edgeLift W) = _
    rw [Finset.image_union]
    change SampledResource.lift W E₀ ∪
      SampledResource.lift W (SampledResource.pull W Ytot) = _
    rw [hLiftPull]
  refine ⟨P₀,E₀,D₀,Ytot,hData,hEDec,hFuture,ψ,?_,hClose,?_,?_,?_,?_,?_,hFutureGraph,hChildAmbient,?_,?_,?_,?_⟩
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hψ
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hPhysical
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using h3Child
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hCleanChild
  · simpa only [Jchild,JW,subHost,Finset.coe_union] using hEkeep
  · intro v
    have hsub : edges JW \ edges Jchild ⊆ edges JW \ E₀ := by
      intro e he
      refine mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,?_⟩
      intro heE
      apply (mem_sdiff.mp he).2
      simpa only [Jchild,JW,subHost,Finset.coe_union] using hEkeep heE
    have hdeg : SparseEdge.degIn (edges JW \ edges Jchild) v ≤
        SparseEdge.degIn (edges JW \ E₀) v :=
      Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    have hraw : (SparseEdge.degIn (edges JW \ E₀) v : ℝ) ≤ ζ*W.card := by
      exact degree_sdiff_le_change_decEq (edges JW) E₀ v (ζ*W.card)
        (@Sym2.instDecidableEq _ (Classical.decEq _))
        (fun a b => a.instDecidableEq b) (hHole v)
    exact (Nat.cast_le.mpr hdeg).trans hraw
  · rw [hChildAmbient]
    exact hOuter
  · rw [hChildAmbient]
    exact hP₀E
  · rw [hChildAmbient]
    exact hRest
  · rw [hChildAmbient]
    exact hTerminal

#print axioms structured_clean_paid_layer_state_with_triangle_monitors_explicit

end TypedTriangle.Vortex.Explicit
