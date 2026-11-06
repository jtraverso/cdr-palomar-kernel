module
public import RequestProject.TypedTriangle.ExplicitResourceCore
public import RequestProject.TypedTriangle.VortexPreparedBankCatalogEarlyProtection
public import RequestProject.TypedTriangle.VortexFixedWindowStructuredBankEarlyProtection
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open CatalogNative CorePaid BasalIncidence SelSimul S07V40 S07V42 S07V43 S07V44

def preparedBankRoundRate (α β εcap δcap : ℝ) (h P : ℕ) : ℝ :=
  CatalogNative.Explicit.bankRoundRate α β εcap (min δcap (coreDelta β h)) h P

def preparedBankOrder (α β εcap δcap : ℝ) (h P : ℕ) : ℕ :=
  max (CatalogNative.Explicit.bankOrder α β εcap (min δcap (coreDelta β h)) h P)
    (coreN0 β h)

theorem catalogGen_on_protected_strata_explicit {V I : Type*} [Fintype V]
    {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}
    {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' P q Ecell zmax L N : ℕ}
    (h3 : SparseEdge.CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V))
      (lab ∘ Subtype.val) F β)
    (h4 : SparseEdge.HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V))
      (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    (hz : (zmax:ℝ) ≤ coreDelta β h*W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → Nonempty (DelCompression H lab F Z d' c' E'))
    (F0 : Finset (Sym2 V))
    (hM : MacroBank (ProtectedBank.protect
      (childSetting C0 (S07V42.Explicit.catRadius β d c E d' c' E') P q Ecell zmax) F0) L N) :
    ∀ j, CatalogGen C0 (S07V42.Explicit.catRadius β d c E d' c' E')
      (Zstrat (S07V47.protSetting C0 (S07V42.Explicit.catRadius β d c E d' c' E')
        P q Ecell zmax F0) N j) := by
  rw [native_protect_eq_protSetting] at hM
  intro j
  let S := S07V47.protSetting C0 (S07V42.Explicit.catRadius β d c E d' c' E') P q Ecell zmax F0
  have hs : (Zstrat S N j).card ≤ zmax :=
    hM.small _ ((preStrat_le N j).trans (numRounds_le N))
  obtain ⟨Cj⟩ := CZ (Zstrat S N j) hs
  exact S07V42.Explicit.catalog_generates_explicit hβ h3 h4 hW C0
    ((show ((Zstrat S N j).card:ℝ) ≤ zmax by exact_mod_cast hs).trans hz) Cj

theorem bank_on_prepared_fixed_window_early_protection_explicit (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    let d := CatalogNative.Explicit.catalogDimension β h
    let c := CatalogNative.Explicit.catalogCoefficient β h
    let E := CatalogNative.Explicit.catalogColumn β h
    let d' := CatalogNative.Explicit.catalogDimension (α/2) h
    let c' := CatalogNative.Explicit.catalogCoefficient (α/2) h
    let E' := CatalogNative.Explicit.catalogColumn (α/2) h
    let Ecell := CatalogNative.Explicit.bankCellSize α β h
    let η := CatalogNative.Explicit.bankProtectionBudget α β h
      ∀ P : ℕ, ∀ εcap δcap : ℝ, 0 < εcap → 0 < δcap →
      let κ := preparedBankRoundRate α β εcap δcap h P
      let ε := CatalogNative.Explicit.bankTolerance α β εcap h
        ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
          (W : Finset V) (A : Finset (Survivors (univ \ W)))
          (F0 : Finset (Sym2 V)),
          preparedBankOrder α β εcap δcap h P ≤ (W \ liftVertexSet (univ \ W) A).card →
          CommonNbrCond H F α → HingeCond H F α h →
          CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F β →
          HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F β h →
          (∀ v, (degIn F0 v : ℝ) ≤ η * (W \ liftVertexSet (univ \ W) A).card) →
          ∃ (C0 : CoreCompression H.G H.lab F
                (W \ liftVertexSet (univ \ W) A) d c E) (qm z : ℕ),
            0 < qm ∧ ε/4*(W \ liftVertexSet (univ \ W) A).card ≤ (qm:ℝ) ∧
            (z:ℝ) ≤ δcap*(W \ liftVertexSet (univ \ W) A).card ∧
            (∀ Z : Finset V, Z.card ≤ z →
              Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
            let Rc := S07V42.Explicit.catRadius β d c E d' c' E'
            let Setting := S07V47.protSetting C0 Rc P qm Ecell z F0
            let M := ⌊κ*((W \ liftVertexSet (univ \ W) A).card:ℝ)^2⌋₊
            MacroBank Setting (Fintype.card (Cat d Rc)) M ∧
              Disjoint (Br Setting M) F0 ∧
              (∀ v, (deg (Br Setting M) v:ℝ) <
                ε*(W \ liftVertexSet (univ \ W) A).card) ∧
              ∀ j, CatalogGen C0 Rc (Zstrat Setting M j) := by
  intro dimD dimC dimE dimD' dimC' dimE' sizeCell protection
  let d := CatalogNative.Explicit.catalogDimension β h
  let c := CatalogNative.Explicit.catalogCoefficient β h
  let E := CatalogNative.Explicit.catalogColumn β h
  let d' := CatalogNative.Explicit.catalogDimension (α/2) h
  let c' := CatalogNative.Explicit.catalogCoefficient (α/2) h
  let E' := CatalogNative.Explicit.catalogColumn (α/2) h
  intro P εcap δcap hεcap hδcap
  have hδB : 0 < min δcap (coreDelta β h) :=
    lt_min hδcap (by unfold coreDelta; positivity)
  intro rateBank toleranceBank
  let nB := CatalogNative.Explicit.bankOrder α β εcap (min δcap (coreDelta β h)) h P
  intro V I _ H F W A F0 hn h3 h4 h3A h4A hF0
  let W' := W \ liftVertexSet (univ \ W) A
  change max nB (coreN0 β h) ≤ (W \ liftVertexSet (univ \ W) A).card at hn
  have hnB : nB ≤ W'.card := (le_max_left _ _).trans hn
  have hnCore : coreN0 β h ≤ W'.card := (le_max_right _ _).trans hn
  have hc3 : SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {x // x ∈ W'} → V))
      (H.lab ∘ Subtype.val) F β :=
    nested_prepared_commonNbrCond_direct H F W A β h3A
  have hc4 : SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {x // x ∈ W'} → V))
      (H.lab ∘ Subtype.val) F β h :=
    nested_prepared_hingeCond_direct H F W A β h h4A
  obtain ⟨C0,qm,z,hqm,hqlo,hz',hCZ,hProtected⟩ :=
    CatalogNative.Explicit.native_protected_geometric_bank_early_protection_explicit
      α β h hα hβ P εcap (min δcap (coreDelta β h)) hεcap hδB H F W' hnB h3 h4 hc3 hc4
  have hzcap : (z:ℝ) ≤ δcap*W'.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzcore : (z:ℝ) ≤ coreDelta β h*W'.card := hz'.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  obtain ⟨hM,hDis,hDeg⟩ := hProtected F0 hF0
  have hCat := catalogGen_on_protected_strata_explicit hβ hc3 hc4 hnCore C0
    hzcore hCZ F0 hM
  exact ⟨C0,qm,z,hqm,hqlo,hzcap,hCZ,hM,hDis,hDeg,hCat⟩
def stockBankOrder (α C β εcap δcap αPool qPool εRoute : ℝ) (h P t : ℕ)
    (ρcap τcap : ℝ) : ℕ :=
  max (resourceOrder α C h αPool qPool εRoute
      (CatalogNative.Explicit.bankProtectionBudget α β h/2) t ρcap τcap)
    ⌈2*(preparedBankOrder α β εcap δcap h P:ℝ)/qPool⌉₊

theorem stock_bank_on_prepared_window_with_structured_future_early_protection_explicit {I : Type}
    (F : Set (Multiset I)) (α C βBank : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hβBank : 0 < βBank) :
      ∀ P : ℕ, ∀ εcap δcap : ℝ, 0 < εcap → 0 < δcap →
        ∀ (αPool qPool εRoute : ℝ) (t : ℕ),
          0 < αPool → 0 < qPool → 0 < εRoute → Odd t → 3 ≤ t →
          ∀ ρcap τcap : ℝ, 0 < ρcap → 0 < τcap →
            ∀ {V : Type} [Fintype V]
                (H : Host V I) (φ : Finset V → ℝ)
                (W : Finset V) (A : Finset (Survivors (univ \ W)))
                (U : Finset V) (T S : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT dS : ℕ),
                let W' := W \ liftVertexSet (univ \ W) A
                stockBankOrder α C βBank εcap δcap αPool qPool εRoute h P t ρcap τcap ≤ Fintype.card V →
                IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
                CommonNbrCond H F α → HingeCond H F α h →
                qPool * Fintype.card V / 2 ≤ W'.card →
                (∀ u v : V, u ≠ v → ∀ k : I,
                  ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
                  qPool * αPool * Fintype.card V / 2 ≤
                    ((commonNbrs H k u v) ∩ W').card) →
                S07V27.RouteProp H.G H.lab F t εRoute W' →
                CommonNbrCond
                  (restrictedHost (restrictedHost H (univ \ W)) A) F βBank →
                HingeCond
                  (restrictedHost (restrictedHost H (univ \ W)) A) F βBank h →
                IsDecomposition H F T DT → Disjoint T S →
                Disjoint W' U → (∀ e ∈ S, ∀ v ∈ e, v ∈ U) →
                (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ (resourceStockBudget α C)*Fintype.card V →
                (dS:ℝ) ≤ ((CatalogNative.Explicit.bankProtectionBudget α βBank h)/2)*W'.card →
                (∀ v, degIn T v ≤ dT) →
                (dT : ℝ) ≤ (resourceTerminalBudget α C h αPool qPool εRoute ((CatalogNative.Explicit.bankProtectionBudget α βBank h)/2) t) * Fintype.card V →
                ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V))
                  (C0 : CoreCompression H.G H.lab F W' (CatalogNative.Explicit.catalogDimension βBank h) (CatalogNative.Explicit.catalogCoefficient βBank h) (CatalogNative.Explicit.catalogColumn βBank h)) (qm z : ℕ),
                  IsDecomposition H F (cover D) D ∧
                  Disjoint (cover D) (T ∪ S) ∧
                  (∀ v, (degIn (cover D) v : ℝ) < (resourceInputBudget αPool qPool εRoute ((CatalogNative.Explicit.bankProtectionBudget α βBank h)/2) t ρcap τcap) * Fintype.card V) ∧
                  (∀ u v, H.G.Adj u v →
                    (BasalIncidence.Explicit.rawStockCompletion α (resourceInputBudget αPool qPool εRoute ((CatalogNative.Explicit.bankProtectionBudget α βBank h)/2) t ρcap τcap)) * Fintype.card V ≤ (good H F D u v).card) ∧
                  Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
                  (∀ e ∈ R, ∃ v ∈ e, v ∈ W') ∧ Disjoint R S ∧
                  (∀ v, (edeg R v : ℝ) ≤ (resourceOutputBudget qPool ((CatalogNative.Explicit.bankProtectionBudget α βBank h)/2) τcap) * Fintype.card V) ∧
                  (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
                    (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W') ∧
                    ∀ v, (edeg Y0 v : ℝ) ≤ (resourceOutputBudget qPool ((CatalogNative.Explicit.bankProtectionBudget α βBank h)/2) τcap) * Fintype.card V) ∧
                  (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
                    ∃ Ps Y : Finset (Sym2 V),
                      R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
                      (∀ e ∈ Y, ∀ v ∈ e, v ∈ W') ∧
                      (∀ v, (edeg Y v : ℝ) ≤ (resourceOutputBudget qPool ((CatalogNative.Explicit.bankProtectionBudget α βBank h)/2) τcap) * Fintype.card V) ∧
                      IsPhysical H F Y) ∧
                  0 < qm ∧ (CatalogNative.Explicit.bankTolerance α βBank εcap h) / 4 * W'.card ≤ (qm : ℝ) ∧
                  (z : ℝ) ≤ δcap * W'.card ∧
                  (∀ Z : Finset V, Z.card ≤ z →
                    Nonempty (DelCompression H.G H.lab F Z (CatalogNative.Explicit.catalogDimension (α/2) h) (CatalogNative.Explicit.catalogCoefficient (α/2) h) (CatalogNative.Explicit.catalogColumn (α/2) h))) ∧
                  let Rc := S07V42.Explicit.catRadius βBank (CatalogNative.Explicit.catalogDimension βBank h) (CatalogNative.Explicit.catalogCoefficient βBank h) (CatalogNative.Explicit.catalogColumn βBank h) (CatalogNative.Explicit.catalogDimension (α/2) h) (CatalogNative.Explicit.catalogCoefficient (α/2) h) (CatalogNative.Explicit.catalogColumn (α/2) h)
                  let F0 := ((cover D ∪ R) ∪ T) ∪ S
                  let Setting := S07V47.protSetting C0 Rc P qm (CatalogNative.Explicit.bankCellSize α βBank h) z F0
                  let M := ⌊(preparedBankRoundRate α βBank εcap δcap h P) * (W'.card : ℝ)^2⌋₊
                  MacroBank Setting (Fintype.card (Cat (CatalogNative.Explicit.catalogDimension βBank h) Rc)) M ∧
                    Disjoint (Br Setting M) F0 ∧
                    (∀ v, (deg (Br Setting M) v : ℝ) < (CatalogNative.Explicit.bankTolerance α βBank εcap h) * W'.card) ∧
                    ∀ j, CatalogGen C0 Rc (Zstrat Setting M j) := by
  let ηBank := CatalogNative.Explicit.bankProtectionBudget α βBank h
  have hηBank : 0 < ηBank := CatalogNative.Explicit.bankProtectionBudget_pos h hα hβBank
  intro P εcap δcap hεcap hδcap
  let nBank := preparedBankOrder α βBank εcap δcap h P
  intro αPool qPool εRoute t hαPool hqPool hεRoute ht ht3
  intro ρcap τcap hρcap hτcap
  let nResources := resourceOrder α C h αPool qPool εRoute (ηBank/2) t ρcap τcap
  intro V _ H φ W A U T S DT dT dS W' hn hSeed hPhys h3 h4 hW hPool hRoute
    h3A h4A hT hTS hWU hSU hSd hScap hSMacro hTd hTcap
  change max nResources ⌈2*(nBank:ℝ)/qPool⌉₊ ≤ Fintype.card V at hn
  have hnResources : nResources ≤ Fintype.card V :=
    (le_max_left _ _).trans hn
  have hnCeil : ⌈2 * (nBank : ℝ) / qPool⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans hn
  have hnBank : nBank ≤ W'.card := by
    have hceil : (⌈2 * (nBank : ℝ) / qPool⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hnCeil
    have h2n : 2 * (nBank : ℝ) ≤
        (⌈2 * (nBank : ℝ) / qPool⌉₊ : ℝ) * qPool :=
      (div_le_iff₀ hqPool).mp (Nat.le_ceil _)
    have hscale := mul_le_mul_of_nonneg_right hceil hqPool.le
    exact_mod_cast (show (nBank : ℝ) ≤ W'.card by
      nlinarith [hW,h2n,hscale])
  obtain ⟨D,R,hD,hDT,hDd,hSupply,hRdis,hR,hRinc,hRS,hRd,hFsmall,hY0,hMode⟩ :=
    fixed_window_resources_explicit_protecting_vertices F α C h hα hC
      αPool qPool εRoute (ηBank/2) t hαPool hqPool hεRoute (by positivity) ht ht3
      ρcap τcap hρcap hτcap H φ W' U T S DT dT dS hnResources hSeed hPhys h3 h4 hW hPool
      hRoute hT hTS hWU hSU hSd hScap hTd hTcap
  let F0 := ((cover D ∪ R) ∪ T) ∪ S
  have hF0 : ∀ v, (degIn F0 v:ℝ) ≤ ηBank*W'.card := by
    intro v
    have hu := edeg_union_le ((cover D ∪ R) ∪ T) S v
    change degIn F0 v ≤ degIn ((cover D ∪ R) ∪ T) v + degIn S v at hu
    have huR : (degIn F0 v:ℝ) ≤ degIn ((cover D ∪ R) ∪ T) v + degIn S v := by
      exact_mod_cast hu
    have hs : (degIn S v:ℝ) ≤ dS := by exact_mod_cast hSd v
    nlinarith only [huR,hFsmall v,hs,hSMacro]
  obtain ⟨C0,qm,z,hqm,hql,hz,hCZ,hMacro,hBDis,hBDeg,hCat⟩ :=
    bank_on_prepared_fixed_window_early_protection_explicit α βBank h hα hβBank
      P εcap δcap hεcap hδcap H F W A F0 hnBank h3 h4 h3A h4A hF0
  exact ⟨D,R,C0,qm,z,hD,hDT,hDd,hSupply,hRdis,hR,hRinc,hRS,hRd,hY0,hMode,
    hqm,hql,hz,hCZ,hMacro,hBDis,hBDeg,hCat⟩
#print axioms bank_on_prepared_fixed_window_early_protection_explicit
#print axioms stock_bank_on_prepared_window_with_structured_future_early_protection_explicit
end TypedTriangle.Vortex.Explicit
