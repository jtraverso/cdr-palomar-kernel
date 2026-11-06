module
public import RequestProject.TypedTriangle.PaschActualBankActivationCore
public import RequestProject.TypedTriangle.PaschBankTotalPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.AmbientBank
open S07V40 S07V42 S07V42.Explicit S07V43 S07V44 ProtectedBank CatalogNative.Explicit

/-- Prepare ONE compression and its literal numerical quotas, then construct
the rich bank against resources already supplied in F0. No stock, withdrawal,
terminal reserve, future core or canonical macro-run is chosen here. -/
theorem prepared_native_ambient_bank
    (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (P : ℕ) (εcap δcap : ℝ) (hεcap : 0 < εcap) (hδcap : 0 < δcap) :
    ∀ {X V I : Type} [Fintype X] [Fintype V] (ι : X ↪ V)
      (H : Host X I) (Hambient : Host V I) (F : Set (Multiset I)),
      (∀ x y,H.G.Adj x y → Hambient.G.Adj (ι x) (ι y)) →
      (∀ x,H.lab x=Hambient.lab (ι x)) →
      ∀ W : Finset X, bankOrder α β εcap δcap h P ≤ W.card →
      CommonNbrCond H F α → HingeCond H F α h →
      SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → X))
        (H.lab ∘ Subtype.val) F β →
      SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → X))
        (H.lab ∘ Subtype.val) F β h →
      ∀ F0 : Finset (Sym2 V),
      (∀ x,(degIn (pullEdges ι F0) x:ℝ) ≤ bankProtectionBudget α β h*W.card) →
      ∀ (R0 : Finset (Finset V)) (L0 : ℕ), PairCodegreeBound R0 L0 →
      let q := ⌊bankTolerance α β εcap h*W.card/2⌋₊
      let z := ⌊bankDeletionBudget α β δcap h*W.card⌋₊
      ∃ C0 : CoreCompression H.G H.lab F W
        (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h),
      ∃ CZ : ∀ Z : Finset X,Z.card ≤ z → DelCompression H.G H.lab F Z
        (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h),
      0 < q ∧ bankTolerance α β εcap h/4*W.card ≤ (q:ℝ) ∧
      (z:ℝ) ≤ bankDeletionBudget α β δcap h*W.card ∧ (z:ℝ) ≤ δcap*W.card ∧
      (∀ Z : Finset X,Z.card ≤ z → CatalogGen C0 (bankCatalogRadius α β h) Z) ∧
      let Sloc := protect (childSetting C0 (bankCatalogRadius α β h) P q (bankCellSize α β h) z) (pullEdges ι F0)
      let S := liftSetting ι Sloc
      let N := ⌊bankRoundRate α β εcap δcap h P*(W.card:ℝ)^2⌋₊
      let Ub := weightedCatalogSupport α β h
        (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h)
        (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h)
      let pay := Ambient.orderRatio ι*catalogCellPotentialCost α β h
        (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h)
        (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h) (L0+2)
      ChainBound S (Fintype.card (Cat (catalogDimension β h) (bankCatalogRadius α β h))) ∧
      2*S.E*S.Bstar*N ≤ S.q*S.zmax ∧
      ∃ es : List (RichBank.Entry V (Cat (catalogDimension β h) (bankCatalogRadius α β h)) P),
      RichBank.Seeded.RunInv Hambient F S Ub pay R0 N es ∧
      (RichBank.toBank es).Valid S.basal S.w S.g ∧
      Disjoint (RichBank.usedEdges es) F0 ∧
      (∀ v,(deg (RichBank.usedEdges es) v:ℝ) < bankTolerance α β εcap h*W.card) ∧
      PairCodegreeBound (RichBank.modes es) 2 ∧
      (count (RichBank.modes es):ℝ) ≤ ((S.Bstar*N:ℕ):ℝ)*pay ∧
      PairCodegreeBound (R0∪RichBank.modes es) (L0+2) ∧
      (count (R0∪RichBank.modes es):ℝ) ≤ count R0+((S.Bstar*N:ℕ):ℝ)*pay ∧
      satSet q (RichBank.usedEdges es) ⊆ (univ : Finset X).map ι ∧
      (pullVertices ι (satSet q (RichBank.usedEdges es))).card=(satSet q (RichBank.usedEdges es)).card := by
  let d := catalogDimension β h
  let c := catalogCoefficient β h
  let E := catalogColumn β h
  let d' := catalogDimension (α/2) h
  let c' := catalogCoefficient (α/2) h
  let E' := catalogColumn (α/2) h
  let Ecell := bankCellSize α β h
  let εb := catalogCellDegreeBudget α β h
  let δb := min (catalogCellDeletionBudget α β h) (coreDelta β h)
  let δc := ExplicitGeometry.deletionBudget α h
  let nc := catalogCompressionOrder α β h
  let nb := bankCellOrder α β h
  have hεb : 0<εb := catalogCellDegreeBudget_pos h hα hβ
  have hδb : 0<δb := lt_min (catalogCellDeletionBudget_pos h hα hβ) (by unfold coreDelta; positivity)
  have hδc : 0<δc := (ExplicitGeometry.deletionBudget_spec hα h).1
  let ε := min (εb/2) εcap
  have hε : 0<ε := lt_min (by positivity) hεcap
  let δ := min δc (min δb δcap)
  have hδ : 0<δ := lt_min hδc (lt_min hδb hδcap)
  let B := 2*Fintype.card (Cat d (bankCatalogRadius α β h))*P
  have hCat : Fintype.card (Cat d (bankCatalogRadius α β h)) = bankCatalogSize α β h := by
    simpa only [d,bankCatalogSize] using card_Cat (catalogDimension β h) (bankCatalogRadius α β h)
  have hB : B = bankCopies α β h P := by dsimp [B,bankCopies]; rw [hCat]
  let κ := quadraticBankRate ε δ Ecell B
  let nq := quadraticBankOrder ε δ Ecell B
  intro X V I _ _ ι H Hambient F hAdj hLab W hn h3 h4 hc3 hc4 F0 hF0 R0 L0 hR0
  change max nc (max nb (max (coreN0 β h) (quadraticBankOrder ε δ Ecell (bankCopies α β h P)))) ≤ W.card at hn
  rw [← hB] at hn
  have hκEq : bankRoundRate α β εcap δcap h P = κ := by
    dsimp only [bankRoundRate,κ,bankTolerance,bankProtectionBudget,bankDeletionBudget,ε,εb,δ,δc,δb,Ecell]
    rw [hB]
  simp only [hκEq]

  have hnc : nc ≤ W.card := (le_max_left _ _).trans hn
  have hnb : nb ≤ W.card := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnCore : coreN0 β h ≤ W.card :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnq : nq ≤ W.card :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  obtain ⟨⟨C0⟩,hCZ⟩ := native_all_catalog_compressions_explicit α β h hα hβ H F W hnc h3 h4 hc3 hc4
  let q := ⌊ε*W.card/2⌋₊
  let z := ⌊δ*W.card⌋₊
  obtain ⟨hq,hz,hdegree,hcap,hql⟩ := quadratic_bank_budget_explicit ε δ Ecell B hε hδ W.card hnq
  have hzC : (z:ℝ) ≤ δc*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzB : (z:ℝ) ≤ δb*W.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by positivity))
  have hzCap : (z:ℝ) ≤ δcap*W.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by positivity))
  let CZ : ∀ Z : Finset X, Z.card ≤ z → DelCompression H.G H.lab F Z d' c' E' :=
    fun Z hZ => Classical.choice (hCZ Z ((Nat.cast_le.mpr hZ).trans hzC))
  let b0 := ⌊(εb/2)*W.card⌋₊
  have hb0 : ∀ x,degIn (pullEdges ι F0) x ≤ b0 := fun x => Nat.le_floor (hF0 x)
  have hb0R : (b0:ℝ) ≤ (εb/2)*W.card := Nat.floor_le (by positivity)
  have hdegreeHalf : ((q+B*Ecell:ℕ):ℝ) ≤ (εb/2)*W.card := hdegree.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hbudget : ((b0+q+B*Ecell:ℕ):ℝ) ≤ εb*W.card := by
    push_cast at hdegreeHalf ⊢
    linarith
  have hzcore : (z:ℝ) ≤ coreDelta β h*W.card := hzB.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hGen : ∀ Z : Finset X,Z.card ≤ z → CatalogGen C0 (bankCatalogRadius α β h) Z := by
    intro Z hZ
    exact catalog_generates_explicit hβ hc3 hc4 hnCore C0
      ((Nat.cast_le.mpr hZ).trans hzcore) (CZ Z hZ)
  let Sloc := protect (childSetting C0 (bankCatalogRadius α β h) P q Ecell z) (pullEdges ι F0)
  let S := liftSetting ι Sloc
  have hChainLocal := S07V43.Explicit.childSetting_chainBound_explicit hβ hc3 hc4 hnCore
    C0 P q Ecell z hzcore CZ
  have hChain : ChainBound S (Fintype.card (Cat d (bankCatalogRadius α β h))) :=
    liftSetting_chainBound ι Sloc _ hChainLocal
  have hRunCap : 2*S.E*S.Bstar*⌊κ*(W.card:ℝ)^2⌋₊ ≤ S.q*S.zmax := hcap
  obtain ⟨es,hInv,hBank,hLocalCodegree,hLocalCount,hExternalCodegree,hExternalCount,hSat,hPullCard⟩ :=
    native_ambient_seeded_bank α β h hα hβ d c E d' c' E' ι H Hambient F hAdj hLab
      W h3 h4 hc3 hc4 hnCore hnb C0 P q z ⌊κ*(W.card:ℝ)^2⌋₊ b0
      hq hzB hbudget CZ hcap F0 hb0 R0 L0 hR0
  have hDis := protected_history_disjoint ι
    (childSetting C0 (bankCatalogRadius α β h) P q Ecell z) F0 hInv.history.local_history
  have hDeg : ∀ v,(deg (RichBank.usedEdges es) v:ℝ) < ε*W.card := by
    intro v
    have hv : deg (RichBank.usedEdges es) v < q+B*Ecell := hInv.maxdeg v
    exact (show (deg (RichBank.usedEdges es) v:ℝ) < (q+B*Ecell:ℕ) by exact_mod_cast hv).trans_le hdegree
  refine ⟨C0,CZ,hq,hql,hz,hzCap,hGen,hChain,hRunCap,es,hInv,hBank,hDis,hDeg,
    hLocalCodegree,hLocalCount,hExternalCodegree,hExternalCount,hSat,hPullCard⟩

end TypedTriangle.Pasch.AmbientBank
#print axioms TypedTriangle.Pasch.AmbientBank.prepared_native_ambient_bank
