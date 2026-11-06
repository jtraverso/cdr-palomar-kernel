module
public import RequestProject.TypedTriangle.PaschAmbientNativeCellSupply
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Pasch.AmbientBank
open S07V40 S07V42 S07V42.Explicit S07V43 CatalogNative.Explicit ProtectedBank

/-- Full ambient bank with geometry and all numeric caps fixed on X. The
complete seed R0 is used throughout selection; both statistical budgets and
the actual off/on witnesses survive the projection to the ordinary bank. -/
theorem native_ambient_seeded_bank (α β : ℝ) (h : ℕ) (hα : 0<α) (hβ : 0<β)
    (d c E d' c' E' : ℕ) {X V I : Type} [Fintype X] [Fintype V]
    (ι : X ↪ V) (J : Host X I) (H : Host V I) (F : Set (Multiset I))
    (hAdj : ∀ x y, J.G.Adj x y → H.G.Adj (ι x) (ι y)) (hLab : ∀ x, J.lab x=H.lab (ι x))
    (W : Finset X) (h3 : CommonNbrCond J F α) (h4 : HingeCond J F α h)
    (hc3 : SparseEdge.CommonNbrCond (J.G.comap (Subtype.val : {x // x∈W} → X))
      (J.lab ∘ Subtype.val) F β)
    (hc4 : SparseEdge.HingeCond (J.G.comap (Subtype.val : {x // x∈W} → X))
      (J.lab ∘ Subtype.val) F β h)
    (hnC : coreN0 β h ≤ W.card) (hn : catalogCellOrder α β h d c E d' c' E' ≤ W.card)
    (C0 : CoreCompression J.G J.lab F W d c E) (P q zmax N b0 : ℕ) (hq : 0<q)
    (hz : (zmax:ℝ) ≤ min (catalogCellDeletionBudget α β h) (coreDelta β h)*W.card)
    (hbud : ((b0+q+(childSetting C0 (catRadius β d c E d' c' E') P q
      (catalogCellSize α β h d c E d' c' E') zmax).Bstar*
      (catalogCellSize α β h d c E d' c' E'):ℕ):ℝ) ≤ catalogCellDegreeBudget α β h*W.card)
    (CZ : ∀ Z : Finset X, Z.card≤zmax → DelCompression J.G J.lab F Z d' c' E')
    (hcap : 2*(catalogCellSize α β h d c E d' c' E')*
      (childSetting C0 (catRadius β d c E d' c' E') P q
        (catalogCellSize α β h d c E d' c' E') zmax).Bstar*N ≤ q*zmax)
    (F0 : Finset (Sym2 V)) (hF0 : ∀ x, degIn (pullEdges ι F0) x≤b0)
    (R0 : Finset (Finset V)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0) :
    let Sloc := protect (childSetting C0 (catRadius β d c E d' c' E') P q
      (catalogCellSize α β h d c E d' c' E') zmax) (pullEdges ι F0)
    let S := liftSetting ι Sloc
    let Ub := weightedCatalogSupport α β h d c E d' c' E'
    let pay := Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' (L0+2)
    ∃ es : List (RichBank.Entry V (Cat d (catRadius β d c E d' c' E')) P),
      RichBank.Seeded.RunInv H F S Ub pay R0 N es ∧ (RichBank.toBank es).Valid S.basal S.w S.g ∧
      PairCodegreeBound (RichBank.modes es) 2 ∧
      (count (RichBank.modes es):ℝ) ≤ ((S.Bstar*N:ℕ):ℝ)*pay ∧
      PairCodegreeBound (R0∪RichBank.modes es) (L0+2) ∧
      (count (R0∪RichBank.modes es):ℝ) ≤ count R0+((S.Bstar*N:ℕ):ℝ)*pay ∧
      satSet q (RichBank.usedEdges es) ⊆ (univ : Finset X).map ι ∧
      (pullVertices ι (satSet q (RichBank.usedEdges es))).card=(satSet q (RichBank.usedEdges es)).card := by
  have hzδ : (zmax:ℝ) ≤ catalogCellDeletionBudget α β h*W.card :=
    hz.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hSupply := native_ambient_cell_supply α β h hα hβ d c E d' c' E' ι J H F hAdj hLab
    W h3 h4 hc3 hc4 hnC hn C0 P q zmax b0 hzδ hbud CZ F0 hF0 R0 L0 hR0
  have hPay : 0 ≤ Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' (L0+2) :=
    mul_nonneg (Ambient.orderRatio_nonneg ι) (RichBank.catalogCellPotentialCost_nonneg hα h d c E d' c' E' (L0+2))
  obtain ⟨es,hInv,hBank,hLocalCodegree,hLocalCount,hExternalCount⟩ :=
    RichBank.Seeded.exists_valid_bank_with_budget hSupply hq hPay N hcap
  refine ⟨es,hInv,hBank,hLocalCodegree,hLocalCount,hInv.history.external_codegree hR0,hExternalCount,?_,?_⟩
  · exact valid_history_saturated_subset_image ι _ hInv.history.local_history hq
  · exact valid_history_saturated_pull_card ι _ hInv.history.local_history hq

end TypedTriangle.Pasch.AmbientBank
#print axioms TypedTriangle.Pasch.AmbientBank.native_ambient_seeded_bank
