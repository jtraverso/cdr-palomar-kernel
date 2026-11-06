module
public import RequestProject.TypedTriangle.PaschSeededNativeCellSupply
public import RequestProject.TypedTriangle.PaschSeededBankRun
public import RequestProject.TypedTriangle.PaschNativeRichBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch.RichBank.Seeded
open S07V40 S07V42 S07V42.Explicit S07V43 CatalogNative.Explicit ProtectedBank

/-- The native rich bank is built with the original parameter bounds. The
ordinary bank is its final projection; its modes are the stored decompositions
chosen during the same run, rather than a later independent choice. -/
theorem native_seeded_bank (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (d c E d' c' E' : ℕ) {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hc3 : SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β)
    (hc4 : SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β h)
    (hnC : coreN0 β h ≤ W.card) (hn : catalogCellOrder α β h d c E d' c' E' ≤ W.card)
    (C0 : CoreCompression H.G H.lab F W d c E) (P q zmax N b0 : ℕ) (hq : 0 < q)
    (hz : (zmax:ℝ) ≤ min (catalogCellDeletionBudget α β h) (coreDelta β h)*W.card)
    (hbud : ((b0+q+(childSetting C0 (catRadius β d c E d' c' E') P q
      (catalogCellSize α β h d c E d' c' E') zmax).Bstar*
      (catalogCellSize α β h d c E d' c' E'):ℕ):ℝ) ≤ catalogCellDegreeBudget α β h*W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H.G H.lab F Z d' c' E')
    (hcap : 2*(catalogCellSize α β h d c E d' c' E')*
      (childSetting C0 (catRadius β d c E d' c' E') P q
        (catalogCellSize α β h d c E d' c' E') zmax).Bstar*N ≤ q*zmax)
    (F0 : Finset (Sym2 V)) (hF0 : ∀ v, degIn F0 v ≤ b0)
    (R0 : Finset (Finset V)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0) :
    let S := protect (childSetting C0 (catRadius β d c E d' c' E') P q
      (catalogCellSize α β h d c E d' c' E') zmax) F0
    let Ub := weightedCatalogSupport α β h d c E d' c' E'
    let pay := catalogCellPotentialCost α β h d c E d' c' E' (L0+2)
    ∃ es : List (Entry V (Cat d (catRadius β d c E d' c' E')) P),
      RunInv H F S Ub pay R0 N es ∧ (toBank es).Valid S.basal S.w S.g ∧
      PairCodegreeBound (modes es) 2 ∧ (count (modes es):ℝ) ≤ ((S.Bstar*N:ℕ):ℝ)*pay ∧
      PairCodegreeBound (R0∪modes es) (L0+2) ∧
      (count (R0∪modes es):ℝ) ≤ count R0+((S.Bstar*N:ℕ):ℝ)*pay := by
  have hzδ : (zmax:ℝ) ≤ catalogCellDeletionBudget α β h*W.card :=
    hz.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hSupply := native_seeded_cell_supply α β h hα hβ d c E d' c' E' H F W h3 h4 hc3 hc4
    hnC hn C0 P q zmax b0 hzδ hbud CZ F0 hF0 R0 L0 hR0
  obtain ⟨es, hInv, hBank, hLocalCodegree, hLocalCount, hExternalCount⟩ :=
    exists_valid_bank_with_budget hSupply hq
      (RichBank.catalogCellPotentialCost_nonneg hα h d c E d' c' E' (L0+2)) N hcap
  exact ⟨es, hInv, hBank, hLocalCodegree, hLocalCount,
    hInv.history.external_codegree hR0, hExternalCount⟩

end TypedTriangle.Pasch.RichBank.Seeded
#print axioms TypedTriangle.Pasch.RichBank.Seeded.native_seeded_bank
