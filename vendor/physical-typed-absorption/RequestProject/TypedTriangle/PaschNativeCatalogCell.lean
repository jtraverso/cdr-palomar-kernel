module
public import RequestProject.TypedTriangle.PaschCatalogCellWindows
public import RequestProject.TypedTriangle.PaschDeletedTriangleFreeResidue
public import RequestProject.TypedTriangle.PaschSurvivingWeightedAbsorber
public import RequestProject.TypedTriangle.PaschCellModePotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open SparseEdge Dispersal S07V42 S07V42.Explicit CatalogNative.Explicit

def catalogCellPotentialCost (α β : ℝ) (h d c E d' c' E' L : ℕ) : ℝ :=
  let k := 4*rerouteSize β d c E d' c' E'
  let K := ExplicitCertificate.uniformCertCost (α/2) h
  let Ub := weightedCatalogSupport α β h d c E d' c' E'
  ((K*k:ℕ):ℝ)*absorptionPotentialCost α h Ub L+
    ((9*L*((Ub.choose 3).choose 2)+(Ub.choose 3).choose 3+(Ub.choose 3).choose 4:ℕ):ℝ)

theorem native_catalog_cell_with_potential (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (d c E d' c' E' : ℕ) :

      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        coreN0 β h ≤ W.card → catalogCellOrder α β h d c E d' c' E' ≤ W.card →
        ∀ C0 : CoreCompression H.G H.lab F W d c E,
        ∀ Z : Finset V, (Z.card:ℝ) ≤ catalogCellDeletionBudget α β h*W.card →
        DelCompression H.G H.lab F Z d' c' E' →
        ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, degIn B v ≤ b) →
          (b:ℝ) ≤ catalogCellDegreeBudget α β h*W.card →
        ∀ (Rprev : Finset (Finset V)) (L : ℕ), PairCodegreeBound Rprev L →
          (∀ T ∈ Rprev, triEdges T ⊆ B) →
        ∀ v : Cat d (catRadius β d c E d' c' E'),
          gCat C0 (catRadius β d c E d' c' E') v ∈ KZ H.G H.lab F W Z → ∀ σ : Bool,
        ∃ A Y : Finset (Sym2 V), IsAbsorber H F A Y ∧ Disjoint (A∪Y) B ∧
          (∀ e ∈ A∪Y, ∀ z ∈ Z, z ∉ e) ∧
          (∀ e ∈ Y, e ∈ SparseEdge.edges (indG H.G (W\Z))) ∧
          (A∪Y).card ≤ catalogCellSize α β h d c E d' c' E' ∧
          chargeQ H.G H.lab F W Y =
            (if σ then gCat C0 (catRadius β d c E d' c' E') v
              else -gCat C0 (catRadius β d c E d' c' E') v) ∧
          ∃ (U0 : Finset V) (Doff Don : Finset (Finset V)), Fresh U0 A ∧ Inside U0 Y ∧
            Disjoint U0 Z ∧ (U0 ∪ support A).card ≤ weightedCatalogSupport α β h d c E d' c' E' ∧
            IsDecomposition H F A Doff ∧ IsDecomposition H F (A∪Y) Don ∧
            PairCodegreeBound (Doff∪Don) 2 ∧ Disjoint (Doff∪Don) Rprev ∧
            (Doff∪Don).card ≤ (weightedCatalogSupport α β h d c E d' c' E').choose 3 ∧
            (supportIncrementCost Rprev U0 (support A):ℝ) ≤ catalogCellPotentialCost α β h d c E d' c' E' L ∧
            (count ((Doff∪Don)∪Rprev):ℝ) ≤ count Rprev + catalogCellPotentialCost α β h d c E d' c' E' L := by
  let U := rerouteSize β d c E d' c' E'
  let εA := boundedPieceBudget (α/2) h
  let EA := boundedPieceSize (α/2) h (4*U)
  let nA := boundedPieceOrder (α/2) h (4*U)
  have hεA : 0<εA := boundedPieceBudget_pos h (by positivity)
  let δ₀ := ExplicitGeometry.deletionBudget α h
  obtain ⟨hδ₀,hδhalf,hWin⟩ := ExplicitGeometry.deletionBudget_spec hα h
  intro V I _ H F W h3 h4 hc3 hc4 hnC hn C0 Z hZ CZ B b hB hb Rprev L hL hRB v hv σ
  change 2*nA+⌈40*(U:ℝ)/β⌉₊+1 ≤ W.card at hn

  have hWn : (W.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ W
  have hW0 : (0:ℝ) ≤ W.card := by positivity
  have hZ₀ : (Z.card:ℝ) ≤ δ₀*Fintype.card V :=
    (hZ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW0)).trans
      (mul_le_mul_of_nonneg_left hWn hδ₀.le)
  have hZcore : (Z.card:ℝ) ≤ coreDelta β h*W.card :=
    hZ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW0)
  obtain ⟨x,hxM,hxL,hxU,hxc⟩ := native_reroute_explicit h hβ d c E d' c' E' hc3 hc4 hnC C0 hZcore CZ v hv
  let xs : Sym2 V → ℤ := if σ then x else -x
  have hxsM : xs ∈ MZ H.G H.lab F W Z := by
    dsimp [xs]; split_ifs <;> first | exact hxM | exact neg_mem hxM
  have hxsL : xs ∈ LamDel H.G H.lab F Z := by
    dsimp [xs]; split_ifs <;> first | exact hxL | exact neg_mem hxL
  have hxsU : Dispersal.l1E xs ≤ U := by
    dsimp [xs]; split_ifs
    · exact hxU
    · simpa only [Dispersal.l1E,Pi.neg_apply,abs_neg] using hxU
  have hxsc : clsQ H.G H.lab F W xs =
      (if σ then gCat C0 (catRadius β d c E d' c' E') v else -gCat C0 (catRadius β d c E d' c' E') v) := by
    dsimp [xs]; split_ifs
    · exact hxc
    · rw [←hxc]; rfl
  have hZhalf : (Z.card:ℝ) ≤ (Fintype.card V:ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right hδhalf (by positivity : (0:ℝ) ≤ Fintype.card V)
    linarith
  have hgeom := hWin (by positivity : (0:ℝ) ≤ Fintype.card V) hZ₀
  obtain ⟨hg3,hg4⟩ := original_geometry_restrictedHost hα.le h3 h4 Z hgeom.1 hgeom.2
  have hcnt := card_survivors_add_card Z
  have hcntR : (Fintype.card (Survivors Z):ℝ)+Z.card = Fintype.card V := by exact_mod_cast hcnt
  have hNA : nA ≤ Fintype.card (Survivors Z) := by
    have hbig : (2:ℝ)*nA ≤ Fintype.card V := by
      have hh : 2*nA ≤ W.card := by omega
      exact_mod_cast hh.trans (card_le_univ W)
    exact_mod_cast (by linarith : (nA:ℝ) ≤ Fintype.card (Survivors Z))
  have hbA : (b:ℝ) ≤ εA*Fintype.card (Survivors Z) := by
    have hh := hb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW0)
    have hw : (W.card:ℝ) ≤ 2*Fintype.card (Survivors Z) := by linarith
    have hh' := mul_le_mul_of_nonneg_left hw hεA.le
    nlinarith
  have hbβ : (b:ℝ) ≤ β/8*W.card := hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW0)
  have hzβ : (Z.card:ℝ) ≤ β/2*W.card :=
    hZcore.trans (mul_le_mul_of_nonneg_right (coreDelta_le hβ h) hW0)
  have hbig : 40*(U:ℝ)/β < W.card := by
    have hh := Nat.le_ceil (40*(U:ℝ)/β)
    have hh' : ((2*nA+⌈40*(U:ℝ)/β⌉₊+1:ℕ):ℝ) ≤ W.card := by exact_mod_cast hn
    push_cast at hh'
    linarith [show (0:ℝ) ≤ nA by positivity]
  have hroom : 5*(U:ℝ)+Z.card+2*b < β*W.card := by
    rw [div_lt_iff₀ hβ] at hbig
    linarith
  obtain ⟨Y,hYL,hYB,hYE,hYc⟩ := polarize hc3 Z hB hxsM hxsU hroom
  have hlatD : SparseEdge.lattice (indG H.G (W\Z)) H.lab F ≤ LamDel H.G H.lab F Z :=
    S07V37.lattice_mono (indG_le_delG H.G sdiff_disjoint) H.lab F
  have hlatC : SparseEdge.lattice (indG H.G (W\Z)) H.lab F ≤ LamCore H.G H.lab F W :=
    S07V37.lattice_mono (indG_mono H.G sdiff_subset) H.lab F
  have hYphys : IsPhysical (vertexDeleted H Z) F Y := by
    have heq : ind Y = (ind Y-xs)+xs := by abel
    change ind Y ∈ LamDel H.G H.lab F Z
    rw [heq]
    exact add_mem (hlatD hYL) hxsL
  have hYav : ∀ e ∈ Y, ∀ z ∈ Z, z ∉ e := by
    intro e he z hz hze
    have he' := hYE e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SparseEdge.mem_edges,SimpleGraph.mem_edgeSet] at he'
      rw [Sym2.mem_iff] at hze
      rcases hze with rfl | rfl
      exacts [(mem_sdiff.mp he'.2.1).2 hz,(mem_sdiff.mp he'.2.2).2 hz]
  have hInsideY : Inside W Y := by
    intro e he x hx
    have he' := hYE e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SparseEdge.mem_edges, SimpleGraph.mem_edgeSet] at he'
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      exacts [(mem_sdiff.mp he'.2.1).1, (mem_sdiff.mp he'.2.2).1]
  obtain ⟨Y0, Dpeel, hY0Y, hY0c, hPeel, hY0phys, hFree, hClass⟩ :=
    exists_deleted_core_class_triangleFree_residue Z W Y hYphys hInsideY
  have hY0card : Y0.card ≤ 4*U := hY0c.trans hYc
  have hY0av : ∀ e ∈ Y0, ∀ z ∈ Z, z ∉ e := fun e he z hz => hYav e (hY0Y he) z hz
  have hRootBad : Disjoint (support Y0) Z := by
    rw [disjoint_left]
    intro x hx hxZ
    simp only [support, mem_filter, mem_univ, true_and] at hx
    obtain ⟨e, he, hxe⟩ := hx
    exact hY0av e he x hxZ hxe
  let K := ExplicitCertificate.uniformCertCost (α/2) h
  let Ub := weightedCatalogSupport α β h d c E d' c' E'
  have hCert : UniformCert (restrictedHost H Z) F K :=
    ExplicitCertificate.uniformCert_of_H3H4_explicit (α/2) h (by positivity)
      (restrictedHost H Z) F ((le_max_left _ _).trans hNA) hg3 hg4
  have hRoot : (support Y0).card ≤ 2*(4*U) :=
    (S07V28.card_support_le Y0).trans (Nat.mul_le_mul_left 2 hY0card)
  have hBudget : (support Y0).card + 3*(K*Y0.card) + K*Y0.card*(2*h-2) +
      3*(K*Y0.card)*(2*h-3) ≤ Ub := by
    have hm := Nat.mul_le_mul_left K hY0card
    have hm3 := Nat.mul_le_mul_left 3 hm
    have hg := Nat.mul_le_mul_right (2*h-2) hm
    have hp := Nat.mul_le_mul_right (2*h-3) hm3
    dsimp only [Ub, weightedCatalogSupport, PreparedSupply.Explicit.supplySupport,
      PreparedSupply.Explicit.absorberCost]
    change (support Y0).card + 3*(K*Y0.card) + K*Y0.card*(2*h-2) +
      3*(K*Y0.card)*(2*h-3) ≤ 2*(4*U)+3*(K*(4*U))+K*(4*U)*(2*h-2)+3*(K*(4*U))*(2*h-3)
    omega
  have hWin := catalog_cell_weighted_windows hα hβ h d c E d' c' E' W.card
    (Fintype.card V) Z.card b (by simpa only [catalogCellOrder] using hn) (card_le_univ W) hZ hb
  obtain ⟨A, U0, hA, hAB, hRootU, hU0card, hInside, hFresh, hAc, hSupport, hPhi, hU0Z, hAZ⟩ :=
    surviving_certificate_weighted_absorber hα h3 h4 Z hCert Rprev L hL B b hB Y0 hY0phys
      (support Y0) hRootBad (inside_support _) Ub hBudget hWin.1 hWin.2
  have hTotalB : Disjoint (A∪Y0) B := disjoint_union_left.mpr ⟨hAB, hYB.mono_left hY0Y⟩
  have hInsideTotal : Inside (U0∪support A) (A∪Y0) := by
    intro e he x hx
    rcases mem_union.mp he with he | he
    · exact mem_union_right _ (inside_support A e he x hx)
    · exact mem_union_left _ (hInside e he x hx)
  let pay := ((K*(4*U):ℕ):ℝ)*absorptionPotentialCost α h Ub L
  have hCost0 : 0 ≤ absorptionPotentialCost α h Ub L := by
    unfold absorptionPotentialCost gadgetPotentialCost compositePotentialCost hingePotentialCost
    positivity
  have hPhiPay : (supportIncrementCost Rprev U0 (support A):ℝ) ≤ pay :=
    hPhi.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left K hY0card) hCost0)
  have hPhiFull : (supportIncrementCost Rprev U0 (U0∪support A):ℝ) ≤ pay := by
    simpa only [supportIncrementCost, ←union_assoc, union_self] using hPhiPay
  obtain ⟨Doff, Don, hOff, hOn, hModesL, hModesR, hModesCard, hCount⟩ :=
    cell_decompositions_with_potential_bound hA hFresh hFree hInsideTotal hTotalB Rprev L hL hRB pay hPhiFull
  have hModesBound : (Doff∪Don).card ≤ Ub.choose 3 :=
    hModesCard.trans (Nat.choose_le_choose 3 hSupport)
  have hPoly : 9*L*((Doff∪Don).card.choose 2)+(Doff∪Don).card.choose 3+(Doff∪Don).card.choose 4 ≤
      9*L*((Ub.choose 3).choose 2)+(Ub.choose 3).choose 3+(Ub.choose 3).choose 4 := by
    have h2 := Nat.mul_le_mul_left (9*L) (Nat.choose_le_choose 2 hModesBound)
    have h3 := Nat.choose_le_choose 3 hModesBound
    have h4 := Nat.choose_le_choose 4 hModesBound
    omega
  have hPolyR : ((9*L*((Doff∪Don).card.choose 2)+(Doff∪Don).card.choose 3+(Doff∪Don).card.choose 4:ℕ):ℝ) ≤
      ((9*L*((Ub.choose 3).choose 2)+(Ub.choose 3).choose 3+(Ub.choose 3).choose 4:ℕ):ℝ) := by exact_mod_cast hPoly
  have hChargeY : chargeQ H.G H.lab F W Y =
      (if σ then gCat C0 (catRadius β d c E d' c' E') v else -gCat C0 (catRadius β d c E d' c' E') v) := by
    rw [chargeQ_eq, ←hxsc]
    unfold clsQ
    exact (Submodule.Quotient.eq _).2 (hlatC hYL)
  have hCharge0 : chargeQ H.G H.lab F W Y0 = chargeQ H.G H.lab F W Y := by
    have hInd (T : Finset (Sym2 V)) : TypedTriangle.ind T = SparseEdge.ind T := by
      funext e
      rfl
    rw [chargeQ_eq, chargeQ_eq, ←hInd Y0, ←hInd Y]
    exact hClass
  refine ⟨A, Y0, hA, hTotalB, ?_, (fun e he => hYE e (hY0Y he)), ?_, hCharge0.trans hChargeY,
    U0, Doff, Don, hFresh, hInside, hU0Z, hSupport, hOff, hOn, hModesL, hModesR, hModesBound, ?_, ?_⟩
  · intro e he z hz hze
    rcases mem_union.mp he with he | he
    · exact disjoint_left.mp hAZ (inside_support A e he z hze) hz
    · exact hY0av e he z hz hze
  · apply (card_union_le _ _).trans
    have hAc' : A.card ≤ boundedPieceSize (α/2) h (4*U) :=
      hAc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hY0card))
    exact Nat.add_le_add hAc' hY0card
  · have hNonneg : (0:ℝ) ≤ (9*L*((Ub.choose 3).choose 2)+(Ub.choose 3).choose 3+(Ub.choose 3).choose 4:ℕ) := by positivity
    change _ ≤ pay + _
    linarith only [hPhiPay, hNonneg]
  · change _ ≤ (count Rprev:ℝ)+(pay+
      ((9*L*((Ub.choose 3).choose 2)+(Ub.choose 3).choose 3+(Ub.choose 3).choose 4:ℕ):ℝ))
    push_cast at hCount hPolyR ⊢
    linarith only [hCount, hPolyR]

#print axioms native_catalog_cell_with_potential
end TypedTriangle.Pasch
