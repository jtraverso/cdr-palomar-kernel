/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BoundedPieceAbsorber
public import RequestProject.TypedTriangle.RestrictedHingeGeometry
public import RequestProject.TypedTriangle.RestrictedVertexBounds
public import RequestProject.S07V42.Polarize
public import RequestProject.S07V42.Catalog
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open SparseEdge Dispersal S07V42

/-- Native single-cell supply. In contrast to the remote intermediate theorem,
the only absorption input is the proved G2 constructor for this particular
physical piece in the true deleted host. No TerminalSupply premise remains. -/
theorem native_catalog_cell (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (d c E d' c' E' : ℕ) :
    ∃ Ecell : ℕ, ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        coreN0 β h ≤ W.card → n₀ ≤ W.card →
        ∀ C0 : CoreCompression H.G H.lab F W d c E,
        ∀ Z : Finset V, (Z.card:ℝ) ≤ δ*W.card →
        DelCompression H.G H.lab F Z d' c' E' →
        ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, degIn B v ≤ b) →
          (b:ℝ) ≤ ε*W.card →
        ∀ v : Cat d (catR β d c E d' c' E'),
          gCat C0 (catR β d c E d' c' E') v ∈ KZ H.G H.lab F W Z → ∀ σ : Bool,
        ∃ A Y : Finset (Sym2 V), IsAbsorber H F A Y ∧ Disjoint (A∪Y) B ∧
          (∀ e ∈ A∪Y, ∀ z ∈ Z, z ∉ e) ∧
          (∀ e ∈ Y, e ∈ SparseEdge.edges (indG H.G (W\Z))) ∧
          (A∪Y).card ≤ Ecell ∧
          chargeQ H.G H.lab F W Y =
            (if σ then gCat C0 (catR β d c E d' c' E') v
              else -gCat C0 (catR β d c E d' c' E') v) := by
  obtain ⟨U,hU⟩ := native_reroute h hβ d c E d' c' E'
  obtain ⟨εA,hεA,EA,nA,hAbs⟩ := bounded_piece_absorber_deleted (α/2) h (4*U) (by positivity)
  obtain ⟨δ₀,hδ₀,hδhalf,hWin⟩ := original_geometry_vertex_budget hα h
  refine ⟨EA+4*U,min (β/8) (εA/2),min δ₀ (coreDelta β h),
    lt_min (by positivity) (by positivity),lt_min hδ₀ (by unfold coreDelta; positivity),
    2*nA+⌈40*(U:ℝ)/β⌉₊+1,?_⟩
  intro V I _ H F W h3 h4 hc3 hc4 hnC hn C0 Z hZ CZ B b hB hb v hv σ
  have hWn : (W.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ W
  have hW0 : (0:ℝ) ≤ W.card := by positivity
  have hZ₀ : (Z.card:ℝ) ≤ δ₀*Fintype.card V :=
    (hZ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW0)).trans
      (mul_le_mul_of_nonneg_left hWn hδ₀.le)
  have hZcore : (Z.card:ℝ) ≤ coreDelta β h*W.card :=
    hZ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW0)
  obtain ⟨x,hxM,hxL,hxU,hxc⟩ := hU hc3 hc4 hnC C0 hZcore CZ v hv
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
      (if σ then gCat C0 (catR β d c E d' c' E') v else -gCat C0 (catR β d c E d' c' E') v) := by
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
  obtain ⟨A,hA,hAB,hAc,hAZ⟩ := hAbs H F Z hNA hg3 hg4 Y hYphys hYc
    (fun e he z hz => fun h => hYav e he z h hz) B b hB hbA
  refine ⟨A,Y,hA,disjoint_union_left.mpr ⟨hAB,hYB⟩,?_,hYE,
    (card_union_le _ _).trans (Nat.add_le_add hAc hYc),?_⟩
  · intro e he z hz hze
    rcases mem_union.mp he with he | he
    · exact hAZ e he z hze hz
    · exact hYav e he z hz hze
  · rw [chargeQ_eq,←hxsc]
    unfold clsQ
    exact (Submodule.Quotient.eq _).2 (hlatC hYL)
end TypedTriangle.CatalogNative
