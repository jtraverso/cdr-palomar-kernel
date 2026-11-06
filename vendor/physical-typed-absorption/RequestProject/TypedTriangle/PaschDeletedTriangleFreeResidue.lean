module
public import RequestProject.TypedTriangle.PaschTriangleFreeResidue
public import RequestProject.TypedTriangle.VertexDeletedQuotient
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- Peel inside the deleted host, retaining its physical lattice, while the
triangle-free conclusion and core class are expressed in the original host.
The peeled triangles are not added to any later cell mode. -/
theorem exists_deleted_core_class_triangleFree_residue
    {H : Host V I} {F : Set (Multiset I)} (Bad W : Finset V)
    (Y : Finset (Sym2 V)) (hY : IsPhysical (vertexDeleted H Bad) F Y)
    (hInside : Inside W Y) :
    ∃ (R : Finset (Sym2 V)) (D : Finset (Finset V)),
      R ⊆ Y ∧ R.card ≤ Y.card ∧
      IsDecomposition (vertexDeleted H Bad) F (Y\R) D ∧
      IsPhysical (vertexDeleted H Bad) F R ∧ HasNoAllowedTriangle H F R ∧
      S07V42.clsQ H.G H.lab F W (ind R) = S07V42.clsQ H.G H.lab F W (ind Y) := by
  obtain ⟨R, D, hRY, hCard, hD, hPhys, hFree⟩ := exists_physical_triangleFree_residue Y hY
  have hEdges : Y ⊆ edges (vertexDeleted H Bad) := by
    intro e he
    by_contra hne
    have hz := (lattice_le_localGroup (vertexDeleted H Bad) F hY).1 e hne
    have h10 : (1 : ℤ) = 0 := by simpa only [ind, if_pos he] using hz
    exact one_ne_zero h10
  have hFreeH : HasNoAllowedTriangle H F R := by
    intro T hT hTR
    apply hFree T
    · apply (isAllowed_vertexDeleted_iff H F Bad T).mpr
      refine ⟨hT, ?_⟩
      rw [disjoint_left]
      intro v hv hvBad
      obtain ⟨u, hu, huv⟩ := exists_mem_ne (by rw [hT.1]; norm_num : 1 < T.card) v
      have he := hEdges (hRY (hTR (mem_triEdges.mpr ⟨hv, hu, huv.symm⟩)))
      exact ((edges_vertexDeleted_iff H Bad s(v,u)).mp he).2 v hvBad (by simp)
    · exact hTR
  have hDcore : IsDecomposition (⟨S07V42.indG H.G W, H.lab⟩ : Host V I) F (Y\R) D := by
    refine ⟨?_, hD.2.1, hD.2.2⟩
    intro T hT
    have hAllow := isAllowed_mono (vertexDeleted_le H Bad) rfl (hD.1 T hT)
    refine ⟨hAllow.1, ?_, hAllow.2.2⟩
    intro x hx y hy hxy
    have he : s(x,y) ∈ Y := (mem_sdiff.mp
      (hD.subset hT (mem_triEdges.mpr ⟨hx, hy, hxy⟩))).1
    exact ⟨hAllow.2.1 x hx y hy hxy,
      hInside _ he x (by simp), hInside _ he y (by simp)⟩
  have hL : ind (Y\R) ∈ S07V42.LamCore H.G H.lab F W := by
    change IsPhysical (⟨S07V42.indG H.G W, H.lab⟩ : Host V I) F (Y\R)
    exact isPhysical_of_isDecomposition hDcore
  have hDiff : ind Y - ind R ∈ S07V42.LamCore H.G H.lab F W := by
    simpa only [ind_sdiff_of_subset hRY] using hL
  refine ⟨R, D, hRY, hCard, hD, hPhys, hFreeH, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  have hNeg := (S07V42.LamCore H.G H.lab F W).neg_mem hDiff
  simpa only [neg_sub] using hNeg

#print axioms exists_deleted_core_class_triangleFree_residue
end TypedTriangle.Pasch
