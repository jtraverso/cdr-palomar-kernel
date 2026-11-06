module
public import RequestProject.TypedTriangle.Packing
public import RequestProject.TypedTriangle.SlotPairing
public import RequestProject.TypedTriangle.Absorb
public import RequestProject.S07V42.Setting
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

def HasNoAllowedTriangle (H : Host V I) (F : Set (Multiset I)) (R : Finset (Sym2 V)) : Prop :=
  ∀ T : Finset V, IsAllowed H F T → ¬triEdges T ⊆ R

/-- Greedy triangle peeling terminates by the strict decrease of the edge count.
The returned packing is maximal by inclusion in the original edge set. -/
theorem exists_triangleFree_residue (H : Host V I) (F : Set (Multiset I))
    (Y : Finset (Sym2 V)) :
    ∃ (R : Finset (Sym2 V)) (Q : Finset (Finset V)),
      R ⊆ Y ∧ IsDecomposition H F (Y\R) Q ∧ HasNoAllowedTriangle H F R := by
  suffices h : ∀ n : ℕ, ∀ Y : Finset (Sym2 V), Y.card = n →
      ∃ (R : Finset (Sym2 V)) (Q : Finset (Finset V)),
        R ⊆ Y ∧ IsDecomposition H F (Y\R) Q ∧ HasNoAllowedTriangle H F R from h Y.card Y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y hYn
    by_cases hFree : HasNoAllowedTriangle H F Y
    · refine ⟨Y,∅,subset_rfl,?_,hFree⟩
      exact ⟨by simp,by simp,by simp⟩
    · obtain ⟨T,hT,hTY⟩ : ∃ T : Finset V, IsAllowed H F T ∧ triEdges T ⊆ Y := by
        by_contra hNo
        exact hFree (fun T hT hTY => hNo ⟨T,hT,hTY⟩)
      have hLess : (Y\triEdges T).card < n := by
        have he := card_sdiff_add_card_eq_card hTY
        rw [card_triEdges_three hT.1] at he
        omega
      obtain ⟨R,Q,hRY,hD,hFreeR⟩ := ih (Y\triEdges T).card hLess (Y\triEdges T) rfl
      have hTri : IsDecomposition H F (triEdges T) {T} := by
        refine ⟨?_,?_,?_⟩
        · intro S hS
          obtain rfl := mem_singleton.mp hS
          exact hT
        · simp
        · simp
      have hDis : Disjoint (triEdges T) ((Y\triEdges T)\R) :=
        (sdiff_disjoint : Disjoint (Y\triEdges T) (triEdges T)).symm.mono_right sdiff_subset
      have hEq : triEdges T ∪ ((Y\triEdges T)\R) = Y\R := by
        ext e
        simp only [mem_union,mem_sdiff]
        constructor
        · rintro (he | ⟨⟨heY,heT⟩,heR⟩)
          · exact ⟨hTY he,fun heR => (mem_sdiff.mp (hRY heR)).2 he⟩
          · exact ⟨heY,heR⟩
        · intro he
          by_cases heT : e ∈ triEdges T
          · exact Or.inl heT
          · exact Or.inr ⟨⟨he.1,heT⟩,he.2⟩
      refine ⟨R,{T}∪Q,hRY.trans sdiff_subset,?_,hFreeR⟩
      simpa only [hEq] using hTri.union hD hDis

theorem exists_physical_triangleFree_residue {H : Host V I} {F : Set (Multiset I)}
    (Y : Finset (Sym2 V)) (hY : IsPhysical H F Y) :
    ∃ (R : Finset (Sym2 V)) (Q : Finset (Finset V)),
      R ⊆ Y ∧ R.card ≤ Y.card ∧ IsDecomposition H F (Y\R) Q ∧
        IsPhysical H F R ∧ HasNoAllowedTriangle H F R := by
  obtain ⟨R,Q,hRY,hD,hFree⟩ := exists_triangleFree_residue H F Y
  have hEq : Y\(Y\R) = R := by
    ext e
    simp only [mem_sdiff]
    constructor
    · intro he
      by_contra hR
      exact he.2 ⟨he.1,hR⟩
    · intro heR
      exact ⟨hRY heR,fun he => he.2 heR⟩
  have hp := isPhysical_sdiff_of_decomposition hY hD (sdiff_subset : Y\R ⊆ Y)
  refine ⟨R,Q,hRY,card_le_card hRY,hD,?_,hFree⟩
  simpa only [hEq] using hp

theorem allowed_triangle_meets_outside_of_fresh {H : Host V I} {F : Set (Multiset I)}
    {A P : Finset (Sym2 V)} {U T : Finset V}
    (hFresh : Fresh U A) (hFree : HasNoAllowedTriangle H F P)
    (hT : IsAllowed H F T) (hSub : triEdges T ⊆ A∪P) :
    ∃ v ∈ T, v ∉ U := by
  by_contra hNot
  have hTU : ∀ v ∈ T, v ∈ U := by simpa only [not_exists, not_and, not_not] using hNot
  apply hFree T hT
  intro e he
  rcases mem_union.mp (hSub he) with hA | hP
  · obtain ⟨v,hve,hvU⟩ := hFresh e hA
    exact (hvU (hTU v (mem_of_mem_triEdges he hve))).elim
  · exact hP

theorem decomposition_blocks_meet_outside_of_fresh {H : Host V I} {F : Set (Multiset I)}
    {A P : Finset (Sym2 V)} {U : Finset V} {D : Finset (Finset V)}
    (hFresh : Fresh U A) (hFree : HasNoAllowedTriangle H F P)
    (hD : IsDecomposition H F (A∪P) D) :
    ∀ T ∈ D, ∃ v ∈ T, v ∉ U :=
  fun T hT => allowed_triangle_meets_outside_of_fresh hFresh hFree (hD.1 T hT) (hD.subset hT)

theorem absorber_modes_meet_outside_of_fresh {H : Host V I} {F : Set (Multiset I)}
    {A P : Finset (Sym2 V)} {U : Finset V}
    (hA : IsAbsorber H F A P) (hFresh : Fresh U A) (hFree : HasNoAllowedTriangle H F P) :
    ∃ D0 D1 : Finset (Finset V), IsDecomposition H F A D0 ∧
      IsDecomposition H F (A∪P) D1 ∧ (∀ T ∈ D0, ∃ v ∈ T, v ∉ U) ∧
        (∀ T ∈ D1, ∃ v ∈ T, v ∉ U) := by
  obtain ⟨_,⟨D0,hD0⟩,⟨D1,hD1⟩⟩ := hA
  refine ⟨D0,D1,hD0,hD1,?_,decomposition_blocks_meet_outside_of_fresh hFresh hFree hD1⟩
  intro T hT
  exact allowed_triangle_meets_outside_of_fresh hFresh hFree (hD0.1 T hT)
    ((hD0.subset hT).trans subset_union_left)

/-- If the peeled graph lies in the core, every removed triangle contributes
zero to the core quotient. The physical residue therefore has the same class. -/
theorem exists_core_class_triangleFree_residue {H : Host V I} {F : Set (Multiset I)}
    (W : Finset V) (Y : Finset (Sym2 V)) (hY : IsPhysical H F Y)
    (hInside : ∀ e ∈ Y, ∀ v ∈ e, v ∈ W) :
    ∃ (R : Finset (Sym2 V)) (Q : Finset (Finset V)),
      R ⊆ Y ∧ R.card ≤ Y.card ∧ IsDecomposition H F (Y\R) Q ∧ IsPhysical H F R ∧
        HasNoAllowedTriangle H F R ∧
          S07V42.clsQ H.G H.lab F W (ind R) = S07V42.clsQ H.G H.lab F W (ind Y) := by
  obtain ⟨R,Q,hRY,hCard,hD,hPhys,hFree⟩ := exists_physical_triangleFree_residue Y hY
  have hDcore : IsDecomposition (⟨S07V42.indG H.G W,H.lab⟩ : Host V I) F (Y\R) Q := by
    refine ⟨?_,hD.2.1,hD.2.2⟩
    intro T hT
    have hAllow := hD.1 T hT
    refine ⟨hAllow.1,?_,hAllow.2.2⟩
    intro x hx y hy hxy
    have he : s(x,y) ∈ Y := (mem_sdiff.mp (hD.subset hT (mem_triEdges.mpr ⟨hx,hy,hxy⟩))).1
    exact ⟨hAllow.2.1 x hx y hy hxy,
      hInside _ he x (by simp),hInside _ he y (by simp)⟩
  have hL : ind (Y\R) ∈ S07V42.LamCore H.G H.lab F W := by
    change IsPhysical (⟨S07V42.indG H.G W,H.lab⟩ : Host V I) F (Y\R)
    exact isPhysical_of_isDecomposition hDcore
  have hDiff : ind Y-ind R ∈ S07V42.LamCore H.G H.lab F W := by
    simpa only [ind_sdiff_of_subset hRY] using hL
  refine ⟨R,Q,hRY,hCard,hD,hPhys,hFree,?_⟩
  apply (Submodule.Quotient.eq _).mpr
  have hNeg := (S07V42.LamCore H.G H.lab F W).neg_mem hDiff
  simpa only [neg_sub] using hNeg

#print axioms exists_triangleFree_residue
#print axioms exists_physical_triangleFree_residue
#print axioms allowed_triangle_meets_outside_of_fresh
#print axioms absorber_modes_meet_outside_of_fresh
#print axioms exists_core_class_triangleFree_residue
end TypedTriangle.Pasch
