module
public import RequestProject.TypedTriangle.PaschRootedInfluence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V] [DecidableEq V]

def childExceptions (P : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  P.filter (fun T => 2 ≤ (T∩U).card)

/-- An old packing avoiding the retained reference has at most one exceptional
triangle per missing internal child edge. No protection of all child edges is
assumed. -/
theorem childExceptions_card_le_holes {H : Host V I} {F : Set (Multiset I)}
    {P : Finset (Finset V)} (hP : IsPacking H F P) (U : Finset V)
    (E0 : Finset (Sym2 V)) (hDis : Disjoint (P.biUnion triEdges) E0) :
    (childExceptions P U).card ≤ ((edges H ∩ triEdges U)\E0).card := by
  let B := childExceptions P U
  let Holes := (edges H ∩ triEdges U)\E0
  have hEdge : ∀ T ∈ B, ∃ e ∈ Holes, e ∈ triEdges T := by
    intro T hT
    obtain ⟨hTP,hTwo⟩ := mem_filter.mp hT
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0 < (T∩U).card)
    obtain ⟨b,hb,hba⟩ := exists_mem_ne (by omega : 1 < (T∩U).card) a
    have heT : s(a,b) ∈ triEdges T :=
      mem_triEdges.mpr ⟨(mem_inter.mp ha).1,(mem_inter.mp hb).1,hba.symm⟩
    have heU : s(a,b) ∈ triEdges U :=
      mem_triEdges.mpr ⟨(mem_inter.mp ha).2,(mem_inter.mp hb).2,hba.symm⟩
    have heCover : s(a,b) ∈ P.biUnion triEdges := mem_biUnion.mpr ⟨T,hTP,heT⟩
    refine ⟨s(a,b),mem_sdiff.mpr ⟨?_,?_⟩,heT⟩
    · exact mem_inter.mpr ⟨triEdges_subset_edges (hP.1 T hTP) heT,heU⟩
    · exact fun he => disjoint_left.mp hDis heCover he
  let f : ↥B → ↥Holes := fun T =>
    ⟨Classical.choose (hEdge T.val T.property),
      (Classical.choose_spec (hEdge T.val T.property)).1⟩
  have hf : Function.Injective f := by
    intro S T hEq
    apply Subtype.ext
    by_contra hne
    have hSP : S.val ∈ P := (mem_filter.mp S.property).1
    have hTP : T.val ∈ P := (mem_filter.mp T.property).1
    have heS := (Classical.choose_spec (hEdge S.val S.property)).2
    have heT := (Classical.choose_spec (hEdge T.val T.property)).2
    have heq : Classical.choose (hEdge S.val S.property) =
        Classical.choose (hEdge T.val T.property) := congrArg Subtype.val hEq
    exact disjoint_left.mp (hP.2 hSP hTP hne) heS (heq.symm ▸ heT)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hh

private theorem distinct_pair_intersections {S : Finset (Finset V)} (hS : IsPasch S)
    {Q1 Q2 T : Finset V} (hQ1 : Q1 ∈ S) (hQ2 : Q2 ∈ S) (hT : T ∈ S)
    (h12 : Q1 ≠ Q2) (hT1 : T ≠ Q1) (hT2 : T ≠ Q2)
    {a b : V} (haT : a ∈ T) (haQ : a ∈ Q1) (hbT : b ∈ T) (hbQ : b ∈ Q2) : a ≠ b := by
  intro hab
  subst b
  have haSupport : a ∈ S.biUnion id := mem_biUnion.mpr ⟨T,hT,haT⟩
  have hDegree := hS.2.2.2.1 a haSupport
  have hSub : ({Q1,Q2,T} : Finset (Finset V)) ⊆ S.filter (fun Q => a ∈ Q) := by
    intro Q hQ
    simp only [mem_insert,mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨hQ1,haQ⟩
    · exact mem_filter.mpr ⟨hQ2,hbQ⟩
    · exact mem_filter.mpr ⟨hT,haT⟩
  have hCard : ({Q1,Q2,T} : Finset (Finset V)).card = 3 := by
    simp [h12,hT1,hT2,Ne.symm hT1,Ne.symm hT2]
  have hh := card_le_card hSub
  omega

/-- With two distinct blocks wholly in the child, every other block of the
same Pasch contains two distinct child vertices. -/
theorem old_block_has_two_core_vertices_of_two_new {S : Finset (Finset V)}
    (hS : IsPasch S) (U : Finset V) {Q1 Q2 T : Finset V}
    (hQ1 : Q1 ∈ S) (hQ2 : Q2 ∈ S) (hT : T ∈ S)
    (h12 : Q1 ≠ Q2) (hT1 : T ≠ Q1) (hT2 : T ≠ Q2)
    (hU1 : Q1 ⊆ U) (hU2 : Q2 ⊆ U) : 2 ≤ (T∩U).card := by
  obtain ⟨a,ha⟩ := inter_nonempty hS hT hQ1 hT1
  obtain ⟨b,hb⟩ := inter_nonempty hS hT hQ2 hT2
  have haT := (mem_inter.mp ha).1
  have haQ := (mem_inter.mp ha).2
  have hbT := (mem_inter.mp hb).1
  have hbQ := (mem_inter.mp hb).2
  have hab := distinct_pair_intersections hS hQ1 hQ2 hT h12 hT1 hT2 haT haQ hbT hbQ
  have hSub : ({a,b} : Finset V) ⊆ T∩U := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_inter.mpr ⟨haT,hU1 haQ⟩
    · have hxb := mem_singleton.mp hx
      subst x
      exact mem_inter.mpr ⟨hbT,hU2 hbQ⟩
  have hh := card_le_card hSub
  have hCard : ({a,b} : Finset V).card = 2 := by simp [hab]
  omega

/-- This form covers both the two-new and three-new cases, without assuming
that the retained reference contains every internal child edge. -/
theorem old_block_exceptional_of_new_family {S : Finset (Finset V)} (hS : IsPasch S)
    (U : Finset V) (New : Finset (Finset V)) (hNew : New ⊆ S) (hTwo : 2 ≤ New.card)
    (hInside : ∀ Q ∈ New, Q ⊆ U) {T : Finset V} (hT : T ∈ S) (hOld : T ∉ New) :
    2 ≤ (T∩U).card := by
  obtain ⟨Q1,hQ1⟩ := card_pos.mp (by omega : 0 < New.card)
  obtain ⟨Q2,hQ2,h21⟩ := exists_mem_ne (by omega : 1 < New.card) Q1
  have hT1 : T ≠ Q1 := by intro h; exact hOld (h.symm ▸ hQ1)
  have hT2 : T ≠ Q2 := by intro h; exact hOld (h.symm ▸ hQ2)
  exact old_block_has_two_core_vertices_of_two_new hS U (hNew hQ1) (hNew hQ2) hT
    h21.symm hT1 hT2 (hInside Q1 hQ1) (hInside Q2 hQ2)

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.childExceptions_card_le_holes
#print axioms TypedTriangle.Pasch.old_block_has_two_core_vertices_of_two_new
#print axioms TypedTriangle.Pasch.old_block_exceptional_of_new_family
