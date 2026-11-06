/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CorePaidLayer
public import RequestProject.TypedTriangle.CoreEdgeGraph
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Positive simple representatives of signed physical charges. A negative
edge is replaced by two fresh wings; a positive edge by two such replacements
after its first sign flip. The lattice used for the differences is intrinsic
to the host in which all three triangles are chosen. -/
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ChargePolar
variable {V I : Type*} [Fintype V]

theorem fresh_triangle {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (h3 : CommonNbrCond H F α) {e : Sym2 V} (he : HasTri H F e)
    (U : Finset V) (B : Finset (Sym2 V)) {b : ℕ}
    (hB : ∀ v, SelSimul.edeg B v ≤ b)
    (hwin : ((U.card+2*b:ℕ):ℝ) < α*Fintype.card V) :
    ∃ a : V, IsAllowed H F (slotTri e a) ∧ a ∉ U ∧ a ∉ e ∧
      Disjoint (wedgeOf e a) B := by
  obtain ⟨u,v,t,rfl,hT⟩ := he.exists_tri
  let Bad := U ∪ nbrIn B u ∪ nbrIn B v
  have hBad : Bad.card ≤ U.card+2*b := by
    have h1 := card_union_le (U ∪ nbrIn B u) (nbrIn B v)
    have h2 := card_union_le U (nbrIn B u)
    have h3 := (card_nbrIn_le B u).trans (hB u)
    have h4 := (card_nbrIn_le B v).trans (hB v)
    dsimp [Bad]
    omega
  have hBadR : (Bad.card:ℝ) < α*Fintype.card V :=
    (show (Bad.card:ℝ) ≤ (U.card+2*b:ℕ) by exact_mod_cast hBad).trans_lt hwin
  obtain ⟨a,ha,haBad⟩ := exists_fresh_apex h3 hT Bad hBadR
  have haU : a ∉ U := fun h => haBad (mem_union_left _ (mem_union_left _ h))
  obtain ⟨huv,hua,hva⟩ := distinct_of_card_three ha.1
  refine ⟨a,by simpa only [slotTri_mk] using ha,haU,?_,?_⟩
  · simp only [Sym2.mem_iff,not_or]
    exact ⟨hua.symm,hva.symm⟩
  · apply disjoint_left.mpr
    intro f hf hfB
    obtain ⟨w,hw,rfl⟩ := mem_wedgeOf.mp hf
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact haBad (mem_union_left _ (mem_union_right _ (by simp [nbrIn,hfB])))
    · exact haBad (mem_union_right _ (by simp [nbrIn,hfB]))

lemma wedge_card_le (e : Sym2 V) (a : V) : (wedgeOf e a).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [wedgeOf_mk]
    exact (card_insert_le _ _).trans (by simp [wedge])

lemma wedge_fresh {e : Sym2 V} {a : V} {U : Finset V} (ha : a ∉ U) :
    Fresh U (wedgeOf e a) := by
  intro f hf
  obtain ⟨u,hu,rfl⟩ := mem_wedgeOf.mp hf
  exact ⟨a,by simp,ha⟩

lemma negative_relation {H : Host V I} {F : Set (Multiset I)} {e : Sym2 V} {a : V}
    (he : ¬ e.IsDiag) (ha : a ∉ e) (hT : IsAllowed H F (slotTri e a)) :
    ind (wedgeOf e a)+ind {e} ∈ lattice H F := by
  have hdis : Disjoint ({e}:Finset (Sym2 V)) (wedgeOf e a) := by
    apply disjoint_singleton_left.mpr
    exact not_mem_wedgeOf_of_not_mem ha
  have heq : ind (wedgeOf e a)+ind {e} = ind (triEdges (slotTri e a)) := by
    rw [triEdges_slotTri he ha]
    change _ = ind ({e} ∪ wedgeOf e a)
    rw [ind_union_of_disjoint hdis]
    abel
  rw [heq]
  exact isPhysical_triEdges hT

lemma wedge_hasTri {H : Host V I} {F : Set (Multiset I)} {e : Sym2 V} {a : V}
    (hT : IsAllowed H F (slotTri e a)) (he : ¬ e.IsDiag) (ha : a ∉ e) :
    ∀ f ∈ wedgeOf e a, HasTri H F f := by
  intro f hf
  refine ⟨slotTri e a,hT,?_⟩
  rw [triEdges_slotTri he ha]
  exact mem_insert_of_mem hf

/-- Each signed edge has a SIMPLE positive representative using at most
three new vertices and four edges, avoiding a protected sparse graph. -/
theorem edge_polarization {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (h3 : CommonNbrCond H F α) {e : Sym2 V} (he : HasTri H F e)
    (positive : Bool) (U : Finset V) (hEU : ∀ v ∈ e, v ∈ U)
    (B : Finset (Sym2 V)) {b : ℕ} (hB : ∀ v, SelSimul.edeg B v ≤ b)
    (hwin : ((U.card+2*b+2:ℕ):ℝ) < α*Fintype.card V) :
    ∃ (A : Finset V) (Y : Finset (Sym2 V)), A.card ≤ 3 ∧ Disjoint A U ∧
      Y.card ≤ 4 ∧ Disjoint Y B ∧ Fresh U Y ∧ Inside (U ∪ A) Y ∧
      Y ⊆ edges H ∧
      ind Y - (if positive then ind {e} else -ind {e}) ∈ lattice H F := by
  have hwin0 : ((U.card+2*b:ℕ):ℝ) < α*Fintype.card V := by
    have hle : U.card+2*b ≤ U.card+2*b+2 := by omega
    exact (show ((U.card+2*b:ℕ):ℝ) ≤ (U.card+2*b+2:ℕ) by exact_mod_cast hle).trans_lt hwin
  obtain ⟨a,hTa,haU,haE,hWaB⟩ := fresh_triangle h3 he U B hB hwin0
  have hnd : ¬ e.IsDiag := by
    obtain ⟨u,v,t,heq,hT⟩ := he.exists_tri
    rw [heq]
    have hh := (distinct_of_card_three hT.1).1
    simpa using hh
  cases positive with
  | false =>
    refine ⟨{a},wedgeOf e a,by simp,disjoint_singleton_left.mpr haU,
      (wedge_card_le e a).trans (by omega),hWaB,wedge_fresh haU,?_,?_,?_⟩
    · exact inside_wedgeOf (fun v hv => mem_union_left _ (hEU v hv)) (mem_union_right _ (mem_singleton_self _))
    · have hBas := basal_triEdges hTa
      apply (CorePaid.basal_subset_edges hBas).trans'
      rw [triEdges_slotTri hnd haE]
      exact subset_insert _ _
    · simpa only [Bool.false_eq_true,if_false,sub_neg_eq_add] using negative_relation hnd haE hTa
  | true =>
    obtain ⟨u,v,heq⟩ := Sym2.exists_mk_eq e
    subst e
    have huU := hEU u (by simp)
    have hvU := hEU v (by simp)
    have huv : u ≠ v := by simpa using hnd
    have hau : a ≠ u := by intro h; exact haU (h ▸ huU)
    have hav : a ≠ v := by intro h; exact haU (h ▸ hvU)
    have hUa : (insert a U).card ≤ U.card+1 := card_insert_le _ _
    have hwin1 : (((insert a U).card+2*b:ℕ):ℝ) < α*Fintype.card V := by
      have hc : (insert a U).card+2*b ≤ U.card+2*b+2 := by omega
      exact (show (((insert a U).card+2*b:ℕ):ℝ) ≤ (U.card+2*b+2:ℕ) by exact_mod_cast hc).trans_lt hwin
    have hUaTri : HasTri H F s(u,a) := wedge_hasTri hTa hnd haE _ (by simp [wedgeOf_mk,wedge])
    have hVaTri : HasTri H F s(v,a) := wedge_hasTri hTa hnd haE _ (by simp [wedgeOf_mk,wedge])
    obtain ⟨b0,hTb,hbUa,hbE,hWbB⟩ := fresh_triangle h3 hUaTri (insert a U) B hB hwin1
    have hUab : (insert b0 (insert a U)).card ≤ U.card+2 :=
      (card_insert_le _ _).trans (Nat.add_le_add_right hUa 1)
    have hwin2 : (((insert b0 (insert a U)).card+2*b:ℕ):ℝ) < α*Fintype.card V := by
      have hc : (insert b0 (insert a U)).card+2*b ≤ U.card+2*b+2 := by omega
      exact (show (((insert b0 (insert a U)).card+2*b:ℕ):ℝ) ≤ (U.card+2*b+2:ℕ) by exact_mod_cast hc).trans_lt hwin
    obtain ⟨c,hTc,hcUab,hcE,hWcB⟩ := fresh_triangle h3 hVaTri (insert b0 (insert a U)) B hB hwin2
    have hbU : b0 ∉ U := fun h => hbUa (mem_insert_of_mem h)
    have hcU : c ∉ U := fun h => hcUab (mem_insert_of_mem (mem_insert_of_mem h))
    have hbc : b0 ≠ c := fun h => hcUab (h ▸ mem_insert_self _ _)
    have hcua : c ∉ s(u,a) := by
      simp only [Sym2.mem_iff,not_or]
      exact ⟨fun h => hcU (h ▸ huU),fun h => hcUab (h ▸ mem_insert_of_mem (mem_insert_self _ _))⟩
    have hdis : Disjoint (wedgeOf s(u,a) b0) (wedgeOf s(v,a) c) := wedgeOf_disjoint hbc hcua
    let Y := wedgeOf s(u,a) b0 ∪ wedgeOf s(v,a) c
    let A : Finset V := {a,b0,c}
    have hAY : Disjoint A U := by
      apply disjoint_left.mpr
      intro w hw hwU
      rcases (show w=a ∨ w=b0 ∨ w=c by simpa [A] using hw) with rfl | rfl | rfl
      · exact haU hwU
      · exact hbU hwU
      · exact hcU hwU
    have hYcard : Y.card ≤ 4 := (card_union_le _ _).trans
      (by have h1 := wedge_card_le s(u,a) b0; have h2 := wedge_card_le s(v,a) c; omega)
    have hYa : ind (wedgeOf s(u,v) a) = ind {s(u,a)}+ind {s(v,a)} := by
      rw [wedgeOf_mk]
      change ind ({s(u,a)} ∪ {s(v,a)}) = _
      apply ind_union_of_disjoint
      simp [Sym2.eq_iff,huv,hau,hav]
    have hbnd : ¬ s(u,a).IsDiag := by simpa using hau.symm
    have hcnd : ¬ s(v,a).IsDiag := by simpa using hav.symm
    have hRel := Submodule.sub_mem (lattice H F)
      (Submodule.add_mem _ (negative_relation hbnd hbE hTb) (negative_relation hcnd hcE hTc))
      (negative_relation hnd haE hTa)
    refine ⟨A,Y,?_,hAY,hYcard,disjoint_union_left.mpr ⟨hWbB,hWcB⟩,
      (wedge_fresh hbU).union (wedge_fresh hcU),?_,?_,?_⟩
    · dsimp [A]
      exact (card_insert_le _ _).trans (Nat.add_le_add_right ((card_insert_le _ _).trans (by simp)) 1)
    · apply Inside.union
      · apply inside_wedgeOf
        · intro w hw
          rcases Sym2.mem_iff.mp hw with rfl | rfl
          · exact mem_union_left _ huU
          · exact mem_union_right _ (by simp [A])
        · exact mem_union_right _ (by simp [A])
      · apply inside_wedgeOf
        · intro w hw
          rcases Sym2.mem_iff.mp hw with rfl | rfl
          · exact mem_union_left _ hvU
          · exact mem_union_right _ (by simp [A])
        · exact mem_union_right _ (by simp [A])
    · apply union_subset
      · apply (CorePaid.basal_subset_edges (basal_triEdges hTb)).trans'
        rw [triEdges_slotTri hbnd hbE]
        exact subset_insert _ _
      · apply (CorePaid.basal_subset_edges (basal_triEdges hTc)).trans'
        rw [triEdges_slotTri hcnd hcE]
        exact subset_insert _ _
    · simp only [Bool.true_eq,if_true]
      have heq : ind Y-ind {s(u,v)} =
          (ind (wedgeOf s(u,a) b0)+ind {s(u,a)} +
            (ind (wedgeOf s(v,a) c)+ind {s(v,a)})) -
              (ind (wedgeOf s(u,v) a)+ind {s(u,v)}) := by
        dsimp [Y]
        rw [ind_union_of_disjoint hdis,hYa]
        abel
      rwa [heq]

end TypedTriangle.ChargePolar
