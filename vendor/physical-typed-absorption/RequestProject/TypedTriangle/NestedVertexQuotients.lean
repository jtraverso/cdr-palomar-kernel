/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RestrictedVertexBounds

@[expose] public section

/-! Concrete quotient maps for nested deletions. -/

open Finset
noncomputable section
open Classical

namespace TypedTriangle
variable {V I : Type*} [Fintype V]

lemma quotMap_surjective_congr_source {H K L : Host V I} {F : Set (Multiset I)}
    (heq : H = K) (hG : H.G ≤ L.G) (hl : H.lab = L.lab)
    (hG' : K.G ≤ L.G) (hl' : K.lab = L.lab) :
    Function.Surjective (quotMap (F := F) hG hl) ↔
      Function.Surjective (quotMap (F := F) hG' hl') := by
  subst K
  rfl

lemma vertexDeleted_antitone (H : Host V I) {A B : Finset V} (hAB : A ⊆ B) :
    (vertexDeleted H B).G ≤ (vertexDeleted H A).G := by
  intro u v huv
  exact ⟨huv.1,fun hu => huv.2.1 (hAB hu),fun hv => huv.2.2 (hAB hv)⟩

lemma vertexDeleted_mono {H K : Host V I} (hG : H.G ≤ K.G) (A : Finset V) :
    (vertexDeleted H A).G ≤ (vertexDeleted K A).G := by
  intro u v huv
  exact ⟨hG huv.1,huv.2⟩

lemma restrictedHost_mono {H K : Host V I} (hG : H.G ≤ K.G) (A : Finset V) :
    (restrictedHost H A).G ≤ (restrictedHost K A).G := by
  intro u v huv
  exact hG huv

lemma restrictedHost_labels {H K : Host V I} (hl : H.lab = K.lab) (A : Finset V) :
    (restrictedHost H A).lab = (restrictedHost K A).lab := by
  funext v
  exact congrFun hl v.1

lemma vertexDeleted_vertexDeleted (H : Host V I) (A B : Finset V) :
    vertexDeleted (vertexDeleted H B) A = vertexDeleted H (A ∪ B) := by
  have hG : (vertexDeleted (vertexDeleted H B) A).G = (vertexDeleted H (A ∪ B)).G := by
    ext u v
    change ((H.G.Adj u v ∧ u ∉ B ∧ v ∉ B) ∧ u ∉ A ∧ v ∉ A) ↔
      (H.G.Adj u v ∧ u ∉ A ∪ B ∧ v ∉ A ∪ B)
    simp only [Finset.mem_union,not_or]
    tauto
  exact congrArg (fun G => (⟨G,H.lab⟩ : Host V I)) hG

lemma restrictedHost_vertexDeleted (H : Host V I) (A B : Finset V) :
    restrictedHost (vertexDeleted H B) A =
      vertexDeleted (restrictedHost H A) (B.subtype (fun v => v ∉ A)) := by
  have hG : (restrictedHost (vertexDeleted H B) A).G =
      (vertexDeleted (restrictedHost H A) (B.subtype (fun v => v ∉ A))).G := by
    ext u v
    change (H.G.Adj u.1 v.1 ∧ u.1 ∉ B ∧ v.1 ∉ B) ↔
      (H.G.Adj u.1 v.1 ∧ u ∉ B.subtype (fun v => v ∉ A) ∧ v ∉ B.subtype (fun v => v ∉ A))
    simp only [Finset.mem_subtype]
  exact congrArg (fun G => (⟨G,fun v => H.lab v.1⟩ : Host (Survivors A) I)) hG

/-- Both paths in the square send an integer representative to its zero extension. -/
lemma quotMap_surviving_naturality {H K : Host V I} (F : Set (Multiset I))
    (hG : H.G ≤ K.G) (hl : H.lab = K.lab) (A : Finset V)
    (q : physQuot (restrictedHost H A) F) :
    quotMap (F := F) (vertexDeleted_mono hG A) hl (survivingPhysQuotEquiv H F A q) =
      survivingPhysQuotEquiv K F A
        (quotMap (F := F) (restrictedHost_mono hG A) (restrictedHost_labels hl A) q) := by
  induction q using Submodule.Quotient.induction_on with
  | H x => rfl

/-- Transfer surjectivity through the explicit natural square. -/
theorem quotMap_deleted_surjective_of_restricted {H K : Host V I}
    (F : Set (Multiset I)) (hG : H.G ≤ K.G) (hl : H.lab = K.lab) (A : Finset V)
    (hs : Function.Surjective
      (quotMap (F := F) (restrictedHost_mono hG A) (restrictedHost_labels hl A))) :
    Function.Surjective (quotMap (F := F) (vertexDeleted_mono hG A) hl) := by
  intro y
  obtain ⟨x,hx⟩ := hs ((survivingPhysQuotEquiv K F A).symm y)
  refine ⟨survivingPhysQuotEquiv H F A x,?_⟩
  rw [quotMap_surviving_naturality F hG hl A x,hx]
  exact (survivingPhysQuotEquiv K F A).apply_symm_apply y

def nestedVertexQuotMap (H : Host V I) (F : Set (Multiset I)) (A B : Finset V) :
    physQuot (vertexDeleted H (A ∪ B)) F →ₗ[ℤ] physQuot (vertexDeleted H A) F :=
  quotMap (vertexDeleted_antitone H Finset.subset_union_left) rfl

/-- The actual quotient map after A and then B is onto, using geometry on V\A. -/
theorem nestedVertexQuotMap_surjective {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (A B : Finset V)
    (hA3 : (A.card : ℝ) ≤ α * Fintype.card V / 2)
    (hA4 : (A.card : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ α/2 * Fintype.card V)
    (hB1 : (B.card : ℝ)+2 < (α/2)*Fintype.card (Survivors A))
    (hB2 : ((B.card : ℝ)+h)*2 ^ Nat.choose h 2 ≤ α/4*Fintype.card (Survivors A)) :
    Function.Surjective (nestedVertexQuotMap H F A B) := by
  have hg := original_geometry_restrictedHost hα.le hH3 hH4 A hA3 hA4
  have hBA : (B.subtype (fun v => v ∉ A)).card ≤ B.card := by
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hBAR : ((B.subtype (fun v => v ∉ A)).card : ℝ) ≤ B.card := by exact_mod_cast hBA
  have hw1 : ((B.subtype (fun v => v ∉ A)).card : ℝ)+2 <
      (α/2)*Fintype.card (Survivors A) := by linarith
  have hw2 : (((B.subtype (fun v => v ∉ A)).card : ℝ)+h)*2 ^ Nat.choose h 2 ≤
      (α/2)/2*Fintype.card (Survivors A) := by
    have hp : (0 : ℝ) ≤ 2 ^ Nat.choose h 2 := by positivity
    have := mul_le_mul_of_nonneg_right (add_le_add_right hBAR h) hp
    nlinarith
  have hs := quotMap_vertexDeleted_surjective (by positivity : 0 < α/2)
    hg.1 hg.2 (B.subtype (fun v => v ∉ A)) hw1 hw2
  have hin : Function.Surjective
      (quotMap (F := F) (restrictedHost_mono (vertexDeleted_le H B) A)
        (restrictedHost_labels rfl A)) := by
    exact (quotMap_surjective_congr_source
      (restrictedHost_vertexDeleted H A B).symm _ _ _ _).1 hs
  have hout := quotMap_deleted_surjective_of_restricted F (vertexDeleted_le H B) rfl A hin
  exact (quotMap_surjective_congr_source
    (vertexDeleted_vertexDeleted H A B) _ _ _ _).1 hout

/-- Zero-supported local demands remain local after the second vertex deletion. -/
theorem localGroup_nested_of_vanish {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (A B : Finset V)
    (hA3 : (A.card : ℝ) ≤ α*Fintype.card V/2)
    (hA4 : (A.card : ℝ)*2 ^ Nat.choose (h+1) 2 ≤ α/2*Fintype.card V)
    (hB1 : (B.card : ℝ)+2 < α/2*Fintype.card (Survivors A))
    (hB2 : ((B.card : ℝ)+h)*2 ^ Nat.choose h 2 ≤ α/4*Fintype.card (Survivors A))
    {x : Sym2 V → ℤ} (hx : x ∈ localGroup (vertexDeleted H A) F)
    (hz : ∀ e, TouchZ B e → x e=0) :
    x ∈ localGroup (vertexDeleted H (A ∪ B)) F := by
  have hg := original_geometry_restrictedHost hα.le hH3 hH4 A hA3 hA4
  let D := B.subtype (fun v => v ∉ A)
  have hDc : D.card ≤ B.card := by
    dsimp [D]; rw [Finset.card_subtype]; exact Finset.card_filter_le _ _
  have hDcR : (D.card : ℝ) ≤ B.card := by exact_mod_cast hDc
  have hw1 : (D.card : ℝ)+2 < α/2*Fintype.card (Survivors A) := by linarith
  have hw2 : ((D.card : ℝ)+h)*2 ^ Nat.choose h 2 ≤ (α/2)/2*Fintype.card (Survivors A) := by
    have := mul_le_mul_of_nonneg_right (add_le_add_right hDcR h)
      (show (0 : ℝ) ≤ 2 ^ Nat.choose h 2 by positivity)
    nlinarith
  have hxU := edgeRestrict_mem_localGroup H F A hx
  have hzU : ∀ e, TouchZ D e → edgeRestrict A x e=0 := by
    intro e he
    obtain ⟨v,hvD,hve⟩ := he
    exact hz (Sym2.map Subtype.val e) ⟨v.1,Finset.mem_subtype.1 hvD,
      Sym2.mem_map.2 ⟨v,hve,rfl⟩⟩
  have hxD : edgeRestrict A x ∈ localGroup (vertexDeleted (restrictedHost H A) D) F :=
    (mem_localGroup_vertexDeleted_iff (by positivity : 0 < α/2) hg.1 hg.2 D hw1 hw2 _).2 ⟨hxU,hzU⟩
  have hxS : edgeRestrict A x ∈ localGroup (restrictedHost (vertexDeleted H B) A) F := by
    simpa only [restrictedHost_vertexDeleted] using hxD
  have hext := edgeZeroExtend_mem_localGroup (vertexDeleted H B) F A hxS
  rw [edgeZeroExtend_restrict A x (localGroup_vertexDeleted_vanish H F A hx)] at hext
  simpa only [vertexDeleted_vertexDeleted] using hext

end TypedTriangle

#print axioms TypedTriangle.nestedVertexQuotMap_surjective
#print axioms TypedTriangle.localGroup_nested_of_vanish
