/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanHingeSampling
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

/-- Vertex deletion pays the same absolute loss for any subfamily, including
clean hinges and families anchored at roots outside the sampled window. -/
theorem hinge_subfamily_after_vertex_deletion {V I : Type*} [Fintype V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b)
    (i : ℕ) (W Z : Finset V) (Fam : Finset (Finset (Sym2 V)))
    (hFam : Fam ⊆ SparseEdge.hinges G lab F u v a b i) :
    (((Fam.filter (fun J => freeV u v a b J ⊆ W)).card : ℝ) -
      Z.card * (2 ^ i.choose 2 * (Fintype.card V : ℝ) ^ (i-5))) ≤
        (Fam.filter (fun J => freeV u v a b J ⊆ W \ Z)).card := by
  let A := (SparseEdge.hinges G lab F u v a b i).filter
    (fun J => freeV u v a b J ⊆ W)
  let Good := (SparseEdge.hinges G lab F u v a b i).filter
    (fun J => freeV u v a b J ⊆ W \ Z)
  let C := Fam.filter (fun J => freeV u v a b J ⊆ W)
  let S := Fam.filter (fun J => freeV u v a b J ⊆ W \ Z)
  have hLoss := hinge_delete (G := G) (lab := lab) (F := F) hd i W Z
  have hGood : Good ⊆ A := by
    intro J hJ
    exact mem_filter.mpr ⟨(mem_filter.mp hJ).1,
      ((mem_filter.mp hJ).2).trans sdiff_subset⟩
  have hCover : C ⊆ S ∪ (A \ Good) := by
    intro J hJ
    obtain ⟨hJF,hJW⟩ := mem_filter.mp hJ
    by_cases hAvoid : freeV u v a b J ⊆ W \ Z
    · exact mem_union_left _ (mem_filter.mpr ⟨hJF,hAvoid⟩)
    · exact mem_union_right _ (mem_sdiff.mpr
        ⟨mem_filter.mpr ⟨hFam hJF,hJW⟩,fun hG => hAvoid (mem_filter.mp hG).2⟩)
  have hCards : (C.card : ℝ) ≤ S.card + (A \ Good).card := by
    exact_mod_cast (card_le_card hCover).trans (card_union_le _ _)
  have hDiff : ((A \ Good).card : ℝ) + Good.card = A.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hGood
  change (A.card : ℝ) - _ ≤ Good.card at hLoss
  change (C.card : ℝ) - _ ≤ S.card
  linarith

private theorem restricted_clean_hinges_card_le {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    (u v a b : Survivors Z) (i : ℕ)
    (hTa : IsAllowed H F {u.1,v.1,a.1}) (hTb : IsAllowed H F {u.1,v.1,b.1}) :
    ((hinges H F u.1 v.1 a.1 b.1 i).filter
      (fun J => Disjoint (support J) Z ∧ s(a.1,b.1) ∉ J)).card ≤
    ((SparseEdge.hinges (restrictedHost H Z).G (restrictedHost H Z).lab F
      u v a b i).filter (fun J => s(a,b) ∉ J)).card := by
  refine Finset.card_le_card_of_injOn (fun J => restrictEdgeSet Z J) ?_ ?_
  · intro J hJ
    obtain ⟨hJ,hd,hClean⟩ := mem_filter.mp hJ
    have hparts := (mem_filter.mp hJ).2
    refine mem_filter.mpr ⟨?_,?_⟩
    · change restrictEdgeSet Z J ∈ hinges (restrictedHost H Z) F u v a b i
      exact mem_filter.mpr ⟨mem_univ _,
        isHinge_restrictEdgeSet H F Z u v a b hparts.1 hd hTa hTb,
        (card_support_restrictEdgeSet Z J hd).trans hparts.2⟩
    · intro hab
      have hmap := (mem_restrictEdgeSet Z J s(a,b)).mp hab
      exact hClean (by simpa only [Sym2.map_mk] using hmap)
  · intro J hJ K hK heq
    exact restrictEdgeSet_injective_on_avoiding Z
      (mem_filter.mp hJ).2.1 (mem_filter.mp hK).2.1 heq

/-- A small preparatory vertex cut causes additive clean-hinge loss without
increasing the hinge order. -/
theorem clean_hinge_after_vertex_deletion {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α ε : ℝ) (h : ℕ) (Z : Finset V)
    (hClean : CleanHingeCond H F α h) (hNonneg : 0 ≤ α - ε)
    (hBudget : (Z.card : ℝ) * 2 ^ h.choose 2 ≤ ε * Fintype.card V) :
    CleanHingeCond (restrictedHost H Z) F (α - ε) h := by
  intro u v a b hab hTa hTb
  have hTa' : IsAllowed H F {u.1,v.1,a.1} := by
    apply (isAllowed_restricted_triple H F Z u v a).mp
    convert hTa using 1 <;> ext x <;> simp
  have hTb' : IsAllowed H F {u.1,v.1,b.1} := by
    apply (isAllowed_restricted_triple H F Z u v b).mp
    convert hTb using 1 <;> ext x <;> simp
  have ht : HingeTest H.G H.lab F u.1 v.1 a.1 b.1 :=
    ⟨fun he => hab (Subtype.ext he),hTa',hTb'⟩
  obtain ⟨i,hi6,hih,hCount⟩ := hClean u.1 v.1 a.1 b.1 ht.1 ht.2.1 ht.2.2
  let Fam := (SparseEdge.hinges H.G H.lab F u.1 v.1 a.1 b.1 i).filter
    (fun J => s(a.1,b.1) ∉ J)
  have hLoss := hinge_subfamily_after_vertex_deletion (roots_distinct ht) i univ Z Fam
    (filter_subset _ _)
  have hCleanCard : (Fam.card : ℝ) -
      Z.card * (2 ^ i.choose 2 * (Fintype.card V : ℝ) ^ (i-5)) ≤
      (Fam.filter (fun J => freeV u.1 v.1 a.1 b.1 J ⊆ univ \ Z)).card := by
    simpa only [filter_true_of_mem (fun _ _ => subset_univ _)] using hLoss
  have hSub : (Fam.filter (fun J => freeV u.1 v.1 a.1 b.1 J ⊆ univ \ Z)) ⊆
      (hinges H F u.1 v.1 a.1 b.1 i).filter
        (fun J => Disjoint (support J) Z ∧ s(a.1,b.1) ∉ J) := by
    intro J hJ
    obtain ⟨hJ,hFree⟩ := mem_filter.mp hJ
    obtain ⟨hJ,hJC⟩ := mem_filter.mp hJ
    refine mem_filter.mpr ⟨hJ,disjoint_left.mpr ?_,hJC⟩
    intro x hx hxZ
    by_cases hr : x ∈ ({u.1,v.1,a.1,b.1} : Finset V)
    · simp only [mem_insert,mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact u.2 hxZ
      · exact v.2 hxZ
      · exact a.2 hxZ
      · exact b.2 hxZ
    · exact (mem_sdiff.mp (hFree (mem_sdiff.mpr ⟨hx,hr⟩))).2 hxZ
  have hFinal := (card_le_card hSub).trans
    (restricted_clean_hinges_card_le H F Z u v a b i hTa' hTb')
  have hCoeff : (Z.card : ℝ) * 2 ^ i.choose 2 ≤ ε * Fintype.card V :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.choose_le_choose 2 hih)) (by positivity)).trans hBudget
  have hPow : (Fintype.card V : ℝ) ^ (i-4) =
      Fintype.card V * (Fintype.card V : ℝ) ^ (i-5) := by
    rw [← pow_succ']; congr 1; omega
  have hPaid : (Z.card : ℝ) * (2 ^ i.choose 2 * (Fintype.card V : ℝ) ^ (i-5)) ≤
      ε * (Fintype.card V : ℝ) ^ (i-4) := by
    have hc := mul_le_mul_of_nonneg_right hCoeff
      (show (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (i-5) by positivity)
    rw [hPow]
    convert hc using 1 <;> ring
  have hSize : (Fintype.card (Survivors Z) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun w : Survivors Z => w.1) (fun _ _ he => Subtype.ext he)
  have hNormalize := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hSize (i-4)) hNonneg
  have hFinalR := (Nat.cast_le (α := ℝ)).mpr hFinal
  change α * (Fintype.card V : ℝ) ^ (i-4) ≤ (Fam.card : ℝ) at hCount
  have hAmbient : (α - ε) * (Fintype.card V : ℝ) ^ (i-4) ≤
      ((SparseEdge.hinges (restrictedHost H Z).G (restrictedHost H Z).lab F
        u v a b i).filter (fun J => s(a,b) ∉ J)).card := calc
    (α - ε) * (Fintype.card V : ℝ) ^ (i-4) =
        α * (Fintype.card V : ℝ) ^ (i-4) -
          ε * (Fintype.card V : ℝ) ^ (i-4) := sub_mul _ _ _
    _ ≤ (Fam.card : ℝ) -
        Z.card * (2 ^ i.choose 2 * (Fintype.card V : ℝ) ^ (i-5)) :=
      sub_le_sub hCount hPaid
    _ ≤ _ := hCleanCard.trans hFinalR
  refine ⟨i,hi6,hih,?_⟩
  have hDone := hNormalize.trans hAmbient
  convert hDone using 1 <;> congr 1 <;> congr 1 <;>
    ext E <;> simp only [Finset.mem_filter]

theorem commonNbr_after_vertex_deletion_additive {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α ε : ℝ) (Z : Finset V)
    (h3 : CommonNbrCond H F α) (hNonneg : 0 ≤ α - ε)
    (hBudget : (Z.card : ℝ) ≤ ε * Fintype.card V) :
    CommonNbrCond (restrictedHost H Z) F (α - ε) := by
  intro u v huv k hk
  have hFull := h3 u.1 v.1 (fun he => huv (Subtype.ext he)) k hk
  let C := commonNbrs H k u.1 v.1
  have hCover : C ⊆ C.filter (fun w => w ∉ Z) ∪ Z := by
    intro w hw
    by_cases hz : w ∈ Z
    · exact mem_union_right _ hz
    · exact mem_union_left _ (mem_filter.mpr ⟨hw,hz⟩)
  have hCount : (C.card : ℝ) ≤
      (commonNbrs (restrictedHost H Z) k u v).card + Z.card := by
    rw [card_commonNbrs_restrictedHost]
    exact_mod_cast (card_le_card hCover).trans (card_union_le _ _)
  have hSize : (Fintype.card (Survivors Z) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun w : Survivors Z => w.1) (fun _ _ he => Subtype.ext he)
  have hNorm := mul_le_mul_of_nonneg_left hSize hNonneg
  change α * Fintype.card V ≤ (C.card : ℝ) at hFull
  change (α - ε) * Fintype.card (Survivors Z) ≤ _
  nlinarith

#print axioms hinge_subfamily_after_vertex_deletion
#print axioms clean_hinge_after_vertex_deletion
#print axioms commonNbr_after_vertex_deletion_additive
end TypedTriangle.Vortex
