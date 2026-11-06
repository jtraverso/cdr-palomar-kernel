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

/-! Clean witnesses anchored in the final window give geometry in every
intermediate induced host containing that window. -/

open Finset Classical S07V24
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex
open CorePaid

theorem anchored_clean_intermediate_geometry {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) {α q η : ℝ} {h : ℕ}
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hη1 : η < 1) (hh : 1 ≤ h)
    (hClean : CleanHingeCond H F α h) (W U : Finset V) (hWU : W ⊆ U)
    (hpool : ∀ u v, u ≠ v → ∀ k, ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      (1 - η) * α * q * Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card)
    (hhinge : ∀ u v a b, HingeTest H.G H.lab F u v a b →
      (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
        (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) ≤
          (((SparseEdge.hinges H.G H.lab F u v a b
            (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
              (fun J => freeV u v a b J ⊆ W)).card) :
    CommonNbrCond (restrictedHost H (univ \ U)) F ((1 - η) * α * q ^ h) ∧
    CleanHingeCond (restrictedHost H (univ \ U)) F ((1 - η) * α * q ^ h) h := by
  have hUcard : (U.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast card_le_card (subset_univ U)
  have hc : 0 ≤ (1 - η) * α := by positivity
  constructor
  · intro u v huv k hk
    have heq : ((commonNbrs H k u.1 v.1).filter (fun w => w ∉ univ \ U)) =
        commonNbrs H k u.1 v.1 ∩ U := by ext w; simp
    rw [card_commonNbrs_restrictedHost, heq, card_survivors_compl]
    have hqpow : q ^ h ≤ q := by
      simpa only [pow_one] using (pow_le_pow_of_le_one hq.le hq1 hh)
    have hcount : ((commonNbrs H k u.1 v.1) ∩ W).card ≤
        ((commonNbrs H k u.1 v.1) ∩ U).card := by
      apply card_le_card
      intro x hx
      exact mem_inter.mpr ⟨(mem_inter.mp hx).1, hWU (mem_inter.mp hx).2⟩
    calc
      (1 - η) * α * q ^ h * (U.card : ℝ) ≤
          (1 - η) * α * q * Fintype.card V := by gcongr
      _ ≤ ((commonNbrs H k u.1 v.1) ∩ W).card :=
        hpool u.1 v.1 (fun he => huv (Subtype.ext he)) k hk
      _ ≤ ((commonNbrs H k u.1 v.1) ∩ U).card := by exact_mod_cast hcount
  · intro u v a b hab hTa hTb
    have hTa' : IsAllowed H F {u.1, v.1, a.1} := by
      apply (isAllowed_restricted_triple H F (univ \ U) u v a).mp
      convert hTa using 1 <;> ext x <;> simp
    have hTb' : IsAllowed H F {u.1, v.1, b.1} := by
      apply (isAllowed_restricted_triple H F (univ \ U) u v b).mp
      convert hTb using 1 <;> ext x <;> simp
    have ht : HingeTest H.G H.lab F u.1 v.1 a.1 b.1 :=
      ⟨fun he => hab (Subtype.ext he), hTa', hTb'⟩
    have hs := cleanHingeOrder_spec hClean ht
    let i := cleanHingeOrder hClean u.1 v.1 a.1 b.1
    let Src := ((SparseEdge.hinges H.G H.lab F u.1 v.1 a.1 b.1 i).filter
      (fun J => s(a.1, b.1) ∉ J)).filter (fun J => freeV u.1 v.1 a.1 b.1 J ⊆ W)
    have hroot : ({u.1, v.1, a.1, b.1} : Finset V) ⊆ U := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simpa only [mem_sdiff, mem_univ, true_and, not_not] using u.2
      · simpa only [mem_sdiff, mem_univ, true_and, not_not] using v.2
      · simpa only [mem_sdiff, mem_univ, true_and, not_not] using a.2
      · simpa only [mem_sdiff, mem_univ, true_and, not_not] using b.2
    have hAvoid : ∀ J ∈ Src, Disjoint (support J) (univ \ U) := by
      intro J hJ
      obtain ⟨_, hFree⟩ := mem_filter.mp hJ
      apply disjoint_left.mpr
      intro x hx hxOut
      have hxU : x ∈ U := by
        by_cases hr : x ∈ ({u.1, v.1, a.1, b.1} : Finset V)
        · exact hroot hr
        · exact hWU (hFree (mem_sdiff.mpr ⟨hx, hr⟩))
      exact (mem_sdiff.mp hxOut).2 hxU
    have hCount : Src.card ≤
        ((SparseEdge.hinges (restrictedHost H (univ \ U)).G
          (restrictedHost H (univ \ U)).lab F u v a b i).filter
            (fun J => s(a, b) ∉ J)).card := by
      refine card_le_card_of_injOn (fun J => restrictEdgeSet (univ \ U) J) ?_ ?_
      · intro J hJ
        have hd := hAvoid J hJ
        obtain ⟨hJ', _⟩ := mem_filter.mp hJ
        obtain ⟨hJ', hCleanJ⟩ := mem_filter.mp hJ'
        have hparts := (mem_filter.mp hJ').2
        refine mem_filter.mpr ⟨?_, ?_⟩
        · change restrictEdgeSet (univ \ U) J ∈ hinges
            (restrictedHost H (univ \ U)) F u v a b i
          exact mem_filter.mpr ⟨mem_univ _,
            isHinge_restrictEdgeSet H F (univ \ U) u v a b hparts.1 hd hTa' hTb',
            (card_support_restrictEdgeSet (univ \ U) J hd).trans hparts.2⟩
        · intro he
          have hmap := (mem_restrictEdgeSet (univ \ U) J s(a, b)).mp he
          exact hCleanJ (by simpa only [Sym2.map_mk] using hmap)
      · intro J hJ K hK heq
        exact restrictEdgeSet_injective_on_avoiding (univ \ U)
          (hAvoid J hJ) (hAvoid K hK) heq
    refine ⟨i, hs.1, hs.2.1, ?_⟩
    rw [card_survivors_compl]
    have hd : i - 4 ≤ h := by have := hs.2.1; omega
    have hqpow : q ^ h ≤ q ^ (i - 4) := pow_le_pow_of_le_one hq.le hq1 hd
    calc
      (1 - η) * α * q ^ h * (U.card : ℝ) ^ (i - 4) ≤
          (1 - η) * α * q ^ (i - 4) * (Fintype.card V : ℝ) ^ (i - 4) := by gcongr
      _ ≤ (Src.card : ℝ) := hhinge u.1 v.1 a.1 b.1 ht
      _ ≤ _ := by
        have hCountR := (Nat.cast_le (α := ℝ)).mpr hCount
        convert hCountR using 1 <;> congr 1 <;> congr 1 <;>
          ext J <;> simp only [Finset.mem_filter]

#print axioms anchored_clean_intermediate_geometry

end TypedTriangle.Vortex
