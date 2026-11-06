/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanHinge
public import RequestProject.TypedTriangle.VortexCleanHingeDeletion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

theorem CleanHingeCond.mono {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)} {α β : ℝ} {h : ℕ}
    (hClean : CleanHingeCond H F α h) (hβα : β ≤ α) :
    CleanHingeCond H F β h := by
  intro u v a b hab hTa hTb
  obtain ⟨i, hi6, hih, hCount⟩ := hClean u v a b hab hTa hTb
  exact ⟨i, hi6, hih,
    (mul_le_mul_of_nonneg_right hβα (by positivity)).trans hCount⟩

/-- Common-neighbour loss is additive in the local paid degree. -/
theorem commonNbr_after_sparse_payment_additive {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α ε : ℝ)
    (C : Finset (Sym2 V)) (d : ℕ) (h3 : CommonNbrCond H F α)
    (hDeg : ∀ x, SparseEdge.degIn C x ≤ d)
    (hBudget : 2 * (d : ℝ) ≤ ε * Fintype.card V) :
    CommonNbrCond (subHost H (edges H \ C)) F (α - ε) := by
  intro u v huv k htype
  have hfull := h3 u v huv k htype
  let bad := SparseEdge.nbrIn C u ∪ SparseEdge.nbrIn C v
  have hbad : bad.card ≤ 2*d :=
    (card_union_le _ _).trans (by
      have hu := (SparseEdge.card_nbrIn_le C u).trans (hDeg u)
      have hv := (SparseEdge.card_nbrIn_le C v).trans (hDeg v)
      omega)
  have hcover : commonNbrs H k u v ⊆
      commonNbrs (subHost H (edges H \ C)) k u v ∪ bad := by
    intro w hw
    by_cases hu : s(u,w) ∈ C
    · exact mem_union_right _ (mem_union_left _ (by simp [SparseEdge.nbrIn,hu]))
    by_cases hv : s(v,w) ∈ C
    · exact mem_union_right _ (mem_union_right _ (by simp [SparseEdge.nbrIn,hv]))
    · exact mem_union_left _ (by
        rw [Residual.commonNbrs_sdiff]
        exact mem_filter.mpr ⟨hw,hu,hv⟩)
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  have hcR : ((commonNbrs H k u v).card : ℝ) ≤
      (commonNbrs (subHost H (edges H \ C)) k u v).card + bad.card := by
    exact_mod_cast hc
  have hbR : (bad.card : ℝ) ≤ 2*d := by exact_mod_cast hbad
  change (α - ε) * Fintype.card V ≤ _
  nlinarith

/-- Sparse payments cause an additive loss in clean hinge density. The
order is the same before and after the payment, so it can remain fixed in
a variable-depth construction. -/
theorem clean_hinge_after_sparse_payment {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α ε : ℝ) (h : ℕ)
    (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ)
    (hClean : CleanHingeCond H F α h)
    (hDeg : ∀ x, B.degree x ≤ d)
    (hBudget : 5 * (d : ℝ) * 2 ^ (h.choose 2) ≤ ε * Fintype.card V) :
    CleanHingeCond (⟨H.G \ B, H.lab⟩ : Host V I) F (α - ε) h := by
  intro u v a b hab hTa hTb
  have hTaG : IsAllowed H F {u,v,a} :=
    ⟨hTa.1, fun x hx y hy hxy =>
      ((SimpleGraph.sdiff_adj _ _ _ _).mp (hTa.2.1 x hx y hy hxy)).1,
      hTa.2.2⟩
  have hTbG : IsAllowed H F {u,v,b} :=
    ⟨hTb.1, fun x hx y hy hxy =>
      ((SimpleGraph.sdiff_adj _ _ _ _).mp (hTb.2.1 x hx y hy hxy)).1,
      hTb.2.2⟩
  obtain ⟨i, hi6, hih, hCount⟩ := hClean u v a b hab hTaG hTbG
  refine ⟨i, hi6, hih, ?_⟩
  have hSurvive := S07V49.clean_hinges_after_edge_deletion
    (G := H.G) (lab := H.lab) (F := F) B d i ⟨hab,hTa,hTb⟩ hi6 hDeg
  have hPow : (Fintype.card V : ℝ) ^ (i-4) =
      Fintype.card V * (Fintype.card V : ℝ) ^ (i-5) := by
    rw [← pow_succ']
    congr 1
    omega
  have hTwo : (2 : ℝ) ^ i.choose 2 ≤ 2 ^ h.choose 2 :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
  have hCoeff : 5 * (d : ℝ) * 2 ^ i.choose 2 ≤ ε * Fintype.card V :=
    (mul_le_mul_of_nonneg_left hTwo (by positivity)).trans hBudget
  have hLoss : 5 * (d : ℝ) *
      (2 ^ i.choose 2 * (Fintype.card V : ℝ) ^ (i-5)) ≤
      ε * (Fintype.card V : ℝ) ^ (i-4) := by
    have hc := mul_le_mul_of_nonneg_right hCoeff
      (show (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (i-5) by positivity)
    rw [hPow]
    convert hc using 1 <;> ring
  calc
    (α - ε) * (Fintype.card V : ℝ) ^ (i-4) =
        α * (Fintype.card V : ℝ) ^ (i-4) -
          ε * (Fintype.card V : ℝ) ^ (i-4) := sub_mul _ _ _
    _ ≤ _ := sub_le_sub hCount hLoss
    _ ≤ _ := hSurvive

/-- The same fixed-order estimate on the actual paid edge complement. -/
theorem clean_hinge_after_sparse_edge_payment {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α ε : ℝ) (h : ℕ)
    (C : Finset (Sym2 V)) (d : ℕ)
    (hClean : CleanHingeCond H F α h) (hCE : C ⊆ edges H)
    (hDeg : ∀ x, SparseEdge.degIn C x ≤ d)
    (hBudget : 5 * (d : ℝ) * 2 ^ (h.choose 2) ≤ ε * Fintype.card V) :
    CleanHingeCond (subHost H (edges H \ C)) F (α - ε) h := by
  let B := SimpleGraph.fromEdgeSet (C : Set (Sym2 V))
  letI : DecidableRel B.Adj := Classical.decRel _
  have hDiag : ∀ e ∈ C, ¬e.IsDiag := CorePaid.edges_diagonal_free hCE
  have hBDeg : ∀ v, B.degree v ≤ d := by
    intro v
    rw [← SimpleGraph.card_incidenceFinset_eq_degree,
      SimpleGraph.incidenceFinset_eq_filter, CorePaid.edgeFinset_fromEdges C hDiag]
    exact hDeg v
  have hGeom := clean_hinge_after_sparse_payment H F α ε h B d hClean hBDeg hBudget
  rw [StockEntry.g4_graph_sdiff_eq_subHost H C] at hGeom
  simpa only [subHost] using hGeom

/-- Both geometry invariants retain the same hinge order and pay the same
additive budget against the actual sparse edge complement. -/
theorem clean_geometry_after_sparse_payment {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α ε : ℝ) (h : ℕ)
    (C : Finset (Sym2 V)) (d : ℕ)
    (h3 : CommonNbrCond H F α) (hClean : CleanHingeCond H F α h)
    (hCE : C ⊆ edges H) (hDeg : ∀ x, SparseEdge.degIn C x ≤ d)
    (hBudget : 5 * (d : ℝ) * 2 ^ (h.choose 2) ≤ ε * Fintype.card V) :
    CommonNbrCond (subHost H (edges H \ C)) F (α - ε) ∧
      CleanHingeCond (subHost H (edges H \ C)) F (α - ε) h := by
  have hp : (1 : ℝ) ≤ 2 ^ h.choose 2 := one_le_pow₀ (by norm_num)
  have hTwo : 2 * (d : ℝ) ≤ ε * Fintype.card V := by
    have hc := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 5*d by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  exact ⟨commonNbr_after_sparse_payment_additive H F α ε C d h3 hDeg hTwo,
    clean_hinge_after_sparse_edge_payment H F α ε h C d hClean hCE hDeg hBudget⟩

#print axioms CleanHingeCond.mono
#print axioms commonNbr_after_sparse_payment_additive
#print axioms clean_hinge_after_sparse_payment
#print axioms clean_hinge_after_sparse_edge_payment
#print axioms clean_geometry_after_sparse_payment
end TypedTriangle.Vortex
