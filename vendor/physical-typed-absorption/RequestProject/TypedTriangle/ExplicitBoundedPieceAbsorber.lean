/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitPreparedAbsorberSupply
public import RequestProject.TypedTriangle.BoundedPieceAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative.Explicit

def boundedPieceBudget (α : ℝ) (h : ℕ) : ℝ := S07V30.delta α 1 h
def boundedPieceSize (α : ℝ) (h k : ℕ) : ℕ := PreparedSupply.Explicit.supplySize α h k
def boundedPieceOrder (α : ℝ) (h k : ℕ) : ℕ :=
  max (PreparedSupply.Explicit.absorberOrder α h) (PreparedSupply.Explicit.supplyOrder α h k)

theorem boundedPieceBudget_pos {α : ℝ} (h : ℕ) (hα : 0 < α) :
    0 < boundedPieceBudget α h := S07V30.delta_pos hα (by norm_num) h

/-- Single-piece absorption with all numerical parameters specified. -/
theorem bounded_piece_absorber_explicit (α : ℝ) (h k : ℕ) (hα : 0 < α) :
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        boundedPieceOrder α h k ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ P : Finset (Sym2 V), IsPhysical H F P → P.card ≤ k →
        ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, degIn B v ≤ b) →
          (b:ℝ) ≤ boundedPieceBudget α h*Fintype.card V →
          ∃ A : Finset (Sym2 V), IsAbsorber H F A P ∧ Disjoint A B ∧ A.card ≤ boundedPieceSize α h k := by
  let K := PreparedSupply.Explicit.absorberCost α h
  let U := PreparedSupply.Explicit.supplySupport α h k
  intro V I _ H F hn h3 h4 P hP hPk B b hB hb
  have hRoot : (support P).card ≤ 2*k := (S07V28.card_support_le P).trans (Nat.mul_le_mul_left 2 hPk)
  have hInside : Inside (support P) P := by
    intro e he v hv
    exact mem_filter.mpr ⟨mem_univ _,e,he,hv⟩
  have hBudget : (support P).card+3*(K*P.card)+K*P.card*(2*h-2)+
      3*(K*P.card)*(2*h-3) ≤ U := by
    dsimp [U,PreparedSupply.Explicit.supplySupport,K]
    gcongr
  obtain ⟨_,_,hw1,hw2⟩ := S07V30.deletion_window hα (by norm_num : (0:ℝ)<1) U h
    (Fintype.card V) (Fintype.card V) 0 b
    ((le_max_right _ _).trans hn) (by omega) (Nat.zero_le _) (Nat.le_floor hb)
  obtain ⟨A,hA,hAB,hAc⟩ := PreparedSupply.Explicit.slot_absorber_explicit α h hα H F ((le_max_left _ _).trans hn) h3 h4 B b hB P hP
    (support P) hInside U hBudget hw1 hw2
  exact ⟨A,hA,hAB,hAc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hPk))⟩


theorem bounded_piece_absorber_deleted_explicit (α : ℝ) (h k : ℕ) (hα : 0 < α) :
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (Z : Finset V),
        boundedPieceOrder α h k ≤ Fintype.card (Survivors Z) →
        CommonNbrCond (restrictedHost H Z) F α → HingeCond (restrictedHost H Z) F α h →
        ∀ P : Finset (Sym2 V), IsPhysical (vertexDeleted H Z) F P → P.card ≤ k →
          (∀ e ∈ P, ∀ v ∈ e, v ∉ Z) →
        ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, degIn B v ≤ b) →
          (b:ℝ) ≤ boundedPieceBudget α h*Fintype.card (Survivors Z) →
          ∃ A : Finset (Sym2 V), IsAbsorber H F A P ∧ Disjoint A B ∧ A.card ≤ boundedPieceSize α h k ∧
            ∀ e ∈ A, ∀ v ∈ e, v ∉ Z := by
  intro V I _ H F Z hn h3 h4 P hP hPk hav B b hB hb
  have hPullPhys : IsPhysical (restrictedHost H Z) F (CorePayment.pullEdges Z P) := by
    rw [IsPhysical,PreparedSupply.pull_ind]
    exact edgeRestrict_mem_lattice H F Z hP
  have hPullCard : (CorePayment.pullEdges Z P).card ≤ k := by
    apply le_trans _ hPk
    rw [CorePayment.pullEdges,card_preimage]
    exact card_filter_le _ _
  have hPullDeg : ∀ v, degIn (CorePayment.pullEdges Z B) v ≤ b := by
    intro v
    have hh := CorePayment.degree_pull_le Z B v
    simp only [CorePayment.edeg_eq_classical] at hh
    exact (show degIn (CorePayment.pullEdges Z B) v ≤ degIn B v.1 by simpa only [degIn,SelSimul.edeg] using hh).trans (hB v.1)
  obtain ⟨A,hA,hAB,hAc⟩ := bounded_piece_absorber_explicit α h k hα (restrictedHost H Z) F hn h3 h4
    (CorePayment.pullEdges Z P) hPullPhys hPullCard (CorePayment.pullEdges Z B) b hPullDeg hb
  refine ⟨CorePayment.liftEdges Z A,PreparedSupply.absorber_lift Z hav hA,?_,card_image_le.trans hAc,
    CorePayment.liftEdges_avoids Z A⟩
  apply disjoint_left.mpr
  intro e he heB
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  exact disjoint_left.mp hAB hf (mem_preimage.mpr heB)

#print axioms bounded_piece_absorber_explicit
#print axioms bounded_piece_absorber_deleted_explicit
end TypedTriangle.CatalogNative.Explicit
