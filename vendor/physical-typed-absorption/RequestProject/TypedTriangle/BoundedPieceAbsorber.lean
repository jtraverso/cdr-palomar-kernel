/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SampleConstruct
public import RequestProject.TypedTriangle.PreparedAbsorberSupply
public import RequestProject.S07V30.DeletionWindow
public import RequestProject.S07V28.AbsorberPlacement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
variable {V I : Type*} [Fintype V]

/-- A uniformly bounded physical piece has a direct G2 absorber outside a
sparse forbidden edge set. No universal TerminalSupply or prepared persistence
is needed when a single specified physical piece is being absorbed. -/
theorem bounded_piece_absorber (α : ℝ) (h k : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ E n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ P : Finset (Sym2 V), IsPhysical H F P → P.card ≤ k →
        ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, degIn B v ≤ b) →
          (b:ℝ) ≤ ε*Fintype.card V →
          ∃ A : Finset (Sym2 V), IsAbsorber H F A P ∧ Disjoint A B ∧ A.card ≤ E := by
  obtain ⟨K,nA,hAbs⟩ := slot_absorber_of_H3H4 α h hα
  let U := 2*k+3*(K*k)+K*k*(2*h-2)+3*(K*k)*(2*h-3)
  obtain ⟨ε,hε,nW,hWin⟩ := S07V30.exists_deletion_window hα (by norm_num : (0:ℝ) < 1) U h
  refine ⟨ε,hε,K*k*(4*(2*h-2).choose 2+6),max nA nW,?_⟩
  intro V I _ H F hn h3 h4 P hP hPk B b hB hb
  have hRoot : (support P).card ≤ 2*k := (S07V28.card_support_le P).trans (Nat.mul_le_mul_left 2 hPk)
  have hInside : Inside (support P) P := by
    intro e he v hv
    exact mem_filter.mpr ⟨mem_univ _,e,he,hv⟩
  have hBudget : (support P).card+3*(K*P.card)+K*P.card*(2*h-2)+
      3*(K*P.card)*(2*h-3) ≤ U := by
    dsimp [U]
    gcongr
  obtain ⟨_,_,hw1,hw2⟩ := hWin (Fintype.card V) (Fintype.card V) 0 b
    ((le_max_right _ _).trans hn) (by omega) (Nat.zero_le _) (Nat.le_floor hb)
  obtain ⟨A,hA,hAB,hAc⟩ := hAbs H F ((le_max_left _ _).trans hn) h3 h4 B b hB P hP
    (support P) hInside U hBudget hw1 hw2
  exact ⟨A,hA,hAB,hAc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hPk))⟩

/-- Work directly in the true surviving host and lift the single-piece
absorber back. The piece is required to be physical AFTER deletion; this is
exactly the property supplied by the native catalog rerouting and polarization. -/
theorem bounded_piece_absorber_deleted (α : ℝ) (h k : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ E n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (Z : Finset V),
        n₀ ≤ Fintype.card (Survivors Z) →
        CommonNbrCond (restrictedHost H Z) F α → HingeCond (restrictedHost H Z) F α h →
        ∀ P : Finset (Sym2 V), IsPhysical (vertexDeleted H Z) F P → P.card ≤ k →
          (∀ e ∈ P, ∀ v ∈ e, v ∉ Z) →
        ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, degIn B v ≤ b) →
          (b:ℝ) ≤ ε*Fintype.card (Survivors Z) →
          ∃ A : Finset (Sym2 V), IsAbsorber H F A P ∧ Disjoint A B ∧ A.card ≤ E ∧
            ∀ e ∈ A, ∀ v ∈ e, v ∉ Z := by
  obtain ⟨ε,hε,E,n₀,hAbs⟩ := bounded_piece_absorber α h k hα
  refine ⟨ε,hε,E,n₀,?_⟩
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
  obtain ⟨A,hA,hAB,hAc⟩ := hAbs (restrictedHost H Z) F hn h3 h4
    (CorePayment.pullEdges Z P) hPullPhys hPullCard (CorePayment.pullEdges Z B) b hPullDeg hb
  refine ⟨CorePayment.liftEdges Z A,PreparedSupply.absorber_lift Z hav hA,?_,card_image_le.trans hAc,
    CorePayment.liftEdges_avoids Z A⟩
  apply disjoint_left.mpr
  intro e he heB
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  exact disjoint_left.mp hAB hf (mem_preimage.mpr heB)
end TypedTriangle.CatalogNative
