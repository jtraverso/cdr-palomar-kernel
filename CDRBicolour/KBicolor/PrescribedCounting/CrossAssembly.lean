/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.VariableCross
public import CDRBicolour.KBicolor.CountingConsequencesFinite

/-! # Injective assembly with a fixed completed residual -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting.VariableCross
open Finset Classical TypedTriangle CDRBicolour.Absorption
variable {n g B k : ℕ} {S : Finset (Finset (Fin g))}

theorem packing_allowed (e : (Fin g × Fin B) ↪ Fin n) (lab : Fin n → Fin k)
    (κ : Fin B → Fin k) (hlabel : ∀ p a, lab (e (p,a))=κ a)
    (Λ : Family S B)
    (hok : ∀ o a b, ({κ a,κ b,κ ((Λ o).1 a b)} : Multiset (Fin k)) ∈ bicF k) :
    ∀ T ∈ packing e Λ, IsAllowed (kHost lab) (bicF k) T := by
  intro T hT
  obtain ⟨x,-,rfl⟩ := mem_image.mp hT
  apply isAllowed_triple lab (pos_ne e Λ x (by decide)) (pos_ne e Λ x (by decide))
    (pos_ne e Λ x (by decide))
  simpa only [pos,slot,hlabel,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    Matrix.cons_val_two,Matrix.tail_cons] using hok x.1 x.2.1 x.2.2

theorem packing_disjoint_residual (e : (Fin g × Fin B) ↪ Fin n)
    (lab : Fin n → Fin k) (Λ : Family S B) {D : Finset (Finset (Fin n))}
    (hD : ∀ T ∈ D, IsAllowed (rHostK lab ((packing e Λ).biUnion triEdges)) (bicF k) T) :
    Disjoint (packing e Λ) D := by
  apply disjoint_left.mpr
  intro T hT hTD
  obtain ⟨x,-,rfl⟩ := mem_image.mp hT
  have he : s(pos e Λ x 0,pos e Λ x 1) ∈ triEdges (triangle e Λ x) :=
    mem_triEdges.mpr ⟨by simp [triangle],by simp [triangle],pos_ne e Λ x (by decide)⟩
  exact disjoint_left.mp (disj_of_rHostK lab (hD _ hTD)) he
    (mem_biUnion.mpr ⟨_,mem_image.mpr ⟨x,mem_univ _,rfl⟩,he⟩)

abbrev Choices (tables : Block S → Finset (Fin B → Fin B → Fin B)) :=
  ∀ o, {L // L ∈ tables o}

def chosenFamily (tables : Block S → Finset (Fin B → Fin B → Fin B))
    (hLatin : ∀ o L, L ∈ tables o → _root_.STS.IsLatin L) (f : Choices tables) : Family S B :=
  fun o => ⟨(f o).1,hLatin o _ (f o).2⟩

theorem family_count_le_exact (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (lab : Fin n → Fin k) (Λ₀ : Family S B) (tv : TypeCoord k → ℕ)
    (tables : Block S → Finset (Fin B → Fin B → Fin B))
    (hLatin : ∀ o L, L ∈ tables o → _root_.STS.IsLatin L)
    (hAllowed : ∀ f : Choices tables, ∀ T ∈ packing e (chosenFamily tables hLatin f),
      IsAllowed (kHost lab) (bicF k) T)
    (D : Finset (Finset (Fin n)))
    (hD : IsDecomposition (rHostK lab ((packing e Λ₀).biUnion triEdges)) (bicF k)
      (edges (rHostK lab ((packing e Λ₀).biUnion triEdges))) D)
    (htype : ∀ f : Choices tables,
      typeVector lab (D ∪ packing e (chosenFamily tables hLatin f))=tv) :
    (∏ o, (tables o).card) ≤ exactTypeCount lab tv := by
  let fam := chosenFamily tables hLatin
  have hDf : ∀ f : Choices tables,
      IsDecomposition (rHostK lab ((packing e (fam f)).biUnion triEdges)) (bicF k)
        (edges (rHostK lab ((packing e (fam f)).biUnion triEdges))) D := by
    intro f
    rw [edges_eq e hS (fam f) Λ₀]
    exact hD
  have hd : ∀ f : Choices tables, Disjoint (packing e (fam f)) D :=
    fun f => packing_disjoint_residual e lab (fam f) (hDf f).1
  have hinj : Function.Injective (fun f : Choices tables => D ∪ packing e (fam f)) := by
    intro f f' he
    have hre : ∀ f : Choices tables, (D ∪ packing e (fam f)) \ D=packing e (fam f) := by
      intro f
      rw [union_sdiff_left,sdiff_eq_self_of_disjoint (hd f)]
    have hp := congrArg (fun P : Finset (Finset (Fin n)) => P \ D) he
    rw [hre,hre] at hp
    have hΛ := packing_injective e hS hp
    funext o
    apply Subtype.ext
    exact congrArg (fun Λ : Family S B => (Λ o).1) hΛ
  have hcard : Fintype.card (Choices tables) ≤ exactTypeCount lab tv := by
    rw [← card_univ]
    apply card_le_card_of_injOn (fun f : Choices tables => D ∪ packing e (fam f))
      (fun f _ => ?_) (fun f _ f' _ he => hinj he)
    apply mem_filter.mpr
    exact ⟨mem_kBlocks_of_decomp lab
      (union_decomp lab (hAllowed f) (packing_disjoint e hS (fam f)) (hDf f)),htype f⟩
  simpa only [Choices,Fintype.card_pi,Fintype.card_coe] using hcard

end CDRBicolour.KBicolor.PrescribedCounting.VariableCross
