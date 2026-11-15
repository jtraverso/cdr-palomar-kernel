/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.PrescribedCounting.FlattenedSetup
public import CDRIIILib.KBicolor.PrescribedCounting.ActualOutline

/-! # A concrete reference cross family and its integer type tournament -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle
open CDRBicolour.KBicolor.Wilson
variable {A : Type} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

theorem bic_of_mem_bicF {a b c : Fin k}
    (h : ({a,b,c} : Multiset (Fin k)) ∈ bicF k) : Pattern.bic a b c := by
  rcases mem_bicF.mp h with ⟨he,hne⟩ | ⟨he,hne⟩ | ⟨he,hne⟩
  · exact Or.inl ⟨he,by simpa only [he] using hne.symm⟩
  · exact Or.inr ⟨hne,Or.inl he.symm⟩
  · exact Or.inr ⟨hne,Or.inr he.symm⟩

theorem exists_reference_cross (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}
    (hS : _root_.STS.IsSTS S) :
    ∃ (Λ : VariableCross.Family S (groupOrder A t)) (x : Fin k → Fin k → ℕ),
      Pattern.IsTour (Hilton.csize (groupLabels κ t)) x ∧
      IsPacking (kHost lab) (bicF k) (VariableCross.packing (groupEmbedding h) Λ) ∧
      ∀ i j, i ≠ j → kTypeCount lab (VariableCross.packing (groupEmbedding h) Λ) i j=
        3*(Fintype.card (VariableCross.Block S)*x i j) := by
  have hlpos : 0 < Nat.card {l : Fin t → Fin t → Fin t // _root_.STS.IsLatin l} :=
    lt_of_lt_of_le Nat.zero_lt_one (_root_.STS.L_pos t)
  obtain ⟨l⟩ := (Nat.card_pos_iff.mp hlpos).1
  let L := referenceTable h l.1
  have hL : _root_.STS.IsLatin L := referenceTable_latin h l.1 l.2
  have hok : ∀ a b, Pattern.bic (groupLabels κ t a) (groupLabels κ t b) (groupLabels κ t (L a b)) :=
    fun a b => bic_of_mem_bicF (referenceTable_allowed h l.1 a b)
  obtain ⟨x,hx,hcount⟩ := actual_latin_type_tournament (groupLabels κ t) L hL hok
  let Λ : VariableCross.Family S (groupOrder A t) := fun _ => ⟨L,hL⟩
  refine ⟨Λ,x,hx,⟨?_,VariableCross.packing_disjoint (groupEmbedding h) hS Λ⟩,?_⟩
  · apply VariableCross.packing_allowed (groupEmbedding h) lab (groupLabels κ t)
      (groupEmbedding_label h) Λ
    intro o a b
    exact referenceTable_allowed h l.1 a b
  · intro i j hij
    rw [VariableCross.packing_typeCount (groupEmbedding h) hS lab (groupLabels κ t) (groupEmbedding_label h)]
    simp only [Λ]
    simp_rw [hcount i j hij]
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
    ring

end CDRBicolour.KBicolor.PrescribedCounting
