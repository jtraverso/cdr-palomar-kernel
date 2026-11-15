/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.GlobalSeed

/-!
# Exact colour counts and balance on the actual Wilson pieces
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined
open scoped Classical

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t)

theorem group_card (i : Fin g) : #(group h i) = Fintype.card A * t := by
  have hinj : Function.Injective (fun p : A × Fin t => gv h i p.1 p.2) := by
    intro p q hpq
    have he := (gv_inj h hpq).2
    exact Prod.ext he.1 he.2
  simp only [group,card_image_of_injective _ hinj,card_univ,Fintype.card_prod,Fintype.card_fin]

theorem group_class_card (i : Fin g) (X : Fin k) :
    #((group h i).filter fun v => lab v = X) = Hilton.csize κ X * t := by
  have hinj : Function.Injective (fun p : A × Fin t => gv h i p.1 p.2) := by
    intro p q hpq
    have he := (gv_inj h hpq).2
    exact Prod.ext he.1 he.2
  rw [group,filter_image,card_image_of_injective _ hinj]
  have hset : (univ.filter fun p : A × Fin t => lab (gv h i p.1 p.2) = X) =
      (univ.filter fun P => κ P = X) ×ˢ (univ : Finset (Fin t)) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_product,and_true]
    simp only [gv,h.label]
  rw [hset,card_product,card_univ,Fintype.card_fin]
  simp only [Hilton.csize,Fintype.card_subtype]

theorem group_reserve_disjoint (i : Fin g) : Disjoint (group h i) (reserve h) := by
  exact disjoint_left.mpr fun _ hu hR => group_not_reserve h hu hR

theorem piece_order (i : Fin g) : Fintype.card (Piece h i) = Fintype.card A*t + #(reserve h) := by
  rw [Fintype.card_coe,piece,card_union_of_disjoint (group_reserve_disjoint h i),group_card]

theorem reserve_order : #(reserve h) + g*(Fintype.card A*t) = n := by
  have hc := card_sdiff_add_card_eq_card (s := univ.image h.embed) (t := univ) (subset_univ _)
  rw [card_image_of_injective _ h.embed.injective,card_univ,card_univ] at hc
  simpa only [reserve,Fintype.card_prod,Fintype.card_fin,mul_assoc] using hc

theorem piece_filter_card (i : Fin g) (p : Fin n → Prop) [DecidablePred p] :
    #((univ : Finset (Piece h i)).filter fun u => p u.val) = #((piece h i).filter p) := by
  apply card_bij (fun u _ => u.val)
  · intro u hu
    exact mem_filter.mpr ⟨u.property,(mem_filter.mp hu).2⟩
  · intro u _ v _ he; exact Subtype.ext he
  · intro v hv
    exact ⟨⟨v,(mem_filter.mp hv).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩,rfl⟩

theorem piece_reserve_counts (i : Fin g) (X : Fin k) :
    #((pieceReserve h i).filter fun u => pieceLab h i u = X) =
      #((reserve h).filter fun v => lab v = X) := by
  unfold pieceReserve pieceLab
  rw [filter_filter,piece_filter_card h i (fun v => v ∈ reserve h ∧ lab v=X)]
  congr 1
  ext v
  simp only [mem_filter,piece,mem_union]
  tauto

theorem piece_group_counts (i : Fin g) (X : Fin k) :
    #((univ \ pieceReserve h i).filter fun u => pieceLab h i u = X) = Hilton.csize κ X*t := by
  have hset : ((univ \ pieceReserve h i).filter fun u => pieceLab h i u = X) =
      univ.filter fun u : Piece h i => u.val ∉ reserve h ∧ lab u.val = X := by
    ext u
    unfold pieceReserve pieceLab
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
  rw [hset,piece_filter_card h i (fun v => v ∉ reserve h ∧ lab v=X)]
  have hset' : (piece h i).filter (fun u => u ∉ reserve h ∧ lab u = X) =
      (group h i).filter fun u => lab u = X := by
    ext u
    simp only [mem_filter,piece,mem_union]
    constructor
    · rintro ⟨hu,huR,hX⟩
      exact ⟨hu.resolve_right huR,hX⟩
    · rintro ⟨hu,hX⟩
      exact ⟨Or.inl hu,group_not_reserve h hu,hX⟩
  rw [hset',group_class_card]

theorem piece_class_counts (i : Fin g) (X : Fin k) :
    ksz (pieceLab h i) X = Hilton.csize κ X*t + #((reserve h).filter fun v => lab v = X) := by
  unfold ksz
  change #((univ : Finset (Piece h i)).filter fun u => lab u.val=X) = _
  rw [piece_filter_card h i (fun v => lab v=X)]
  have hd : Disjoint ((group h i).filter fun v => lab v = X)
      ((reserve h).filter fun v => lab v = X) :=
    disjoint_left.mpr (fun _ hu hR => group_not_reserve h (mem_filter.mp hu).1 (mem_filter.mp hR).1)
  rw [piece,filter_union,card_union_of_disjoint hd,group_class_card]

theorem piece_balance_from_profile
    (hglobal : 3*∑ X, (ksz lab X : ℝ)^2 = (n : ℝ)^2+2*n)
    (hcone : 3*∑ X, Hilton.csize κ X^2 = (∑ X, Hilton.csize κ X)^2) (i : Fin g) :
    (g : ℝ)*profileDefect
      ((fun X => (#((univ \ pieceReserve h i).filter fun u => pieceLab h i u = X) : ℝ)) +
       (fun X => (#((pieceReserve h i).filter fun u => pieceLab h i u = X) : ℝ))) =
      ((g : ℝ)-1)*profileDefect
        (fun X => (#((pieceReserve h i).filter fun u => pieceLab h i u = X) : ℝ)) := by
  have hsum : ∑ X, ksz lab X = n := by
    have hh := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
      (t := univ) (f := lab) (fun _ _ => mem_univ _)
    simpa only [card_univ,Fintype.card_fin,ksz] using hh.symm
  have hr : ∀ X, (#((reserve h).filter fun u => lab u = X) : ℝ) =
      (ksz lab X : ℝ) - (g : ℝ)*Hilton.csize κ X*t := by
    intro X
    have hh : (#((reserve h).filter fun u => lab u = X) : ℝ) +
        (g : ℝ)*Hilton.csize κ X*t = ksz lab X := by
      exact_mod_cast reserve_class_card h X
    linarith
  simp only [piece_group_counts,piece_reserve_counts,Nat.cast_mul,hr]
  exact local_balance_of_counts (ksz lab) (Hilton.csize κ) g t hsum hglobal hcone

end CDRBicolour.KBicolor.Wilson
