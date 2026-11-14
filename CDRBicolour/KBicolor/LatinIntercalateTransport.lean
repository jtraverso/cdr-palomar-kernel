/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.LatinIntercalateCounting

/-! # Relabelling and isotopy preserve the number of intercalates -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle.Applications.Latin
variable {A B : Type} [Fintype A] [Fintype B]

def isotopySquare (L : LatinSquare A) (ρ σ : Equiv.Perm A) : LatinSquare A where
  toFun r c := σ (L (ρ r) c)
  row_bijective r := σ.bijective.comp (L.row_bijective (ρ r))
  column_bijective c := σ.bijective.comp ((L.column_bijective c).comp ρ.bijective)

theorem oriented_card_isotopy (L : LatinSquare A) (ρ σ : Equiv.Perm A) :
    (orientedIntercalates (isotopySquare L ρ σ)).card = (orientedIntercalates L).card := by
  apply card_bij (fun p _ => (ρ p.1,ρ p.2.1,p.2.2.1,p.2.2.2))
  · intro p hp
    simp only [orientedIntercalates, mem_filter, mem_univ, true_and, isotopySquare] at hp ⊢
    exact ⟨fun he => hp.1 (ρ.injective he), hp.2.1,
      σ.injective hp.2.2.1, σ.injective hp.2.2.2⟩
  · rintro ⟨a,b,c,d⟩ _ ⟨a',b',c',d'⟩ _ he
    simpa only [Prod.mk.injEq, ρ.injective.eq_iff] using he
  · rintro ⟨a,b,c,d⟩ hp
    refine ⟨(ρ.symm a,ρ.symm b,c,d),?_,?_⟩
    · simp only [orientedIntercalates, mem_filter, mem_univ, true_and,
        isotopySquare, Equiv.apply_symm_apply] at hp ⊢
      exact ⟨fun he => hp.1 (ρ.symm.injective he),hp.2.1,
        congrArg σ hp.2.2.1,congrArg σ hp.2.2.2⟩
    · simp

theorem intercalates_card_isotopy (L : LatinSquare A) (ρ σ : Equiv.Perm A) :
    (intercalates (isotopySquare L ρ σ)).card = (intercalates L).card := by
  have h₁ := four_mul_intercalates (isotopySquare L ρ σ)
  have h₂ := four_mul_intercalates L
  rw [oriented_card_isotopy] at h₁
  omega

def transportSquare (e : A ≃ B) (L : LatinSquare A) : LatinSquare B where
  toFun r c := e (L (e.symm r) (e.symm c))
  row_bijective r := e.bijective.comp ((L.row_bijective (e.symm r)).comp e.symm.bijective)
  column_bijective c := e.bijective.comp ((L.column_bijective (e.symm c)).comp e.symm.bijective)

theorem oriented_card_transport (e : A ≃ B) (L : LatinSquare A) :
    (orientedIntercalates (transportSquare e L)).card = (orientedIntercalates L).card := by
  apply card_bij (fun p _ => (e.symm p.1,e.symm p.2.1,e.symm p.2.2.1,e.symm p.2.2.2))
  · intro p hp
    simp only [orientedIntercalates, mem_filter, mem_univ, true_and, transportSquare] at hp ⊢
    exact ⟨fun he => hp.1 (e.symm.injective he), fun he => hp.2.1 (e.symm.injective he),
      e.injective hp.2.2.1, e.injective hp.2.2.2⟩
  · rintro ⟨a,b,c,d⟩ _ ⟨a',b',c',d'⟩ _ he
    simpa only [Prod.mk.injEq, e.symm.injective.eq_iff] using he
  · rintro ⟨a,b,c,d⟩ hp
    refine ⟨(e a,e b,e c,e d),?_,?_⟩
    · simp only [orientedIntercalates, mem_filter, mem_univ, true_and,
        transportSquare, Equiv.symm_apply_apply] at hp ⊢
      exact ⟨fun he => hp.1 (e.injective he),fun he => hp.2.1 (e.injective he),
        congrArg e hp.2.2.1,congrArg e hp.2.2.2⟩
    · simp

theorem intercalates_card_transport (e : A ≃ B) (L : LatinSquare A) :
    (intercalates (transportSquare e L)).card = (intercalates L).card := by
  have h₁ := four_mul_intercalates (transportSquare e L)
  have h₂ := four_mul_intercalates L
  rw [oriented_card_transport] at h₁
  omega

end CDRBicolour.KBicolor.LatinPasch
