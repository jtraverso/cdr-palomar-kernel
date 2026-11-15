/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.LatinIntercalateCounting

/-! # Intercalates of an abelian-group table

A difference h != 0 with h+h=0, an initial row and an initial column
parametrize the oriented intercalates bijectively. Four orientations
represent each unoriented configuration.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle.Applications.Latin
variable {A : Type} [Fintype A] [AddCommGroup A]

def twoTorsion (A : Type*) [Fintype A] [AddCommGroup A] : Finset A :=
  univ.filter (fun h => h+h=0)

def nonzeroTwoTorsion (A : Type*) [Fintype A] [AddCommGroup A] : Finset A :=
  univ.filter (fun h => h ≠ 0 ∧ h+h=0)

def groupRectangle (p : A×A×A) : A×A×A×A := (p.1, p.1+p.2.2, p.2.1, p.2.1+p.2.2)

theorem groupRectangle_injective : Function.Injective (groupRectangle (A := A)) := by
  rintro ⟨r,c,h⟩ ⟨r',c',h'⟩ he
  simp only [groupRectangle, Prod.mk.injEq] at he
  rcases he with ⟨rfl, he, rfl, _⟩
  have hh : h=h' := add_left_cancel he
  subst h'
  rfl

theorem groupRectangle_image :
    (univ ×ˢ (univ ×ˢ nonzeroTwoTorsion A)).image groupRectangle =
      orientedIntercalates (LatinSquare.add A) := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨r,c,h⟩, hm, rfl⟩ := mem_image.mp hp
    have hh : h ≠ 0 ∧ h+h=0 := by simpa [nonzeroTwoTorsion] using hm
    simp only [orientedIntercalates, mem_filter, mem_univ, true_and]
    change r+h ≠ r ∧ c+h ≠ c ∧ (r+h)+c=r+(c+h) ∧ (r+h)+(c+h)=r+c
    refine ⟨?_, ?_, by abel, ?_⟩
    · intro he
      apply hh.1
      exact add_left_cancel (a := r) (by simpa using he)
    · intro he
      apply hh.1
      exact add_left_cancel (a := c) (by simpa using he)
    · calc
        (r+h)+(c+h)=(r+c)+(h+h) := by abel
        _=r+c := by rw [hh.2]; simp
  · rcases p with ⟨a,b,c,d⟩
    intro hp
    have hp' : b ≠ a ∧ d ≠ c ∧ b+c=a+d ∧ b+d=a+c := by
      simpa [orientedIntercalates, LatinSquare.add] using hp
    obtain ⟨hba, hdc, h₁, h₂⟩ := hp'
    let h := b-a
    have hb : b=a+h := by dsimp [h]; abel
    have hd : d=c+h := by
      apply add_left_cancel (a := a)
      calc
        a+d=b+c := h₁.symm
        _=a+(c+h) := by rw [hb]; abel
    have hzero : h+h=0 := by
      apply add_left_cancel (a := a+c)
      calc
        (a+c)+(h+h)=(a+h)+(c+h) := by abel
        _=b+d := by rw [← hb, ← hd]
        _=(a+c)+0 := by simpa using h₂
    have hn : h ≠ 0 := by intro he; rw [he, add_zero] at hb; exact hba hb
    apply mem_image.mpr
    refine ⟨(a,c,h), ?_, ?_⟩
    · simp [nonzeroTwoTorsion, hn, hzero]
    · simp only [groupRectangle, hb, hd]

theorem oriented_group_card : (orientedIntercalates (LatinSquare.add A)).card =
    (Fintype.card A)^2 * (nonzeroTwoTorsion A).card := by
  rw [← groupRectangle_image, card_image_of_injective _ groupRectangle_injective]
  simp only [card_product, card_univ]
  ring

theorem nonzeroTwoTorsion_card : (nonzeroTwoTorsion A).card = (twoTorsion A).card-1 := by
  have heq : nonzeroTwoTorsion A = (twoTorsion A).erase 0 := by
    ext h
    simp [nonzeroTwoTorsion, twoTorsion, and_left_comm, and_comm]
  rw [heq, card_erase_of_mem]
  simp [twoTorsion]

/-- The exact factor four agrees with Paper III's unoriented Pasch count. -/
theorem four_mul_group_intercalates :
    4 * (intercalates (LatinSquare.add A)).card =
      (Fintype.card A)^2 * ((twoTorsion A).card-1) := by
  rw [four_mul_intercalates, oriented_group_card, nonzeroTwoTorsion_card]

end CDRBicolour.KBicolor.LatinPasch
