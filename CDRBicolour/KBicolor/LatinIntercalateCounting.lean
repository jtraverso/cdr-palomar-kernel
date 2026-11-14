/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ApplicationsLatinPaschIntercalates

/-! # Four orientations of each literal Latin intercalate -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle.Applications.Latin
variable {A : Type} [Fintype A]

def orientedIntercalates (L : LatinSquare A) : Finset (A×A×A×A) :=
  univ.filter (fun p => p.2.1 ≠ p.1 ∧ p.2.2.2 ≠ p.2.2.1 ∧
    L p.2.1 p.2.2.1 = L p.1 p.2.2.2 ∧ L p.2.1 p.2.2.2 = L p.1 p.2.2.1)

theorem rectangle_eq_iff {a b c d r r' s s' : A} (hab : a ≠ b) (hcd : c ≠ d) :
    intercalateCells a b c d = intercalateCells r r' s s' ↔
      ((a=r ∧ b=r') ∨ (a=r' ∧ b=r)) ∧ ((c=s ∧ d=s') ∨ (c=s' ∧ d=s)) := by
  constructor
  · intro he
    have hac : (a,c) ∈ intercalateCells r r' s s' := he ▸ (by simp [intercalateCells])
    have hbc : (b,c) ∈ intercalateCells r r' s s' := he ▸ (by simp [intercalateCells])
    have had : (a,d) ∈ intercalateCells r r' s s' := he ▸ (by simp [intercalateCells])
    simp only [intercalateCells, mem_insert, mem_singleton, Prod.mk.injEq] at hac hbc had
    have ha : a=r ∨ a=r' := by tauto
    have hb : b=r ∨ b=r' := by tauto
    have hc : c=s ∨ c=s' := by tauto
    have hd : d=s ∨ d=s' := by tauto
    constructor
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩
      · exact False.elim (hab rfl)
    · rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact False.elim (hcd rfl)
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩
      · exact False.elim (hcd rfl)
  · rintro ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩), (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ <;>
      ext p <;> simp [intercalateCells, or_assoc, or_comm, or_left_comm]

theorem oriented_fibre_eq (L : LatinSquare A) {r r' c c' : A}
    (hr : r' ≠ r) (hc : c' ≠ c)
    (h₁ : L r' c = L r c') (h₂ : L r' c' = L r c) :
    ((orientedIntercalates L).filter (fun p =>
      intercalateCells p.1 p.2.1 p.2.2.1 p.2.2.2 = intercalateCells r r' c c')) =
      {(r,r',c,c'), (r',r,c,c'), (r,r',c',c), (r',r,c',c)} := by
  ext p
  rcases p with ⟨a,b,c₀,d⟩
  simp only [orientedIntercalates, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hp, he⟩
    have hh := (rectangle_eq_iff hp.1.symm hp.2.1.symm).mp he
    rcases hh with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩), (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ <;> simp
  · intro hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with hp | hp | hp | hp <;> cases hp <;>
      simp [hr, hc, Ne.symm hr, Ne.symm hc, h₁, h₂, intercalateCells,
        or_assoc, or_comm, or_left_comm, Finset.ext_iff]

theorem four_mul_intercalates (L : LatinSquare A) :
    4 * (intercalates L).card = (orientedIntercalates L).card := by
  let f : A×A×A×A → Finset (A×A) := fun p =>
    intercalateCells p.1 p.2.1 p.2.2.1 p.2.2.2
  have hsum := card_eq_sum_card_image f (orientedIntercalates L)
  have himage : (orientedIntercalates L).image f = intercalates L := rfl
  rw [himage] at hsum
  have hcard : ∀ B ∈ intercalates L, #((orientedIntercalates L).filter (fun p => f p = B)) = 4 := by
    intro B hB
    obtain ⟨r,r',c,c',hr,hc,h₁,h₂,rfl⟩ := (mem_intercalates L B).mp hB
    rw [oriented_fibre_eq L hr hc h₁ h₂]
    simp [hr, hc, Ne.symm hr, Ne.symm hc, Prod.mk.injEq]
  rw [sum_congr rfl hcard] at hsum
  simpa [mul_comm] using hsum.symm

end CDRBicolour.KBicolor.LatinPasch
