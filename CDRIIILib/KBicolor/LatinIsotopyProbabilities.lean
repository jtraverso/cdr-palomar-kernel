/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.TransitiveFiniteAverage

/-! # Exact one- and two-block frequencies in Latin isotopies

Uniform independent row and symbol permutations suffice. For pairs sharing
a symbol, fix the symbol permutation and invert the two columns; this
reduces the count to the same distinct-two-point permutation identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical
variable {A : Type*} [Fintype A] [DecidableEq A]

def isotopyValue (L : A → A → A) (ρ σ : Equiv.Perm A) (r c : A) : A := σ (L (ρ r) c)

theorem isotopy_single_frequency (L : A → A → A) (r c s : A) :
    (Fintype.card A : ℝ) *
      (∑ ρ : Equiv.Perm A, ∑ σ : Equiv.Perm A,
        if isotopyValue L ρ σ r c = s then (1 : ℝ) else 0) =
      (Fintype.card (Equiv.Perm A) : ℝ)^2 := by
  rw [mul_sum]
  have hh : ∀ ρ : Equiv.Perm A, (Fintype.card A : ℝ) *
      (∑ σ : Equiv.Perm A, if isotopyValue L ρ σ r c = s then (1 : ℝ) else 0) =
      Fintype.card (Equiv.Perm A) := fun ρ => permutation_point_indicator (L (ρ r) c) s
  rw [sum_congr rfl (fun ρ _ => hh ρ)]
  simp [sq]

theorem isotopy_shared_row_frequency (L : A → A → A)
    (hrow : ∀ a, Function.Injective (L a))
    (r c c' s s' : A) (hcc : c ≠ c') (hss : s ≠ s') :
    (Fintype.card A*(Fintype.card A-1) : ℕ) *
      (∑ ρ : Equiv.Perm A, ∑ σ : Equiv.Perm A,
        if isotopyValue L ρ σ r c = s ∧ isotopyValue L ρ σ r c' = s'
          then (1 : ℝ) else 0) = (Fintype.card (Equiv.Perm A) : ℝ)^2 := by
  rw [mul_sum]
  have hh : ∀ ρ : Equiv.Perm A, (Fintype.card A*(Fintype.card A-1) : ℕ) *
      (∑ σ : Equiv.Perm A, if isotopyValue L ρ σ r c = s ∧
        isotopyValue L ρ σ r c' = s' then (1 : ℝ) else 0) =
      Fintype.card (Equiv.Perm A) := fun ρ =>
    permutation_pair_indicator ((hrow (ρ r)).ne hcc) hss
  rw [sum_congr rfl (fun ρ _ => hh ρ)]
  simp [sq]

theorem isotopy_shared_column_frequency (L : A → A → A)
    (hcol : ∀ b, Function.Injective (fun a => L a b))
    (r r' c s s' : A) (hrr : r ≠ r') (hss : s ≠ s') :
    (Fintype.card A*(Fintype.card A-1) : ℕ) *
      (∑ ρ : Equiv.Perm A, ∑ σ : Equiv.Perm A,
        if isotopyValue L ρ σ r c = s ∧ isotopyValue L ρ σ r' c = s'
          then (1 : ℝ) else 0) = (Fintype.card (Equiv.Perm A) : ℝ)^2 := by
  rw [mul_sum]
  have hh : ∀ ρ : Equiv.Perm A, (Fintype.card A*(Fintype.card A-1) : ℕ) *
      (∑ σ : Equiv.Perm A, if isotopyValue L ρ σ r c = s ∧
        isotopyValue L ρ σ r' c = s' then (1 : ℝ) else 0) =
      Fintype.card (Equiv.Perm A) := fun ρ =>
    permutation_pair_indicator ((hcol c).ne (ρ.injective.ne hrr)) hss
  rw [sum_congr rfl (fun ρ _ => hh ρ)]
  simp [sq]

theorem isotopy_shared_symbol_frequency (L : A → A → A)
    (hrow : ∀ a, Function.Injective (L a))
    (hcol : ∀ b, Function.Bijective (fun a => L a b))
    (r r' c c' s : A) (hrr : r ≠ r') (hcc : c ≠ c') :
    (Fintype.card A*(Fintype.card A-1) : ℕ) *
      (∑ ρ : Equiv.Perm A, ∑ σ : Equiv.Perm A,
        if isotopyValue L ρ σ r c = s ∧ isotopyValue L ρ σ r' c' = s
          then (1 : ℝ) else 0) = (Fintype.card (Equiv.Perm A) : ℝ)^2 := by
  rw [sum_comm, mul_sum]
  have hh : ∀ σ : Equiv.Perm A, (Fintype.card A*(Fintype.card A-1) : ℕ) *
      (∑ ρ : Equiv.Perm A, if isotopyValue L ρ σ r c = s ∧
        isotopyValue L ρ σ r' c' = s then (1 : ℝ) else 0) =
      Fintype.card (Equiv.Perm A) := by
    intro σ
    obtain ⟨u, hu⟩ := (hcol c).2 (σ.symm s)
    obtain ⟨v, hv⟩ := (hcol c').2 (σ.symm s)
    have huv : u ≠ v := by
      intro he
      subst v
      exact hcc (hrow u (hu.trans hv.symm))
    have h₁ : ∀ ρ : Equiv.Perm A, isotopyValue L ρ σ r c = s ↔ ρ r = u := by
      intro ρ
      change σ (L (ρ r) c) = s ↔ ρ r = u
      rw [← σ.apply_symm_apply s, σ.injective.eq_iff, ← hu, (hcol c).1.eq_iff]
    have h₂ : ∀ ρ : Equiv.Perm A, isotopyValue L ρ σ r' c' = s ↔ ρ r' = v := by
      intro ρ
      change σ (L (ρ r') c') = s ↔ ρ r' = v
      rw [← σ.apply_symm_apply s, σ.injective.eq_iff, ← hv, (hcol c').1.eq_iff]
    simp_rw [h₁, h₂]
    exact permutation_pair_indicator hrr huv
  rw [sum_congr rfl (fun σ _ => hh σ)]
  simp [sq]

end CDRBicolour.KBicolor.LatinPasch
