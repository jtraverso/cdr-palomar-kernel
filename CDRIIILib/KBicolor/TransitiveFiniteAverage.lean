/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.FiniteSymmetrization
public import Mathlib.Data.Fintype.Perm

/-! # Uniform finite averages on transitive permutation orbits

All identities are finite sums, without probability axioms. They supply
the one-point and distinct-two-point probabilities needed for Latin isotopies.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset CDRBicolour.KBicolor.Symmetrization

section Group
variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]

theorem orbit_sum_constant (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (x y : X) : (∑ g : G, w (g • x)) = ∑ g : G, w (g • y) := by
  obtain ⟨h, hh⟩ := htrans x y
  rw [← hh]
  simp_rw [← mul_smul]
  exact (Equiv.sum_comp (rightEquiv h) (fun g : G => w (g • x))).symm

/-- A transitive orbit average is the uniform average of its points. -/
theorem transitive_weight_sum (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (x : X) :
    (Fintype.card X : ℝ) * (∑ g : G, w (g • x)) =
      (Fintype.card G : ℝ) * (∑ y : X, w y) := by
  calc
    _ = ∑ _y : X, ∑ g : G, w (g • x) := by simp
    _ = ∑ y : X, ∑ g : G, w (g • y) := by
      apply sum_congr rfl
      intro y _
      exact orbit_sum_constant htrans w x y
    _ = ∑ g : G, ∑ y : X, w (g • y) := sum_comm
    _ = ∑ _g : G, ∑ y : X, w y := by
      apply sum_congr rfl
      intro g _
      exact Equiv.sum_comp (actionEquiv g) w
    _ = _ := by simp

theorem exists_cost_le_of_sum_le (cost : G → ℝ) (B : ℝ)
    (h : (∑ g, cost g) ≤ (Fintype.card G : ℝ)*B) : ∃ g : G, cost g ≤ B := by
  classical
  obtain ⟨g, _, hmin⟩ := (univ : Finset G).exists_min_image cost ⟨1, mem_univ _⟩
  refine ⟨g, ?_⟩
  have hlow : (Fintype.card G : ℝ)*cost g ≤ ∑ a : G, cost a := by
    calc
      _ = ∑ _a : G, cost g := by simp
      _ ≤ _ := sum_le_sum (fun a ha => hmin a ha)
  have hpos := group_card_pos (G := G)
  nlinarith

end Group

section Permutations
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem exists_perm_map_two {a b c d : A} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ e : Equiv.Perm A, e a = c ∧ e b = d := by
  let e₁ := Equiv.swap a c
  have ha : e₁ a = c := Equiv.swap_apply_left a c
  have hbc : e₁ b ≠ c := by rw [← ha]; exact e₁.injective.ne hab.symm
  let e₂ := Equiv.swap (e₁ b) d
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · change e₂ (e₁ a) = c
    rw [ha]
    exact Equiv.swap_apply_of_ne_of_ne hbc.symm hcd
  · exact Equiv.swap_apply_left _ _

def distinctPairAction : MulAction (Equiv.Perm A) {p : A × A // p.1 ≠ p.2} where
  smul e p := ⟨(e p.1.1, e p.1.2), e.injective.ne p.2⟩
  one_smul p := by apply Subtype.ext; rfl
  mul_smul e f p := by apply Subtype.ext; rfl

theorem distinctPair_card : Fintype.card {p : A × A // p.1 ≠ p.2} =
    Fintype.card A * (Fintype.card A - 1) := by
  let e : {p : A × A // p.1 ≠ p.2} ≃ ↥((univ : Finset A).offDiag) :=
    { toFun := fun p => ⟨p.val, by simp [p.property]⟩
      invFun := fun p => ⟨p.val, (mem_offDiag.mp p.property).2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, offDiag_card, card_univ]
  simp [Nat.mul_sub_left_distrib]

theorem permutation_point_weight_sum (x : A) (w : A → ℝ) :
    (Fintype.card A : ℝ) * (∑ e : Equiv.Perm A, w (e x)) =
      (Fintype.card (Equiv.Perm A) : ℝ) * ∑ y : A, w y := by
  apply transitive_weight_sum (G := Equiv.Perm A)
  intro a b
  exact ⟨Equiv.swap a b, Equiv.swap_apply_left a b⟩

theorem permutation_pair_weight_sum (x : {p : A × A // p.1 ≠ p.2})
    (w : {p : A × A // p.1 ≠ p.2} → ℝ) :
    (Fintype.card A * (Fintype.card A - 1) : ℕ) *
        (∑ e : Equiv.Perm A, w ⟨(e x.1.1, e x.1.2), e.injective.ne x.2⟩) =
      (Fintype.card (Equiv.Perm A) : ℝ) * ∑ y, w y := by
  letI := distinctPairAction (A := A)
  have htrans : ∀ a b : {p : A × A // p.1 ≠ p.2}, ∃ e : Equiv.Perm A, e • a = b := by
    intro a b
    obtain ⟨e, he₁, he₂⟩ := exists_perm_map_two a.2 b.2
    exact ⟨e, Subtype.ext (Prod.ext he₁ he₂)⟩
  have hh := transitive_weight_sum htrans w x
  rw [distinctPair_card] at hh
  exact hh

theorem permutation_point_indicator (x y : A) :
    (Fintype.card A : ℝ) *
        (∑ e : Equiv.Perm A, if e x = y then (1 : ℝ) else 0) =
      Fintype.card (Equiv.Perm A) := by
  simpa using permutation_point_weight_sum x (fun z => if z = y then (1 : ℝ) else 0)

theorem permutation_pair_indicator {x₁ x₂ y₁ y₂ : A} (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) :
    (Fintype.card A * (Fintype.card A - 1) : ℕ) *
        (∑ e : Equiv.Perm A, if e x₁ = y₁ ∧ e x₂ = y₂ then (1 : ℝ) else 0) =
      Fintype.card (Equiv.Perm A) := by
  simpa only [Subtype.mk.injEq, Prod.mk.injEq, sum_ite_eq', mem_univ, if_true,
    mul_one] using permutation_pair_weight_sum ⟨(x₁, x₂), hx⟩
      (fun z => if z = ⟨(y₁, y₂), hy⟩ then (1 : ℝ) else 0)

end Permutations
end CDRBicolour.KBicolor.LatinPasch
