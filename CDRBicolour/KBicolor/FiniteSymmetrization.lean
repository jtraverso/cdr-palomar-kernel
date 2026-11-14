/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

/-! # Finite averaging of a signed replacement matrix

The average is defined explicitly. Column bounds and incidence identities
are preserved. Its row masses are constant on output orbits, which turns
a lower bound on orbit size into a uniform supremum bound.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Symmetrization

open Finset

variable {G X Y Z : Type*} [Group G] [Fintype G]
  [Fintype X] [Fintype Y] [MulAction G X] [MulAction G Y]

def actionEquiv (g : G) : X ≃ X where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp

def rightEquiv (h : G) : G ≃ G where
  toFun g := g*h
  invFun g := g*h⁻¹
  left_inv g := by simp [mul_assoc]
  right_inv g := by simp [mul_assoc]

theorem group_card_pos : (0:ℝ) < Fintype.card G := by
  letI : Nonempty G := ⟨1⟩
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)

def average (G : Type*) [Group G] [Fintype G] [MulAction G X] [MulAction G Y]
    (A : Y → X → ℝ) (y : Y) (x : X) : ℝ :=
  (∑ g : G, A (g • y) (g • x)) / Fintype.card G

theorem average_equivariant (A : Y → X → ℝ) (h : G) (y : Y) (x : X) :
    average G A (h • y) (h • x) = average G A y x := by
  unfold average
  congr 1
  simp_rw [← mul_smul]
  exact (rightEquiv h).sum_comp (fun g => A (g • y) (g • x))

theorem average_column_bound (A : Y → X → ℝ) {L : ℝ}
    (hcol : ∀ x, ∑ y, |A y x| ≤ L) (x : X) :
    ∑ y, |average G A y x| ≤ L := by
  have hc := group_card_pos (G := G)
  have hbound : ∀ g : G, ∑ y, |A (g • y) (g • x)| ≤ L := by
    intro g
    calc ∑ y, |A (g • y) (g • x)| = ∑ y, |A y (g • x)| :=
          (actionEquiv g).sum_comp (fun y => |A y (g • x)|)
      _ ≤ L := hcol (g • x)
  calc ∑ y, |average G A y x|
      ≤ ∑ y, (∑ g : G, |A (g • y) (g • x)|) / Fintype.card G := by
        apply sum_le_sum
        intro y _
        rw [average, abs_div, abs_of_pos hc]
        exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
    _ = (∑ g : G, ∑ y, |A (g • y) (g • x)|) / Fintype.card G := by
        rw [← sum_div, sum_comm]
    _ ≤ (∑ _g : G, L) / Fintype.card G :=
        div_le_div_of_nonneg_right (sum_le_sum fun g _ => hbound g) hc.le
    _ = L := by
        rw [sum_const, nsmul_eq_mul, card_univ]
        field_simp

def rowMass (A : Y → X → ℝ) (y : Y) : ℝ := ∑ x, |A y x|

theorem rowMass_nonneg (A : Y → X → ℝ) (y : Y) : 0 ≤ rowMass A y :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem average_row_invariant (A : Y → X → ℝ) (g : G) (y : Y) :
    rowMass (average G A) (g • y) = rowMass (average G A) y := by
  unfold rowMass
  calc ∑ x, |average G A (g • y) x|
      = ∑ x, |average G A (g • y) (g • x)| :=
        ((actionEquiv g).sum_comp (fun x => |average G A (g • y) x|)).symm
    _ = ∑ x, |average G A y x| := by
        apply sum_congr rfl
        intro x _
        rw [average_equivariant]

theorem orbit_row_bound [DecidableEq Y] (A : Y → X → ℝ) {L : ℝ}
    (hcol : ∀ x, ∑ y, |A y x| ≤ L) (O : Finset Y) (y : Y)
    (hrow : ∀ z ∈ O, rowMass A z = rowMass A y) :
    (O.card:ℝ)*rowMass A y ≤ (Fintype.card X:ℝ)*L := by
  calc (O.card:ℝ)*rowMass A y = ∑ z ∈ O, rowMass A z := by
        calc (O.card:ℝ)*rowMass A y = ∑ _z ∈ O, rowMass A y := by
              rw [sum_const, nsmul_eq_mul]
          _ = ∑ z ∈ O, rowMass A z := sum_congr rfl fun z hz => (hrow z hz).symm
    _ = ∑ x, ∑ z ∈ O, |A z x| := by
        unfold rowMass
        rw [sum_comm]
    _ ≤ ∑ x, L := by
        apply sum_le_sum
        intro x _
        exact (sum_le_univ_sum_of_nonneg (fun z => abs_nonneg (A z x))).trans (hcol x)
    _ = (Fintype.card X:ℝ)*L := by rw [sum_const, nsmul_eq_mul, card_univ]

theorem average_incidence [Fintype Z] [MulAction G Z]
    (A : Y → X → ℝ) (D : Z → X → ℝ) (E : Z → Y → ℝ)
    (hD : ∀ (g : G) z x, D (g • z) (g • x) = D z x)
    (hE : ∀ (g : G) z y, E (g • z) (g • y) = E z y)
    (hinc : ∀ z x, ∑ y, E z y * A y x = D z x) (z : Z) (x : X) :
    ∑ y, E z y * average G A y x = D z x := by
  have hc := group_card_pos (G := G)
  have hg : ∀ g : G, ∑ y, E z y * A (g • y) (g • x) = D z x := by
    intro g
    calc ∑ y, E z y * A (g • y) (g • x)
        = ∑ y, E (g • z) (g • y) * A (g • y) (g • x) := by simp_rw [hE]
      _ = ∑ y, E (g • z) y * A y (g • x) :=
          (actionEquiv g).sum_comp (fun y => E (g • z) y * A y (g • x))
      _ = D (g • z) (g • x) := hinc _ _
      _ = D z x := hD _ _ _
  simp only [average, ← mul_div_assoc, mul_sum]
  rw [← sum_div, sum_comm]
  simp_rw [hg]
  rw [sum_const, nsmul_eq_mul, card_univ]
  field_simp

def kernelMap (A : Y → X → ℝ) : (X → ℝ) →ₗ[ℝ] (Y → ℝ) where
  toFun f y := ∑ x, A y x * f x
  map_add' f g := by ext y; simp [mul_add, sum_add_distrib]
  map_smul' c f := by ext y; simp [mul_sum, mul_left_comm]

theorem kernelMap_bound (A : Y → X → ℝ) {b : ℝ}
    {f : X → ℝ} (hf : ∀ x, |f x| ≤ b) (y : Y) :
    |kernelMap A f y| ≤ rowMass A y*b := by
  calc |kernelMap A f y| ≤ ∑ x, |A y x * f x| := abs_sum_le_sum_abs _ _
    _ = ∑ x, |A y x| * |f x| := by simp_rw [abs_mul]
    _ ≤ ∑ x, |A y x| * b := sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = rowMass A y*b := by rw [rowMass, sum_mul]

/-- The numerical row estimate used for triangle orbits of size at least m³/4. -/
theorem cubic_row_bound [DecidableEq Y] (A : Y → X → ℝ)
    (O : Finset Y) (y : Y) {N m R : ℝ}
    (hN : 0 ≤ N) (hm : 0 < m) (hR : 0 ≤ R) (hsize : (Fintype.card X:ℝ) ≤ N^3)
    (hratio : N ≤ R*m) (horbit : m^3 ≤ 4*(O.card:ℝ))
    (hcol : ∀ x, ∑ z, |A z x| ≤ 25)
    (hrow : ∀ z ∈ O, rowMass A z = rowMass A y) :
    rowMass A y ≤ 100*R^3 := by
  have htotal := orbit_row_bound A hcol O y hrow
  have hpow : N^3 ≤ R^3*m^3 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hN hratio 3
  have hsum : m^3*rowMass A y ≤ 100*(R^3*m^3) := by
    calc m^3*rowMass A y ≤ (4*(O.card:ℝ))*rowMass A y :=
          mul_le_mul_of_nonneg_right horbit (rowMass_nonneg A y)
      _ ≤ 4*((Fintype.card X:ℝ)*25) := by nlinarith only [htotal]
      _ ≤ 100*N^3 := by nlinarith only [hsize]
      _ ≤ 100*(R^3*m^3) := mul_le_mul_of_nonneg_left hpow (by norm_num)
  by_contra hbad
  have hpositive : 0 < m^3*(rowMass A y-100*R^3) :=
    mul_pos (pow_pos hm 3) (by linarith)
  nlinarith only [hsum, hpositive]

open Classical in
def orbitSet (G : Type*) [Group G] [Fintype G] [MulAction G Y] (y : Y) : Finset Y :=
  univ.image (fun g : G => g • y)

theorem average_cubic_bound (A : Y → X → ℝ) (y : Y) {N m R : ℝ}
    (hN : 0 ≤ N) (hm : 0 < m) (hR : 0 ≤ R) (hsize : (Fintype.card X:ℝ) ≤ N^3)
    (hratio : N ≤ R*m) (horbit : m^3 ≤ 4*((orbitSet G y).card:ℝ))
    (hcol : ∀ x, ∑ z, |A z x| ≤ 25) :
    rowMass (average G A) y ≤ 100*R^3 := by
  classical
  apply cubic_row_bound (average G A) (orbitSet G y) y hN hm hR hsize hratio horbit
    (average_column_bound A hcol)
  intro z hz
  obtain ⟨g, _, rfl⟩ := mem_image.mp hz
  exact average_row_invariant A g y

theorem averaged_kernel_bound (A : Y → X → ℝ) (y : Y) {N m R b : ℝ}
    (hN : 0 ≤ N) (hm : 0 < m) (hR : 0 ≤ R) (hsize : (Fintype.card X:ℝ) ≤ N^3)
    (hratio : N ≤ R*m) (horbit : m^3 ≤ 4*((orbitSet G y).card:ℝ))
    (hcol : ∀ x, ∑ z, |A z x| ≤ 25) (hb : 0 ≤ b)
    {f : X → ℝ} (hf : ∀ x, |f x| ≤ b) :
    |kernelMap (average G A) f y| ≤ (100*R^3)*b :=
  (kernelMap_bound _ hf y).trans (mul_le_mul_of_nonneg_right
    (average_cubic_bound A y hN hm hR hsize hratio horbit hcol) hb)

end CDRBicolour.KBicolor.Symmetrization
