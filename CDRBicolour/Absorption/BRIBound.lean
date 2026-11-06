/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.BRIUniform

/-!
# The bound for the averaged gadgets

If every class has at least `m ≥ 3` points, every gadget pair set has at least `(m-1)²`
elements (`card_pairsF_ge`), and

  `|Φ₁ d T| ≤ 54 n ‖d‖ / (m-1)²`  (`abs_Phi1_le`).

Proof: `|gad u v w z T|` is at most the sum of the four triangle indicators; summing over all
quadruples `(u, v, w, z)` each indicator `[T = {x, y, z}]` contributes at most `27` (the three
named points lie in `T`) times `n` (the free point).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Bound

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

theorem card_class_erase (u : V) :
    #(univ.filter fun w => lab w = lab u ∧ w ≠ u) = csz lab (lab u) - 1 := by
  have : (univ.filter fun w => lab w = lab u ∧ w ≠ u) = (univ.filter fun w => lab w = lab u).erase u := by
    ext w; simp [and_comm]
  rw [this, card_erase_of_mem (by simp)]
  rfl

theorem card_pairsF_ge {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (u v : V) :
    (m - 1) * (m - 1) ≤ #(pairsF lab u v) := by
  unfold pairsF
  split_ifs with hl
  · rw [offDiag_card]
    have h := hm (lab u + 1)
    unfold csz at h
    set c := #(univ.filter fun w => lab w = lab u + 1)
    rw [← Nat.mul_sub_one]
    exact Nat.mul_le_mul (by omega) (by omega)
  · rw [card_product, card_class_erase, card_class_erase]
    exact Nat.mul_le_mul (by have := hm (lab u); omega) (by have := hm (lab v); omega)

theorem abs_indT_le (S T : Finset V) : |indT S T| = if T = S then 1 else 0 := by
  unfold indT; split_ifs <;> simp

theorem abs_gad_le (u v w z : V) (T : Finset V) :
    |gad u v w z T| ≤ (if T = {u, v, w} then 1 else 0) + (if T = {u, v, z} then 1 else 0) +
      (if T = {u, w, z} then 1 else 0) + (if T = {v, w, z} then 1 else 0) := by
  simp only [gad, Pi.sub_apply, Pi.add_apply]
  calc _ ≤ |indT {u, v, w} T| + |indT {u, v, z} T| + |indT {u, w, z} T| + |indT {v, w, z} T| := by
        have h1 := abs_sub (indT {u, v, w} T + indT {u, v, z} T - indT {u, w, z} T) (indT {v, w, z} T)
        have h2 := abs_sub (indT {u, v, w} T + indT {u, v, z} T) (indT {u, w, z} T)
        have h3 := abs_add_le (indT {u, v, w} T) (indT {u, v, z} T)
        linarith
    _ = _ := by rw [abs_indT_le, abs_indT_le, abs_indT_le, abs_indT_le]

/-- At most `27` ordered triples spell a given set. -/
theorem sum_triple_le (T : Finset V) :
    ∑ x : V, ∑ y : V, ∑ z : V, (if T = {x, y, z} then (1 : ℝ) else 0) ≤ 27 := by
  by_cases hT : T.card ≤ 3
  · have hle : ∀ x y z : V, (if T = {x, y, z} then (1 : ℝ) else 0) ≤
        (if x ∈ T then 1 else 0) * (if y ∈ T then 1 else 0) * (if z ∈ T then 1 else 0) := by
      intro x y z
      split_ifs with h <;> simp_all
    calc _ ≤ ∑ x : V, ∑ y : V, ∑ z : V, (if x ∈ T then (1 : ℝ) else 0) *
          (if y ∈ T then 1 else 0) * (if z ∈ T then 1 else 0) :=
          sum_le_sum fun x _ => sum_le_sum fun y _ => sum_le_sum fun z _ => hle x y z
      _ = (T.card : ℝ) ^ 3 := by
          have hc : ∑ x : V, (if x ∈ T then (1 : ℝ) else 0) = T.card := by
            rw [sum_boole]; congr 2; ext x; simp
          simp_rw [← mul_sum, ← sum_mul, hc]
          rw [← Finset.sum_mul_sum, hc]
          ring
      _ ≤ 27 := by
          have : (T.card : ℝ) ≤ 3 := by exact_mod_cast hT
          have h0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
          nlinarith [pow_le_pow_left₀ h0 this 3]
  · have : ∀ x y z : V, (if T = {x, y, z} then (1 : ℝ) else 0) = 0 := by
      intro x y z
      rw [if_neg]
      intro h
      apply hT
      rw [h]
      exact card_le_three
    simp [this]

theorem rep_injective : Function.Injective (rep : E0 V → V × V) := by
  intro e e' h
  apply Subtype.ext
  rw [← rep_spec e, ← rep_spec e', h]

/-- **Bound for the averaged-gadget operator.** -/
theorem abs_Phi1_le {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m) (d : E0 V → ℝ)
    (T : Finset V) :
    |Phi1 lab d T| ≤ 54 * Fintype.card V * ‖d‖ / ((m - 1 : ℝ) * (m - 1)) := by
  have hm1 : (0 : ℝ) < (m - 1 : ℝ) * (m - 1) := by
    have : (2 : ℝ) ≤ m - 1 := by
      have : (3 : ℝ) ≤ m := by exact_mod_cast h3
      linarith
    positivity
  set P : ℝ := (m - 1 : ℝ) * (m - 1)
  have hP : ∀ u v : V, P ≤ #(pairsF lab u v) := by
    intro u v
    have := card_pairsF_ge hm u v
    have h1 : 1 ≤ m := by omega
    have : ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) ≤ #(pairsF lab u v) := by exact_mod_cast this
    rwa [Nat.cast_sub h1, Nat.cast_one] at this
  -- the indicator sum of a gadget
  let I : V × V → V × V → ℝ := fun q p =>
    (if T = {q.1, q.2, p.1} then 1 else 0) + (if T = {q.1, q.2, p.2} then 1 else 0) +
      (if T = {q.1, p.1, p.2} then 1 else 0) + (if T = {q.2, p.1, p.2} then 1 else 0)
  have hI0 : ∀ q p, 0 ≤ I q p := fun q p => by simp only [I]; split_ifs <;> norm_num
  -- each averaged gadget
  have hgav : ∀ e : E0 V, |gav lab (rep e).1 (rep e).2 T| ≤ (1 / (2 * P)) * ∑ p : V × V, I (rep e) p := by
    intro e
    have hc : P ≤ #(pairsF lab (rep e).1 (rep e).2) := hP _ _
    have hpos : (0 : ℝ) < #(pairsF lab (rep e).1 (rep e).2) := lt_of_lt_of_le hm1 hc
    simp only [gav, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (2 * (#(pairsF lab (rep e).1 (rep e).2) : ℝ)) *
          |∑ p ∈ pairsF lab (rep e).1 (rep e).2, gad (rep e).1 (rep e).2 p.1 p.2 T|
        ≤ 1 / (2 * P) * ∑ p ∈ pairsF lab (rep e).1 (rep e).2, I (rep e) p := by
          apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
          · rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
          · exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => abs_gad_le _ _ _ _ T)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => hI0 _ p
  -- summing over edges
  have hsum : ∑ e : E0 V, ∑ p : V × V, I (rep e) p ≤ ∑ q : V × V, ∑ p : V × V, I q p := by
    rw [← sum_image (s := univ) (g := rep) (f := fun q => ∑ p : V × V, I q p)
      (fun e _ e' _ h => rep_injective h)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun q _ _ =>
      sum_nonneg fun p _ => hI0 q p
  have hcount : ∑ q : V × V, ∑ p : V × V, I q p ≤ 4 * 27 * Fintype.card V := by
    have h1 := sum_triple_le T
    simp only [I, Fintype.sum_prod_type, sum_add_distrib]
    have e1 : ∑ x : V, ∑ y : V, ∑ x_1 : V, ∑ _y_1 : V,
        (if T = {x, y, x_1} then (1 : ℝ) else 0) =
        Fintype.card V * ∑ x : V, ∑ y : V, ∑ z : V, (if T = {x, y, z} then (1 : ℝ) else 0) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_sum]
    have e2 : ∑ x : V, ∑ y : V, ∑ _x_1 : V, ∑ y_1 : V,
        (if T = {x, y, y_1} then (1 : ℝ) else 0) =
        Fintype.card V * ∑ x : V, ∑ y : V, ∑ z : V, (if T = {x, y, z} then (1 : ℝ) else 0) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_sum]
    have e3 : ∑ x : V, ∑ _y : V, ∑ x_1 : V, ∑ y_1 : V,
        (if T = {x, x_1, y_1} then (1 : ℝ) else 0) =
        Fintype.card V * ∑ x : V, ∑ y : V, ∑ z : V, (if T = {x, y, z} then (1 : ℝ) else 0) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_sum]
    have e4 : ∑ _x : V, ∑ y : V, ∑ x_1 : V, ∑ y_1 : V,
        (if T = {y, x_1, y_1} then (1 : ℝ) else 0) =
        Fintype.card V * ∑ x : V, ∑ y : V, ∑ z : V, (if T = {x, y, z} then (1 : ℝ) else 0) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [e1, e2, e3, e4]
    have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 hn]
  -- assemble
  simp only [Phi1, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ e : E0 V, d e * gav lab (rep e).1 (rep e).2 T|
      ≤ ∑ e : E0 V, |d e| * |gav lab (rep e).1 (rep e).2 T| := by
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ ≤ ∑ e : E0 V, ‖d‖ * ((1 / (2 * P)) * ∑ p : V × V, I (rep e) p) :=
        sum_le_sum fun e _ => mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d e)
          (hgav e) (abs_nonneg _) (norm_nonneg _)
    _ = ‖d‖ * (1 / (2 * P)) * ∑ e : E0 V, ∑ p : V × V, I (rep e) p := by
        rw [mul_assoc, mul_sum, mul_sum]
    _ ≤ ‖d‖ * (1 / (2 * P)) * (4 * 27 * Fintype.card V) :=
        mul_le_mul_of_nonneg_left (hsum.trans hcount) (by positivity)
    _ = 54 * Fintype.card V * ‖d‖ / P := by field_simp; ring

end Bound

end CDRBicolour.Absorption
