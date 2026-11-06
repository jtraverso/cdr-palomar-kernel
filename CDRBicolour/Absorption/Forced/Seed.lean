/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Host

/-!
# The forced-type host and its closed-form seed (backlog item 3, exact spectrum)

Role labels `Fin 4`: `0 = X₁`, `1 = X₂` (the two parts of the class `X`), `2 = Y`, `3 = Z`.
The allowed types `F4` are the bicoloured ones, except that an `XX` pair inside a part goes only
with `Y` and an `XX` pair across the parts only with `Z`:
`{0,0,2}, {1,1,2}, {0,1,3}, {0,2,2}, {1,2,2}, {0,3,3}, {1,3,3}, {2,2,3}, {2,3,3}`.
In every decomposition of this host the number of `XXY` triangles equals the number of `XX` edges
inside the parts — the exact count used for the spectrum.

`forced_edge_sum`: the closed-form type weights `fw` cover every pair exactly once (the `YZ`
equation is equivalent to the admissibility identity of `(|X|, |Y|, |Z|)`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Forced

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

/-- The allowed forced types. -/
def F4list : Finset (Multiset (Fin 4)) :=
  {{0, 0, 2}, {1, 1, 2}, {0, 1, 3}, {0, 2, 2}, {1, 2, 2}, {0, 3, 3}, {1, 3, 3}, {2, 2, 3},
    {2, 3, 3}}

/-- The allowed forced types, as a set. -/
def F4 : Set (Multiset (Fin 4)) := {m | m ∈ F4list}

/-- The closed-form weights (`p, q` the parts of `X`, `y = |Y|`, `z = |Z|`). -/
def fw (p q y z : ℝ) (m : Multiset (Fin 4)) : ℝ :=
  if m = {0, 0, 2} ∨ m = {1, 1, 2} then 1 / y
  else if m = {0, 1, 3} then 1 / z
  else if m = {0, 2, 2} then (y - p + 1) / (y * (y - 1))
  else if m = {1, 2, 2} then (y - q + 1) / (y * (y - 1))
  else if m = {0, 3, 3} then (z - q) / (z * (z - 1))
  else if m = {1, 3, 3} then (z - p) / (z * (z - 1))
  else if m = {2, 2, 3} then
    (1 - p * ((y - p + 1) / (y * (y - 1))) - q * ((y - q + 1) / (y * (y - 1)))) / z
  else if m = {2, 3, 3} then
    (1 - p * ((z - q) / (z * (z - 1))) - q * ((z - p) / (z * (z - 1)))) / y
  else 0

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Size of a role class. -/
def rsz (rl : V → Fin 4) (k : Fin 4) : ℕ := #(univ.filter fun v => rl v = k)

/-- The forced seed. -/
def fseed (rl : V → Fin 4) (T : Finset V) : ℝ :=
  fw (rsz rl 0) (rsz rl 1) (rsz rl 2) (rsz rl 3) (T.val.map rl)

/-- **The closed-form weights cover every pair exactly once.** -/
theorem forced_edge_sum (rl : V → Fin 4) (hy : 2 ≤ rsz rl 2) (hz : 2 ≤ rsz rl 3)
    (hadm : ((rsz rl 0 : ℝ) + rsz rl 1) ^ 2 + (rsz rl 2 : ℝ) ^ 2 + (rsz rl 3 : ℝ) ^ 2 -
      ((rsz rl 0 : ℝ) + rsz rl 1) * rsz rl 2 - ((rsz rl 0 : ℝ) + rsz rl 1) * rsz rl 3 -
      (rsz rl 2 : ℝ) * rsz rl 3 = (rsz rl 0 : ℝ) + rsz rl 1 + rsz rl 2 + rsz rl 3)
    {u v : V} (huv : u ≠ v) :
    ∑ T ∈ (allowed (⟨⊤, rl⟩ : Host V (Fin 4)) F4).filter (fun T => s(u, v) ∈ triEdges T),
      fseed rl T = 1 := by
  classical
  unfold fseed
  rw [edge_sum_top' rl F4 (fw (rsz rl 0) (rsz rl 1) (rsz rl 2) (rsz rl 3)) huv _
    (fun T => by rw [mem_filter])]
  rw [sum_by_label rl (fun k => ({rl u, rl v, k} : Multiset (Fin 4)) ∈ F4)
    (fun k => fw (rsz rl 0) (rsz rl 1) (rsz rl 2) (rsz rl 3) {rl u, rl v, k})]
  have hc : ∀ k, ((univ.filter fun z => z ≠ u ∧ z ≠ v ∧ rl z = k).card : ℝ) =
      (rsz rl k : ℝ) - (if rl u = k then 1 else 0) - (if rl v = k then 1 else 0) :=
    fun k => card_third rl huv k
  simp only [hc, Fin.sum_univ_four]
  have hy1 : (rsz rl 2 : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ rsz rl 2 := by exact_mod_cast hy
    intro h; linarith
  have hz1 : (rsz rl 3 : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ rsz rl 3 := by exact_mod_cast hz
    intro h; linarith
  have hy0 : (rsz rl 2 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ rsz rl 2 := by exact_mod_cast hy
    intro h; linarith
  have hz0 : (rsz rl 3 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ rsz rl 3 := by exact_mod_cast hz
    intro h; linarith
  generalize rsz rl 0 = p at hadm ⊢
  generalize rsz rl 1 = q at hadm ⊢
  generalize rsz rl 2 = y at hadm hy0 hy1 ⊢
  generalize rsz rl 3 = z at hadm hz0 hz1 ⊢
  generalize rl u = i
  generalize rl v = j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [F4, F4list, fw] <;>
    field_simp <;> ring_nf <;> nlinarith [hadm]

/-! ### Bounds -/

theorem frac_bounds {num den N : ℝ} (hN : 0 < N) (hden : 0 < den) (hlo : den ≤ 64 * N * num)
    (hhi : num * N ≤ 64 * den) : 1 / (64 * N) ≤ num / den ∧ num / den ≤ 64 / N := by
  constructor
  · rw [div_le_div_iff₀ (by positivity) hden]; linarith
  · rw [div_le_div_iff₀ hden hN]; linarith

theorem b_inv {Y N : ℝ} (hN : 0 < N) (hYN : Y ≤ N) (hY : N ≤ 4 * Y) :
    1 / (64 * N) ≤ 1 / Y ∧ 1 / Y ≤ 64 / N :=
  frac_bounds hN (by linarith) (by linarith) (by linarith)

theorem b_lin {Y N r : ℝ} (hN : 16 ≤ N) (hYN : Y ≤ N) (hY : N ≤ 4 * Y) (hr : 0 ≤ r)
    (h1 : N ≤ 16 * (Y - r)) :
    1 / (64 * N) ≤ (Y - r + 1) / (Y * (Y - 1)) ∧ (Y - r + 1) / (Y * (Y - 1)) ≤ 64 / N := by
  have hY1 : 1 ≤ Y - 1 := by linarith
  have a1 : Y * (Y - 1) ≤ N * N := mul_le_mul hYN (by linarith) (by linarith) (by linarith)
  have a2 : N * N ≤ 16 * N * (Y - r) := by
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ N); linarith
  have a3 : (Y - r + 1) * N ≤ (Y + 1) * (4 * Y) :=
    mul_le_mul (by linarith) hY (by linarith) (by linarith)
  have a4 : (Y + 1) * (4 * Y) ≤ 64 * (Y * (Y - 1)) := by nlinarith
  exact frac_bounds (by linarith) (mul_pos (by linarith) (by linarith)) (by nlinarith) (by linarith)

theorem b_lin' {Z N r : ℝ} (hN : 16 ≤ N) (hZN : Z ≤ N) (hZ : N ≤ 4 * Z) (hr : 0 ≤ r)
    (h1 : N ≤ 16 * (Z - r)) :
    1 / (64 * N) ≤ (Z - r) / (Z * (Z - 1)) ∧ (Z - r) / (Z * (Z - 1)) ≤ 64 / N := by
  have hZ1 : 1 ≤ Z - 1 := by linarith
  have a1 : Z * (Z - 1) ≤ N * N := mul_le_mul hZN (by linarith) (by linarith) (by linarith)
  have a2 : N * N ≤ 16 * N * (Z - r) := by
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ N); linarith
  have a3 : (Z - r) * N ≤ Z * (4 * Z) := mul_le_mul (by linarith) hZ (by linarith) (by linarith)
  have a4 : Z * (4 * Z) ≤ 64 * (Z * (Z - 1)) := by nlinarith
  exact frac_bounds (by linarith) (mul_pos (by linarith) (by linarith)) (by nlinarith) (by linarith)

theorem b_quad {Y Z N num : ℝ} (hN : 16 ≤ N) (hYN : Y ≤ N) (hZN : Z ≤ N) (hY : N ≤ 4 * Y)
    (hZ : N ≤ 4 * Z) (hlo : N ^ 2 ≤ 64 * num) (hhi : num ≤ Y * (Y - 1)) :
    1 / (64 * N) ≤ num / (Y * (Y - 1) * Z) ∧ num / (Y * (Y - 1) * Z) ≤ 64 / N := by
  have hY1 : 1 ≤ Y - 1 := by linarith
  have a1 : Y * (Y - 1) ≤ N * N := mul_le_mul hYN (by linarith) (by linarith) (by linarith)
  have a2 : Y * (Y - 1) * Z ≤ N * N * N := mul_le_mul a1 hZN (by linarith) (mul_self_nonneg N)
  have a3 : N * N * N ≤ 64 * N * num := by
    have := mul_le_mul_of_nonneg_left hlo (by linarith : (0 : ℝ) ≤ N); nlinarith
  have a4 : num * N ≤ Y * (Y - 1) * (4 * Z) :=
    mul_le_mul hhi hZ (by linarith) (mul_pos (by linarith) (by linarith)).le
  exact frac_bounds (by linarith) (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
    (by linarith) (by nlinarith)

/-- **Diffuseness of the closed-form weights** (`C = 64`), under explicit size conditions. -/
theorem fw_bounds {P Q Y Z N : ℝ} (hN : 64 ≤ N) (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hYN : Y ≤ N) (hZN : Z ≤ N) (hY : N ≤ 4 * Y) (hZ : N ≤ 4 * Z)
    (h1 : N ≤ 16 * (Y - P)) (h2 : N ≤ 16 * (Y - Q)) (h3 : N ≤ 16 * (Z - Q))
    (h4 : N ≤ 16 * (Z - P))
    (h5 : N ^ 2 ≤ 64 * (Y ^ 2 - Y - (P + Q) * Y - (P + Q) + P ^ 2 + Q ^ 2))
    (h6 : N ^ 2 ≤ 64 * (Z ^ 2 - Z - (P + Q) * Z + 2 * P * Q))
    {m : Multiset (Fin 4)} (hm : m ∈ F4) :
    1 / (64 * N) ≤ fw P Q Y Z m ∧ fw P Q Y Z m ≤ 64 / N := by
  have hN0 : 0 < N := by linarith
  have hN16 : 16 ≤ N := by linarith
  simp only [F4, F4list, Set.mem_ofPred_eq, mem_insert, mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp (config := { decide := true }) only [fw, true_or, if_true]; exact b_inv hN0 hYN hY
  · simp (config := { decide := true }) only [fw, or_true, if_true]; exact b_inv hN0 hYN hY
  · simp (config := { decide := true }) only [fw, if_true, if_false, or_self]
    exact b_inv hN0 hZN hZ
  · simp (config := { decide := true }) only [fw, if_true, if_false, or_self]
    exact b_lin hN16 hYN hY hP h1
  · simp (config := { decide := true }) only [fw, if_true, if_false, or_self]
    exact b_lin hN16 hYN hY hQ h2
  · simp (config := { decide := true }) only [fw, if_true, if_false, or_self]
    exact b_lin' hN16 hZN hZ hQ h3
  · simp (config := { decide := true }) only [fw, if_true, if_false, or_self]
    exact b_lin' hN16 hZN hZ hP h4
  · simp (config := { decide := true }) only [fw, if_true, if_false, or_self]
    have hY1 : 0 < Y - 1 := by linarith
    have e : (1 - P * ((Y - P + 1) / (Y * (Y - 1))) - Q * ((Y - Q + 1) / (Y * (Y - 1)))) / Z =
        (Y ^ 2 - Y - (P + Q) * Y - (P + Q) + P ^ 2 + Q ^ 2) / (Y * (Y - 1) * Z) := by
      have : Y ≠ 0 := by linarith
      have : Y - 1 ≠ 0 := by linarith
      have : Z ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    have q1 : 0 ≤ P * (Y - P + 1) := mul_nonneg hP (by linarith)
    have q2 : 0 ≤ Q * (Y - Q + 1) := mul_nonneg hQ (by linarith)
    exact b_quad hN16 hYN hZN hY hZ h5 (by nlinarith)
  · simp (config := { decide := true }) only [fw, if_true, if_false, or_self]
    have e : (1 - P * ((Z - Q) / (Z * (Z - 1))) - Q * ((Z - P) / (Z * (Z - 1)))) / Y =
        (Z ^ 2 - Z - (P + Q) * Z + 2 * P * Q) / (Z * (Z - 1) * Y) := by
      have : Y ≠ 0 := by linarith
      have : Z - 1 ≠ 0 := by linarith
      have : Z ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    have q1 : 0 ≤ P * (Z - Q) := mul_nonneg hP (by linarith)
    have q2 : 0 ≤ Q * (Z - P) := mul_nonneg hQ (by linarith)
    exact b_quad hN16 hZN hYN hZ hY h6 (by nlinarith)

end CDRBicolour.Absorption.Forced