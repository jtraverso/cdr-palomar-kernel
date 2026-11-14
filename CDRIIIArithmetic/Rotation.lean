/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Reduction
public import FourSquaresCaps.FourSquaresDenseProof

/-!
# Quaternion rotations from four squares in caps

`FourSquaresDense`: for every unit vector `q ∈ ℝ⁴` and `δ > 0`, every large odd `m` is the norm of
an integer quaternion `β` with `|βᵢ − √m qᵢ| ≤ δ √m`.

`quaternionRotationsDense_of`: `FourSquaresDense → QuaternionRotationsDense`. For unit vectors
`y, u ∈ ℝ³` there is a unit quaternion `q` whose rotation takes `y` to `u` (`exists_rotR_eq`); the
rotation of `β / √m` is `rot β / m`, and it depends continuously on the quaternion.
-/

@[expose] public section

namespace ThreeSquares

open Matrix

/-- The rotation matrix of a real quaternion (multiplied by its squared norm). -/
def rotR (q : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q 0 ^ 2 + q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2, 2 * (q 1 * q 2 - q 0 * q 3),
      2 * (q 1 * q 3 + q 0 * q 2);
    2 * (q 1 * q 2 + q 0 * q 3), q 0 ^ 2 - q 1 ^ 2 + q 2 ^ 2 - q 3 ^ 2,
      2 * (q 2 * q 3 - q 0 * q 1);
    2 * (q 1 * q 3 - q 0 * q 2), 2 * (q 2 * q 3 + q 0 * q 1),
      q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 + q 3 ^ 2]

/-- The registered four-square cap contract, with no added assumption. -/
abbrev FourSquaresDense := FourSquaresCaps.FourSquaresDense

theorem rot_map_eq (β : Fin 4 → ℤ) :
    (rot β).map (Int.cast : ℤ → ℝ) = rotR (fun i => (β i : ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, rotR]

/-- `rotR` is homogeneous of degree two. -/
theorem rotR_smul (c : ℝ) (q : Fin 4 → ℝ) : rotR (c • q) = c ^ 2 • rotR q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotR] <;> ring

/-- The unnormalized half-turn quaternion `(1 + y·u, y × u)` takes `y` to `2 (1 + y·u) u`. -/
theorem rotR_cross_mulVec {y u : Fin 3 → ℝ} (hy : ∑ i, y i ^ 2 = 1) (hu : ∑ i, u i ^ 2 = 1) :
    rotR ![1 + ∑ i, y i * u i, y 1 * u 2 - y 2 * u 1, y 2 * u 0 - y 0 * u 2,
      y 0 * u 1 - y 1 * u 0] *ᵥ y = (2 * (1 + ∑ i, y i * u i)) • u := by
  simp only [Fin.sum_univ_three] at hy hu ⊢
  ext i
  fin_cases i <;> simp [rotR, mulVec, dotProduct, Fin.sum_univ_three]
  · linear_combination (-(y 0) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) +
      2 * (1 + (y 0 * u 0 + y 1 * u 1 + y 2 * u 2)) * u 0) * hy + (-(y 0)) * hu
  · linear_combination (-(y 1) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) +
      2 * (1 + (y 0 * u 0 + y 1 * u 1 + y 2 * u 2)) * u 1) * hy + (-(y 1)) * hu
  · linear_combination (-(y 2) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) +
      2 * (1 + (y 0 * u 0 + y 1 * u 1 + y 2 * u 2)) * u 2) * hy + (-(y 2)) * hu

/-- A pure unit quaternion orthogonal to `y` turns `y` into `−y`. -/
theorem rotR_pure_mulVec {y n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) (hny : ∑ i, n i * y i = 0) :
    rotR ![0, n 0, n 1, n 2] *ᵥ y = -y := by
  simp only [Fin.sum_univ_three] at hn hny
  ext i
  fin_cases i <;> simp [rotR, mulVec, dotProduct, Fin.sum_univ_three]
  · linear_combination (-(y 0)) * hn + 2 * n 0 * hny
  · linear_combination (-(y 1)) * hn + 2 * n 1 * hny
  · linear_combination (-(y 2)) * hn + 2 * n 2 * hny

set_option maxHeartbeats 4000000 in
-- the two cases and the normalizations exceed the default heartbeat budget
/-- **A rotation taking `y` to `u`.** -/
theorem exists_rotR_eq {y u : Fin 3 → ℝ} (hy : ∑ i, y i ^ 2 = 1) (hu : ∑ i, u i ^ 2 = 1) :
    ∃ q : Fin 4 → ℝ, ∑ i, q i ^ 2 = 1 ∧ rotR q *ᵥ y = u := by
  set s := 1 + ∑ i, y i * u i with hs_def
  have hsum : ∑ i, (u i + y i) ^ 2 = 2 * s := by
    simp only [Fin.sum_univ_three, hs_def] at hy hu ⊢
    linear_combination hu + hy
  have hs0 : 0 ≤ s := by
    have : 0 ≤ ∑ i, (u i + y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  rcases hs0.lt_or_eq with hs | hs
  · -- `u ≠ −y`: the normalized half-turn quaternion
    set c := Real.sqrt (2 * s)
    have hc : c ^ 2 = 2 * s := Real.sq_sqrt (by positivity)
    have hc0 : c ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    set w : Fin 4 → ℝ := ![1 + ∑ i, y i * u i, y 1 * u 2 - y 2 * u 1, y 2 * u 0 - y 0 * u 2,
      y 0 * u 1 - y 1 * u 0] with hw
    have hwnorm : ∑ i, w i ^ 2 = 2 * s := by
      simp only [Fin.sum_univ_three] at hy hu
      simp [hw, Fin.sum_univ_four, Fin.sum_univ_three, hs_def]
      linear_combination (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * hy + hu
    refine ⟨c⁻¹ • w, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hwnorm, inv_pow, hc]
      field_simp
    · rw [rotR_smul, smul_mulVec, rotR_cross_mulVec hy hu, ← hs_def, smul_smul, inv_pow, hc]
      rw [inv_mul_cancel₀ (by positivity), one_smul]
  · -- `u = −y`: a pure quaternion orthogonal to `y`
    have huy : ∀ i, u i = -y i := by
      intro i
      have h0 : ∑ j, (u j + y j) ^ 2 = 0 := by rw [hsum, ← hs]; ring
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (u j + y j))).mp h0 i
        (Finset.mem_univ i)
      linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this]
    -- some coordinate of `y` has square less than one
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, y k ^ 2 < 1 := by
      by_contra h
      push Not at h
      simp only [Fin.sum_univ_three] at hy
      have h0 := h 0; have h1 := h 1; have h2 := h 2
      nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]
    -- the cross product of `y` with the `k`-th basis vector
    set v : Fin 3 → ℝ := ![y 1 * (if k = 2 then 1 else 0) - y 2 * (if k = 1 then 1 else 0),
      y 2 * (if k = 0 then 1 else 0) - y 0 * (if k = 2 then 1 else 0),
      y 0 * (if k = 1 then 1 else 0) - y 1 * (if k = 0 then 1 else 0)] with hv
    have hvnorm : ∑ i, v i ^ 2 = 1 - y k ^ 2 := by
      simp only [Fin.sum_univ_three] at hy
      fin_cases k <;> simp [hv, Fin.sum_univ_three] <;> linear_combination hy
    have hvy : ∑ i, v i * y i = 0 := by
      fin_cases k <;> simp [hv, Fin.sum_univ_three] <;> ring
    set e := Real.sqrt (1 - y k ^ 2)
    have he : e ^ 2 = 1 - y k ^ 2 := Real.sq_sqrt (by linarith)
    have he0 : e ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    set n : Fin 3 → ℝ := e⁻¹ • v
    have hk' : 1 - y k ^ 2 ≠ 0 := by linarith
    have hn : ∑ i, n i ^ 2 = 1 := by
      simp only [n, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hvnorm, inv_pow, he]
      field_simp
    have hny : ∑ i, n i * y i = 0 := by
      simp only [n, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hvy, mul_zero]
    refine ⟨![0, n 0, n 1, n 2], ?_, ?_⟩
    · simp only [Fin.sum_univ_three] at hn
      simp [Fin.sum_univ_four]
      linear_combination hn
    · rw [rotR_pure_mulVec hn hny]
      ext i
      simp [huy i]

theorem continuous_rotR_mulVec (y : Fin 3 → ℝ) : Continuous fun q : Fin 4 → ℝ => rotR q *ᵥ y := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [rotR, mulVec, dotProduct, Fin.sum_univ_three] <;> simp <;> fun_prop

/-- **Rotations from four squares in caps.** -/
theorem quaternionRotationsDense_of (h : FourSquaresDense) : QuaternionRotationsDense := by
  intro y u hy hu ε hε
  obtain ⟨q, hq, hqu⟩ := exists_rotR_eq hy hu
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp (continuous_rotR_mulVec y) q ε hε
  obtain ⟨M₀, hM₀⟩ := h q hq (δ / 2) (by positivity)
  refine ⟨M₀ + 1, fun m hm hodd => ?_⟩
  obtain ⟨β, hβ, hβq⟩ := hM₀ m (by omega) hodd
  refine ⟨β, hβ, fun i => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsq0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  set p : Fin 4 → ℝ := fun j => (β j : ℝ) / Real.sqrt m
  have hβp : (fun j => (β j : ℝ)) = Real.sqrt m • p := by
    ext j; simp [p]; field_simp
  have hp : dist p q < δ := by
    rw [dist_pi_lt_iff hδ]
    intro j
    rw [Real.dist_eq]
    have h1 := hβq j
    have : p j - q j = ((β j : ℝ) - Real.sqrt m * q j) / Real.sqrt m := by
      simp only [p]; field_simp
    rw [this, abs_div, abs_of_pos hsq0, div_lt_iff₀ hsq0]
    have := mul_pos hδ hsq0
    linarith
  have hclose := hδε p hp
  rw [dist_pi_lt_iff hε] at hclose
  have hi := hclose i
  rw [Real.dist_eq, hqu] at hi
  have hrot : ((rot β).map (Int.cast : ℤ → ℝ) *ᵥ y) i / m = (rotR p *ᵥ y) i := by
    rw [rot_map_eq, hβp, rotR_smul, smul_mulVec, Real.sq_sqrt hm0.le, Pi.smul_apply,
      smul_eq_mul]
    field_simp
  rw [hrot]
  exact hi.le

end ThreeSquares
