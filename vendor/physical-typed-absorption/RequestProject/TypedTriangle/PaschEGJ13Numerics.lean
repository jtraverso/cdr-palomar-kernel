module
public import RequestProject.Pseudorandom.Eventually12
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace TypedTriangle.Pasch

/-- The exponent for delta=1/4, tuple order at most four and the actual
four-uniform packet hypergraph (three graph edges and one private tag). -/
def egj13Epsilon : ℝ := 1/51200

private theorem eventually_square_conditions (C c ε D0 : ℝ) (q : ℕ)
    (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ n : ℝ in atTop,
      1 ≤ n ∧ 1 ≤ n^2 ∧ D0 ≤ n^2 ∧ C*n ≤ (n^2)^(3/4 : ℝ) ∧
      n^4 ≤ Real.exp ((n^2)^(egj13Epsilon^2)) ∧
      n^q ≤ Real.exp ((n^2)^(egj13Epsilon^2)) ∧
      (n^2)^(-egj13Epsilon) ≤ ε ∧ 2*C ≤ n ∧ 32*C^3 ≤ c*n ∧ C/n ≤ ε := by
  have he : 0 < egj13Epsilon := by norm_num [egj13Epsilon]
  have hExp : 0 < 2*egj13Epsilon^2 := by positivity
  have hSmall := Pseudorandom.eventually_rpow_le_mul_rpow
    (σ := -(2*egj13Epsilon)) (γ := 0) (c := ε) (by linarith only [he]) hε
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2*C),eventually_ge_atTop (32*C^3/c),
    eventually_ge_atTop (C/ε),
    Pseudorandom.eventually_const_le_rpow (by norm_num : (0 : ℝ) < 2) D0,
    Pseudorandom.eventually_const_le_rpow (by norm_num : (0 : ℝ) < 1/2) C,
    Pseudorandom.eventually_mul_log_le_rpow hExp 4,
    Pseudorandom.eventually_mul_log_le_rpow hExp (q : ℝ),hSmall]
    with n hn h2C hScale hRatio hD hCodegree hLog4 hLogq hError
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hN2 : 1 ≤ n^2 := one_le_pow₀ hn
  have hSquareExp : (n^2)^(egj13Epsilon^2) = n^(2*egj13Epsilon^2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hErrorEq : (n^2)^(-egj13Epsilon) = n^(-(2*egj13Epsilon)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hPowerExp (k : ℕ) (hk : (k : ℝ)*Real.log n ≤ n^(2*egj13Epsilon^2)) :
      n^k ≤ Real.exp ((n^2)^(egj13Epsilon^2)) := by
    rw [hSquareExp]
    have hh := Real.exp_le_exp.mpr hk
    simpa only [← Real.log_pow,Real.exp_log (pow_pos hn0 k)] using hh
  refine ⟨hn,hN2,?_,?_,hPowerExp 4 hLog4,hPowerExp q hLogq,?_,h2C,?_,?_⟩
  · simpa only [Real.rpow_two] using hD
  · have hh := mul_le_mul_of_nonneg_right hCodegree hn0.le
    calc
      C*n ≤ n^(1/2 : ℝ)*n := hh
      _ = (n^2)^(3/4 : ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
        norm_num only [Nat.cast_ofNat]
        rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
          Real.rpow_add hn0,Real.rpow_one]
  · rw [hErrorEq]
    simpa only [Real.rpow_zero,mul_one] using hError
  · have hh := (div_le_iff₀ hc).mp hScale
    simpa only [mul_comm] using hh
  · apply (div_le_iff₀ hn0).2
    have hh := (div_le_iff₀ hε).mp hRatio
    simpa only [mul_comm] using hh

/-- A genuine eventually-derived order for the EGJ13 clone numerics. This
order is existential; no computable tower bound for the Pasch theorem is claimed. -/
theorem exists_egj13_square_order (C c ε D0 : ℝ) (q : ℕ)
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ (n : ℝ)^2 ∧ D0 ≤ (n : ℝ)^2 ∧
      C*n ≤ ((n : ℝ)^2)^(3/4 : ℝ) ∧
      (n : ℝ)^4 ≤ Real.exp (((n : ℝ)^2)^(egj13Epsilon^2)) ∧
      (n : ℝ)^q ≤ Real.exp (((n : ℝ)^2)^(egj13Epsilon^2)) ∧
      ((n : ℝ)^2)^(-egj13Epsilon) ≤ ε ∧ 2*C ≤ n ∧ 32*C^3 ≤ c*n ∧ C/n ≤ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hh := ht.eventually (eventually_square_conditions C c ε D0 q hc hε)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hh
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro n hn
  exact (hN n ((le_max_right _ _).trans hn)).2

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.exists_egj13_square_order
