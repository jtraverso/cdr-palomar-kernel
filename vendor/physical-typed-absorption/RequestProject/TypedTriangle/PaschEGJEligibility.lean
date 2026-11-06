module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
set_option autoImplicit false
namespace TypedTriangle.Pasch

/-- The rounding factor stays uniformly positive when its relative loss is at
most one half. -/
theorem fourth_rounding_factor_lower {x : ℝ} (hx : x ≤ 1/2) :
    (1/16 : ℝ) ≤ (1-x)^4 := by
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2)
    (by linarith only [hx] : (1/2 : ℝ) ≤ 1-x) 4
  norm_num at hh ⊢
  exact hh

/-- Scalar discharge of the four-tuple EGJ eligibility inequality after the
geometric extension bounds and fractional mass lower bound have been proved.
This is an arithmetic lemma, not a new hypothesis of a decomposition theorem. -/
theorem gamma_sqrt_le_rounded_mass {C c n gamma source rounded : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hn : 1 ≤ n) (hRound : 2*C ≤ n)
    (hScale : 32*C^3 ≤ c*n) (hGamma : gamma ≤ 2*C^3)
    (hSource : c*n^2 ≤ source)
    (hRounded : (1-C/n)^4*source ≤ rounded) :
    gamma*Real.sqrt n ≤ rounded := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hRatio : C/n ≤ 1/2 := (div_le_iff₀ hn0).2 (by linarith only [hRound])
  have hFactor := fourth_rounding_factor_lower hRatio
  have hSource0 : 0 ≤ source := (mul_nonneg hc (sq_nonneg n)).trans hSource
  have hMass : c*n^2/16 ≤ rounded := by
    have h1 := mul_le_mul_of_nonneg_right hFactor hSource0
    have h2 := div_le_div_of_nonneg_right hSource (by norm_num : (0 : ℝ) ≤ 16)
    nlinarith only [h1,h2,hRounded]
  have hSqrt : Real.sqrt n ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr hn)
  have hBound0 : 0 ≤ 2*C^3 := by positivity
  calc
    gamma*Real.sqrt n ≤ (2*C^3)*Real.sqrt n :=
      mul_le_mul_of_nonneg_right hGamma (Real.sqrt_nonneg n)
    _ ≤ (2*C^3)*n := mul_le_mul_of_nonneg_left hSqrt hBound0
    _ ≤ c*n^2/16 := by
      have hh := mul_le_mul_of_nonneg_right hScale hn0.le
      nlinarith only [hh]
    _ ≤ rounded := hMass

theorem square_rpow_quarter {n : ℝ} (hn : 0 ≤ n) :
    (n^2) ^ (1/4 : ℝ) = Real.sqrt n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn, Real.sqrt_eq_rpow]
  congr 1
  norm_num

/-- Combine an actual clone tuple-degree bound and actual clone mass bound.
The fixed copies contribute only the remaining `4-j` multiplicity factors. -/
theorem tuple_eligibility_of_gamma_sqrt {n gamma target degree mass : ℝ}
    {j : ℕ} (hn : 0 < n) (hj : j ≤ 4)
    (hDegree : degree ≤ (n^2)^(4-j)*gamma)
    (hMass : (n^2)^4*target ≤ mass)
    (hGamma : gamma*Real.sqrt n ≤ target) :
    degree * (n^2)^((j : ℝ)+(1/4 : ℝ)) ≤ mass := by
  have hn2 : 0 < n^2 := pow_pos hn 2
  have hFactor : (n^2)^((j : ℝ)+(1/4 : ℝ)) =
      (n^2)^j*Real.sqrt n := by
    rw [Real.rpow_add hn2,Real.rpow_natCast,square_rpow_quarter hn.le]
  calc
    degree * (n^2)^((j : ℝ)+(1/4 : ℝ)) ≤
        ((n^2)^(4-j)*gamma) * (n^2)^((j : ℝ)+(1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hDegree (Real.rpow_nonneg hn2.le _)
    _ = (n^2)^4 * (gamma*Real.sqrt n) := by
      rw [hFactor]
      calc
        ((n^2)^(4-j)*gamma) * ((n^2)^j*Real.sqrt n) =
            ((n^2)^(4-j)*(n^2)^j)*(gamma*Real.sqrt n) := by ring
        _ = _ := by rw [← pow_add,Nat.sub_add_cancel hj]
    _ ≤ (n^2)^4*target := mul_le_mul_of_nonneg_left hGamma (by positivity)
    _ ≤ mass := hMass

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.fourth_rounding_factor_lower
#print axioms TypedTriangle.Pasch.gamma_sqrt_le_rounded_mass
#print axioms TypedTriangle.Pasch.square_rpow_quarter
#print axioms TypedTriangle.Pasch.tuple_eligibility_of_gamma_sqrt
