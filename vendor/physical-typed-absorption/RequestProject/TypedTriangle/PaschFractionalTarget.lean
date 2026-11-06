module
public import RequestProject.TypedTriangle.PaschStatistics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch

private theorem fourth_power_bounds {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    1-15*ν ≤ (1-ν)^4 ∧ (1+ν)^4 ≤ 1+15*ν := by
  have hLo : 0 ≤ ν^2*((ν-2)^2+2)+11*ν := by positivity
  have hHi : 0 ≤ ν*(1-ν)*(ν^2+5*ν+11) :=
    mul_nonneg (mul_nonneg hν0 (sub_nonneg.mpr hν1)) (by positivity)
  constructor <;> nlinarith only [hLo,hHi]

theorem prod_four_difference_of_relative {A : Type*} (S : Finset A)
    (μ ψ : A → ℝ) (ν : ℝ) (hS : S.card = 4) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hμ : ∀ T ∈ S, 0 ≤ μ T) (hClose : ∀ T ∈ S, |ψ T-μ T| ≤ ν*μ T) :
    |(∏ T ∈ S, ψ T)-(∏ T ∈ S, μ T)| ≤ 15*ν*(∏ T ∈ S, μ T) := by
  have hLower : ∀ T ∈ S, (1-ν)*μ T ≤ ψ T := by
    intro T hT
    have h := (abs_le.mp (hClose T hT)).1
    nlinarith only [h]
  have hUpper : ∀ T ∈ S, ψ T ≤ (1+ν)*μ T := by
    intro T hT
    have h := (abs_le.mp (hClose T hT)).2
    nlinarith only [h]
  have hψ : ∀ T ∈ S, 0 ≤ ψ T := by
    intro T hT
    exact (mul_nonneg (sub_nonneg.mpr hν1) (hμ T hT)).trans (hLower T hT)
  have hLo : (1-ν)^4*(∏ T ∈ S, μ T) ≤ ∏ T ∈ S, ψ T := by
    have hp := Finset.prod_le_prod₀ (fun T hT => mul_nonneg (sub_nonneg.mpr hν1) (hμ T hT)) hLower
    simpa only [prod_mul_distrib,prod_const,hS] using hp
  have hHi : (∏ T ∈ S, ψ T) ≤ (1+ν)^4*(∏ T ∈ S, μ T) := by
    have hp := Finset.prod_le_prod₀ hψ hUpper
    simpa only [prod_mul_distrib,prod_const,hS] using hp
  have hBase : 0 ≤ ∏ T ∈ S, μ T := Finset.prod_nonneg hμ
  have hBounds := fourth_power_bounds hν0 hν1
  have hLo' := (mul_le_mul_of_nonneg_right hBounds.1 hBase).trans hLo
  have hHi' := hHi.trans (mul_le_mul_of_nonneg_right hBounds.2 hBase)
  apply abs_le.mpr
  constructor <;> nlinarith only [hLo',hHi']

theorem target_nonneg_on {V : Type*} [DecidableEq V]
    (D : Finset (Finset V)) (μ : Finset V → ℝ) (hμ : ∀ T ∈ D, 0 ≤ μ T) :
    0 ≤ target μ D := by
  rw [target,statistic_eq_sum]
  apply sum_nonneg
  intro S hS
  exact prod_nonneg (fun T hT => hμ T ((mem_configurations.mp hS).1 hT))

/-- A relative fractional target bound on the same surviving triangle domain.
This does not estimate the patterns removed by restricting that domain. -/
theorem target_difference_of_relative_pointwise {V : Type*} [DecidableEq V]
    (D : Finset (Finset V)) (μ ψ : Finset V → ℝ) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hμ : ∀ T ∈ D, 0 ≤ μ T)
    (hClose : ∀ T ∈ D, |ψ T-μ T| ≤ ν*μ T) :
    |target ψ D-target μ D| ≤ 15*ν*target μ D := by
  simp only [target,statistic_eq_sum]
  calc
    |(∑ S ∈ configurations D, ∏ T ∈ S, ψ T)-(∑ S ∈ configurations D, ∏ T ∈ S, μ T)| =
        |∑ S ∈ configurations D, ((∏ T ∈ S, ψ T)-(∏ T ∈ S, μ T))| := by rw [sum_sub_distrib]
    _ ≤ ∑ S ∈ configurations D, |(∏ T ∈ S, ψ T)-(∏ T ∈ S, μ T)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ configurations D, 15*ν*(∏ T ∈ S, μ T) := by
      apply sum_le_sum
      intro S hS
      obtain ⟨hSD,hCard,_⟩ := mem_configurations.mp hS
      exact prod_four_difference_of_relative S μ ψ ν hCard hν0 hν1
        (fun T hT => hμ T (hSD hT)) (fun T hT => hClose T (hSD hT))
    _ = 15*ν*(∑ S ∈ configurations D, ∏ T ∈ S, μ T) := by rw [mul_sum]

theorem target_difference_of_absolute_pointwise {V : Type*} [DecidableEq V]
    (D : Finset (Finset V)) (μ ψ : Finset V → ℝ) (n C ε : ℝ)
    (hn : 0 < n) (hC : 0 < C) (hε : 0 ≤ ε) (hSmall : C*ε ≤ 1)
    (hLower : ∀ T ∈ D, 1/(C*n) ≤ μ T)
    (hClose : ∀ T ∈ D, |ψ T-μ T| ≤ ε/n) :
    |target ψ D-target μ D| ≤ 15*(C*ε)*target μ D := by
  have hμ : ∀ T ∈ D, 0 ≤ μ T := by
    intro T hT
    exact (div_nonneg (by norm_num) (mul_nonneg hC.le hn.le)).trans (hLower T hT)
  apply target_difference_of_relative_pointwise D μ ψ (C*ε) (mul_nonneg hC.le hε) hSmall hμ
  intro T hT
  calc |ψ T-μ T| ≤ ε/n := hClose T hT
    _ = (C*ε)*(1/(C*n)) := by field_simp
    _ ≤ (C*ε)*μ T := mul_le_mul_of_nonneg_left (hLower T hT) (mul_nonneg hC.le hε)

/-- The actual seed-persistence pointwise error K*d/n², with d≤δ*n,
is a relative O(K*C*δ) perturbation of the surviving Pasch target. -/
theorem target_difference_of_paid_seed {V : Type*} [DecidableEq V]
    (D : Finset (Finset V)) (μ ψ : Finset V → ℝ) (n C K δ d : ℝ)
    (hn : 0 < n) (hC : 0 < C) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hd : d ≤ δ*n) (hSmall : C*(K*δ) ≤ 1)
    (hLower : ∀ T ∈ D, 1/(C*n) ≤ μ T)
    (hClose : ∀ T ∈ D, |ψ T-μ T| ≤ K*d/n^2) :
    |target ψ D-target μ D| ≤ 15*(C*(K*δ))*target μ D := by
  apply target_difference_of_absolute_pointwise D μ ψ n C (K*δ) hn hC (mul_nonneg hK hδ) hSmall hLower
  intro T hT
  calc |ψ T-μ T| ≤ K*d/n^2 := hClose T hT
    _ ≤ K*(δ*n)/n^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK) (sq_nonneg n)
    _ = (K*δ)/n := by field_simp

#print axioms prod_four_difference_of_relative
#print axioms target_nonneg_on
#print axioms target_difference_of_relative_pointwise
#print axioms target_difference_of_absolute_pointwise
#print axioms target_difference_of_paid_seed
end TypedTriangle.Pasch
