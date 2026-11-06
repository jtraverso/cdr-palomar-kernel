/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.Pseudorandom.Eventually12
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Filter
open scoped Topology
noncomputable section
namespace TypedTriangle.WeightedClone

/-- All numerical EGJ obligations for cloned diffuse triangles hold uniformly
for large hosts. Here D=n^2+Cn, p=n^2 and epsilon=1/3200. The mass threshold is
linear in n; in particular it applies to localized anchor tests. -/
theorem eventually_clone_numerics (C c η D₀ : ℝ) (q : ℕ)
    (hC : 0 ≤ C) (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ n : ℝ in atTop,
      1 ≤ n ∧ D₀ ≤ n^2+C*n ∧ 1 ≤ n^2+C*n ∧
      C*n+1 ≤ (n^2+C*n)^((3:ℝ)/4) ∧
      (n^2+C*n)*n^2 ≤ Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) ∧
      n^q ≤ Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) ∧
      (n^2+C*n)^((5:ℝ)/4) ≤ n^2*(c*n) ∧
      (n^2+C*n)^(-((1:ℝ)/3200))+2*(C*n)/(n^2+C*n) ≤ η := by
  have hlim : Tendsto (fun n : ℝ => n^(-((2:ℝ)/3200))+2*C/n) atTop (𝓝 0) := by
    have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2/3200)
    have h₂ : Tendsto (fun n : ℝ => (2*C)/n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using h₁.add (h₂ : Tendsto (fun n : ℝ => (2*C)/n) atTop (𝓝 0))
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop C,
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).eventually_ge_atTop D₀,
    Pseudorandom.eventually_const_le_rpow (by norm_num : (0:ℝ)<1/4) 2,
    Pseudorandom.eventually_mul_rpow_le_rpow (α:=1) (β:=(3:ℝ)/2) (by norm_num) (C+1),
    Pseudorandom.eventually_mul_log_le_rpow (by norm_num : (0:ℝ)<2*((1/3200:ℝ)^2)) 5,
    Pseudorandom.eventually_mul_log_le_rpow (by norm_num : (0:ℝ)<2*((1/3200:ℝ)^2)) q,
    Pseudorandom.eventually_rpow_le_mul_rpow (σ:=(45:ℝ)/16) (γ:=3) (by norm_num) hc,
    hlim.eventually (gt_mem_nhds hη)] with n hn hnC hnD hn2 hncode hnlog hnlogq hnmass hnerr
  have hn0 : 0 < n := by linarith
  have hDpos : 0 < n^2+C*n := by positivity
  have hDlo : n^2 ≤ n^2+C*n := le_add_of_nonneg_right (mul_nonneg hC hn0.le)
  have hDupper : n^2+C*n ≤ n^((9:ℝ)/4) := by
    have hCn : C*n ≤ n^2 := by nlinarith
    calc n^2+C*n ≤ 2*n^2 := by linarith
      _ ≤ n^((1:ℝ)/4)*n^2 := mul_le_mul_of_nonneg_right hn2 (sq_nonneg _)
      _ = n^((9:ℝ)/4) := by rw [←Real.rpow_natCast,←Real.rpow_add hn0]; norm_num
  have hpower (a : ℝ) (ha : 0 ≤ a) : (n^2+C*n)^a ≤ n^((9/4:ℝ)*a) := by
    calc (n^2+C*n)^a ≤ (n^((9:ℝ)/4))^a := Real.rpow_le_rpow (by positivity) hDupper ha
      _ = _ := (Real.rpow_mul hn0.le _ _).symm
  have hlowpow (a : ℝ) (ha : 0 ≤ a) : n^(2*a) ≤ (n^2+C*n)^a := by
    rw [Real.rpow_mul hn0.le,Real.rpow_two]
    exact Real.rpow_le_rpow (sq_nonneg _) hDlo ha
  have hexp : ∀ k : ℕ, (k:ℝ)*Real.log n ≤ n^(2*((1/3200:ℝ)^2)) →
      n^k ≤ Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) := by
    intro k hk
    calc n^k = Real.exp ((k:ℝ)*Real.log n) := by rw [←Real.log_pow,Real.exp_log (pow_pos hn0 _)]
      _ ≤ Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) :=
        Real.exp_le_exp.mpr (hk.trans (hlowpow _ (by positivity)))
  have hsize : (n^2+C*n)*n^2 ≤ n^5 := by
    calc (n^2+C*n)*n^2 ≤ n^((9:ℝ)/4)*n^2 := mul_le_mul_of_nonneg_right hDupper (sq_nonneg _)
      _ = n^((17:ℝ)/4) := by rw [←Real.rpow_natCast,←Real.rpow_add hn0]; norm_num
      _ ≤ n^5 := by rw [←Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have herror : (n^2+C*n)^(-((1:ℝ)/3200))+2*(C*n)/(n^2+C*n) ≤
      n^(-((2:ℝ)/3200))+2*C/n := by
    apply add_le_add
    · calc (n^2+C*n)^(-((1:ℝ)/3200)) ≤ (n^2)^(-((1:ℝ)/3200)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hDlo (by norm_num)
        _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hn0.le]; norm_num
    · calc 2*(C*n)/(n^2+C*n) ≤ 2*(C*n)/n^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hDlo
        _ = 2*C/n := by field_simp <;> ring
  refine ⟨hn,hnD.trans hDlo,(by nlinarith),?_,hsize.trans (hexp 5 hnlog),hexp q hnlogq,?_,herror.trans hnerr.le⟩
  · calc C*n+1 ≤ (C+1)*n := by nlinarith
      _ ≤ n^((3:ℝ)/2) := by simpa using hncode
      _ ≤ (n^2+C*n)^((3:ℝ)/4) := by convert hlowpow ((3:ℝ)/4) (by norm_num) using 1 <;> norm_num
  · calc (n^2+C*n)^((5:ℝ)/4) ≤ n^((45:ℝ)/16) := by convert hpower ((5:ℝ)/4) (by norm_num) using 1 <;> norm_num
      _ ≤ c*n^(3:ℝ) := hnmass
      _ = n^2*(c*n) := by rw [Real.rpow_ofNat]; ring
end TypedTriangle.WeightedClone
