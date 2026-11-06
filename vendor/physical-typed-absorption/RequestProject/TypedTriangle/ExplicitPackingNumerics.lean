/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.Pseudorandom.ExplicitAsymptotics
public import RequestProject.TypedTriangle.PackingNumerics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section
namespace TypedTriangle.WeightedClone.Explicit
open Pseudorandom.Explicit

/-- Specified host-size bound for all scalar obligations of cloned packing. -/
def cloneCut (C c η D₀ : ℝ) (q : ℕ) : ℝ :=
  max 1 (max C (max (powerCut 2 D₀)
    (max (powerCut (1/4) 2)
    (max (powerCut ((3:ℝ)/2-1) (C+1))
    (max (logCut (2*((1/3200:ℝ)^2)) 5)
    (max (logCut (2*((1/3200:ℝ)^2)) q)
    (max (powerCut (3-(45:ℝ)/16) (1/c))
    (max (powerCut ((2:ℝ)/3200) (2/η)) (4*C/η)))))))))

theorem clone_numerics_explicit (C c η D₀ : ℝ) (q : ℕ)
    (hC : 0 ≤ C) (hc : 0 < c) (hη : 0 < η) :
    ∀ n : ℝ, cloneCut C c η D₀ q ≤ n →
      1 ≤ n ∧ D₀ ≤ n^2+C*n ∧ 1 ≤ n^2+C*n ∧
      C*n+1 ≤ (n^2+C*n)^((3:ℝ)/4) ∧
      (n^2+C*n)*n^2 ≤ Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) ∧
      n^q ≤ Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) ∧
      (n^2+C*n)^((5:ℝ)/4) ≤ n^2*(c*n) ∧
      (n^2+C*n)^(-((1:ℝ)/3200))+2*(C*n)/(n^2+C*n) ≤ η := by
  intro n hnCut
  have bounds : 1 ≤ n ∧ C ≤ n ∧ powerCut 2 D₀ ≤ n ∧ powerCut (1/4) 2 ≤ n ∧
      powerCut ((3:ℝ)/2-1) (C+1) ≤ n ∧
      logCut (2*((1/3200:ℝ)^2)) 5 ≤ n ∧
      logCut (2*((1/3200:ℝ)^2)) q ≤ n ∧
      powerCut (3-(45:ℝ)/16) (1/c) ≤ n ∧
      powerCut ((2:ℝ)/3200) (2/η) ≤ n ∧ 4*C/η ≤ n := by
    simpa only [cloneCut,max_le_iff] using hnCut
  rcases bounds with ⟨hn,hnC,hnD',hn2',hncode',hnlog',hnlogq',hnmass',hnerr',hnerrC⟩
  have hnD : D₀ ≤ n^2 := by simpa using const_le_rpow (by norm_num : (0:ℝ)<2) hnD'
  have hn2 := const_le_rpow (by norm_num : (0:ℝ)<1/4) hn2'
  have hncode := mul_rpow_le_rpow (by norm_num : (1:ℝ)<3/2) hncode'
  have hnlog := mul_log_le_rpow (by norm_num : (0:ℝ)<2*((1/3200:ℝ)^2)) hnlog'
  have hnlogq := mul_log_le_rpow (by norm_num : (0:ℝ)<2*((1/3200:ℝ)^2)) hnlogq'
  have hnmass := rpow_le_mul_rpow (by norm_num : (45:ℝ)/16<3) hc hnmass'
  have hnpos : 0 < n := by linarith
  have herrpow : n^(-((2:ℝ)/3200)) ≤ η/2 := by
    have hh := const_le_rpow (by norm_num : (0:ℝ)<2/3200) hnerr'
    have hi := (inv_le_inv₀ (Real.rpow_pos_of_pos hnpos ((2:ℝ)/3200))
      (by positivity : (0:ℝ)<2/η)).mpr hh
    simpa only [Real.rpow_neg hnpos.le, one_div, inv_div] using hi
  have herrC : 2*C/n ≤ η/2 := by
    apply (div_le_iff₀ hnpos).mpr
    have hh := (div_le_iff₀ hη).mp hnerrC
    nlinarith
  have hnerr : n^(-((2:ℝ)/3200))+2*C/n ≤ η := by linarith
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
  refine ⟨hn,hnD.trans hDlo,(by nlinarith),?_,hsize.trans (hexp 5 hnlog),hexp q hnlogq,?_,herror.trans hnerr⟩
  · calc C*n+1 ≤ (C+1)*n := by nlinarith
      _ ≤ n^((3:ℝ)/2) := by simpa using hncode
      _ ≤ (n^2+C*n)^((3:ℝ)/4) := by convert hlowpow ((3:ℝ)/4) (by norm_num) using 1 <;> norm_num
  · calc (n^2+C*n)^((5:ℝ)/4) ≤ n^((45:ℝ)/16) := by convert hpower ((5:ℝ)/4) (by norm_num) using 1 <;> norm_num
      _ ≤ c*n^(3:ℝ) := hnmass
      _ = n^2*(c*n) := by rw [Real.rpow_ofNat]; ring
#print axioms clone_numerics_explicit
end TypedTriangle.WeightedClone.Explicit
