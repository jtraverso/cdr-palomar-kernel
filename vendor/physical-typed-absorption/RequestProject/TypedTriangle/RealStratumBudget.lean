/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V34.Box
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Stratum

/-- Real recurrence bound retaining small real coefficients. -/
lemma cumulative_real_bound (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (m : ℕ → ℝ) (t : ℕ)
    (hm : ∀ j < t, m j ≤ a+r*∑ i ∈ range j, m i) :
    (∑ i ∈ range t, m i) ≤ a*t*(1+r)^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ih' := ih (fun j hj => hm j (by omega))
    have hstep := hm t (Nat.lt_succ_self _)
    have hp : 1 ≤ (1+r)^t := one_le_pow₀ (by linarith)
    have hmul := mul_le_mul_of_nonneg_left ih' (by linarith : 0 ≤ 1+r)
    rw [sum_range_succ,pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_left (le_trans hp (le_mul_of_one_le_left (by linarith : 0 ≤ (1+r)^t) (by linarith : 1 ≤ 1+r))) ha]

/-- First-entry arithmetic at the physical scale q >= gamma*n. Unlike the
natural-coefficient helper, this keeps eta and tau real and cancels n/q before
the geometric recurrence. The multiplier is therefore independent of host size. -/
theorem exists_large_real_stratum (A η τ n c γ q N : ℝ) (L : ℕ)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hn : 0 < n)
    (hc : 0 ≤ c) (hγ : 0 < γ) (hq : γ*n ≤ q)
    (m z : ℕ → ℝ) (hz : ∀ j ≤ L, 0 ≤ z j)
    (hpre : ∀ j ≤ L, q*z j ≤ c*∑ i ∈ range j, m i)
    (hsum : ∑ j ∈ range (L+1), m j = N)
    (hN : A*(1+τ*n^2)*(L+1)*(1+A*η*c/γ)^(L+1) < N) :
    ∃ j ≤ L, A*(1+η*n*z j+τ*n^2) ≤ m j := by
  by_contra hnone
  push_neg at hnone
  have hr : 0 ≤ A*η*c/γ := by positivity
  have ha : 0 ≤ A*(1+τ*n^2) := by positivity
  have hrec : ∀ j < L+1, m j ≤ A*(1+τ*n^2)+(A*η*c/γ)*(∑ i ∈ range j, m i) := by
    intro j hj
    have hjL : j ≤ L := by omega
    have hqz := mul_le_mul_of_nonneg_right hq (hz j hjL)
    have hload := hpre j hjL
    have hnz : n*z j ≤ (c/γ)*(∑ i ∈ range j, m i) := by
      calc n*z j ≤ (c*(∑ i ∈ range j, m i))/γ := (le_div_iff₀ hγ).mpr (by nlinarith)
           _ = (c/γ)*(∑ i ∈ range j, m i) := by ring
    have hscaled := mul_le_mul_of_nonneg_left hnz (mul_nonneg hA hη)
    have hs : A*η*n*z j ≤ (A*η*c/γ)*(∑ i ∈ range j, m i) := by
      convert hscaled using 1 <;> ring
    have hmj := hnone j hjL
    nlinarith only [hs,hmj]
  have hb := cumulative_real_bound (A*(1+τ*n^2)) (A*η*c/γ) ha hr m (L+1) hrec
  rw [hsum] at hb
  have heq : (A*(1+τ*n^2))*(L+1:ℕ)*(1+A*η*c/γ)^(L+1) =
      A*(1+τ*n^2)*(L+1)*(1+A*η*c/γ)^(L+1) := by norm_num
  rw [heq] at hb
  linarith

end TypedTriangle.Stratum
