/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3SplitPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
namespace TypedTriangle.CorePaid

/-- The forbidden stock cap is fixed before an arbitrarily small selector
output cap is requested. -/
theorem payment_window_uniform (κ μ : ℝ) (hκ : 0 < κ) (hμ : 0 < μ)
    (A D : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ τ : ℝ, 0 < τ →
    ∃ (δ : ℝ) (n₀ : ℕ), 0 < δ ∧
      ∀ n N r b q : ℕ, n₀ ≤ n → μ*n ≤ N → q ≤ D*(r+1) →
        (r:ℝ) ≤ δ*n → (b:ℝ) ≤ θ*n →
        ∃ p : ℕ, 0 < p ∧
          ((n*(61*r+60*q)/p +
            2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) < κ*N ∧
          ((max (A*r) (60*r+61*q)+2*(61*r+60*q+p):ℕ):ℝ) ≤ τ*n ∧
          ((3*(61*r+60*q)+2*p:ℕ):ℝ) ≤ τ*n := by
  let θ := κ*μ/16
  refine ⟨θ,by positivity,?_⟩
  intro τ hτ
  let T : ℕ := A+61*D+61
  have hT : (0:ℝ) < T := by dsimp [T]; positivity
  let γ := min (κ*μ/32) (τ/8)
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  let J : ℕ := ⌈1/γ⌉₊
  have hJ : 1 ≤ (J:ℝ)*γ := by
    have := Nat.le_ceil (1/γ)
    exact (div_le_iff₀ hγ).mp this
  let C : ℝ := 2*(J+8)*T+4
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := min (κ*μ/(8*C)) (τ/(12*T))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,max (max ⌈1/δ⌉₊ ⌈1/γ⌉₊) 1,hδ,?_⟩
  intro n N r b q hn hN hq hr hb
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδn : 1 ≤ δ*n := by
    have hh : (⌈1/δ⌉₊:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans ((le_max_left _ _).trans hn)
    have := (Nat.le_ceil (1/δ)).trans hh
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp this
  have hγn : 1 ≤ γ*n := by
    have hh : (⌈1/γ⌉₊:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have := (Nat.le_ceil (1/γ)).trans hh
    simpa only [mul_comm] using (div_le_iff₀ hγ).mp this
  let p : ℕ := ⌈γ*n⌉₊
  have hpR : γ*n ≤ (p:ℝ) := Nat.le_ceil _
  have hp : 0 < p := by exact_mod_cast (show (0:ℝ) < p by linarith)
  have hpHi : (p:ℝ) ≤ 2*γ*n := by
    have := Nat.ceil_lt_add_one (show 0 ≤ γ*n by positivity)
    change (⌈γ*n⌉₊:ℝ) ≤ _
    linarith
  have hnJ : n ≤ J*p := by
    have h1 := mul_le_mul_of_nonneg_right hJ hnpos.le
    have h2 := mul_le_mul_of_nonneg_left hpR (show (0:ℝ) ≤ J by positivity)
    exact_mod_cast (show (n:ℝ) ≤ J*p by nlinarith)
  have hy : 61*r+60*q ≤ T*(r+1) := by dsimp [T]; nlinarith
  have hz : max (A*r) (60*r+61*q) ≤ T*(r+1) := by
    apply max_le
    · dsimp [T]; nlinarith
    · dsimp [T]; nlinarith
  have hdiv : n*(61*r+60*q)/p ≤ J*(61*r+60*q) := by
    apply (Nat.div_le_iff_le_mul hp).mpr
    calc n*(61*r+60*q) ≤ (J*p)*(61*r+60*q) := Nat.mul_le_mul_right _ hnJ
      _ ≤ J*(61*r+60*q)*p+p-1 := by
        have heq : (J*p)*(61*r+60*q) = J*(61*r+60*q)*p := by ring
        rw [heq]
        omega
  have hcost : n*(61*r+60*q)/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p) ≤
      (J+8)*T*(r+1)+2*r+2*b+4*p := by nlinarith
  have hcostR : ((n*(61*r+60*q)/p +
      2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
      C*δ*n+2*b+8*γ*n := by
    have hcR : ((n*(61*r+60*q)/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
        (J+8)*T*(r+1)+2*r+2*b+4*p := by exact_mod_cast hcost
    have hscaled := mul_le_mul_of_nonneg_left (show (r:ℝ)+1 ≤ 2*δ*n by linarith)
      (show (0:ℝ) ≤ (J+8)*T by positivity)
    dsimp [C]
    nlinarith
  have hδC : C*δ ≤ κ*μ/8 := by
    have h := min_le_left (κ*μ/(8*C)) (τ/(12*T))
    change δ ≤ _ at h
    have := (le_div_iff₀ (show 0 < 8*C by positivity)).mp h
    linarith
  have hγK : 8*γ ≤ κ*μ/4 := by
    have := min_le_left (κ*μ/32) (τ/8)
    change γ ≤ _ at this
    linarith
  have hθK : 2*θ ≤ κ*μ/8 := by dsimp [θ]; linarith [mul_nonneg hκ.le hμ.le]
  have hδT : 6*T*δ ≤ τ/2 := by
    have h := min_le_right (κ*μ/(8*C)) (τ/(12*T))
    change δ ≤ _ at h
    have := (le_div_iff₀ (show (0:ℝ) < 12*T by positivity)).mp h
    linarith
  have hγT : 4*γ ≤ τ/2 := by
    have := min_le_right (κ*μ/32) (τ/8)
    change γ ≤ _ at this
    linarith
  have hsmall : 6*T*δ*n+4*γ*n ≤ τ*n := by
    have := mul_le_mul_of_nonneg_right hδT hnpos.le
    have := mul_le_mul_of_nonneg_right hγT hnpos.le
    nlinarith
  have hyR : ((61*r+60*q:ℕ):ℝ) ≤ T*(r+1) := by exact_mod_cast hy
  have hzR : ((max (A*r) (60*r+61*q):ℕ):ℝ) ≤ T*(r+1) := by exact_mod_cast hz
  have hsc := mul_le_mul_of_nonneg_left (show (r:ℝ)+1 ≤ 2*δ*n by linarith) hT.le
  refine ⟨p,hp,?_,?_,?_⟩
  · have h1 := mul_le_mul_of_nonneg_right hδC hnpos.le
    have h2 := mul_le_mul_of_nonneg_right hγK hnpos.le
    have h5 := mul_le_mul_of_nonneg_right hθK hnpos.le
    have h3 := mul_le_mul_of_nonneg_left hN hκ.le
    have h4 : 0 < κ*μ*n := by positivity
    nlinarith only [hcostR,h1,h2,h5,hb,h3,h4]
  · push_cast at hyR hzR ⊢
    nlinarith
  · push_cast at hyR hzR ⊢
    nlinarith



end TypedTriangle.CorePaid
