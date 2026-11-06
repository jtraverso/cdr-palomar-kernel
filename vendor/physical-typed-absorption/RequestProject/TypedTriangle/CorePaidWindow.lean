/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V27.SelectorWindow
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section

/-! Uniform scalar budget for paying the all-root selector layer in its
surviving core. Constants are chosen before the host and its input degree. -/
noncomputable section
namespace TypedTriangle.CorePaid

lemma selQ_linear {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ r, S07V27.selQ ε A r ≤ D*(r+1) := by
  let c : ℝ := 4*(A:ℝ)/min ε 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let D := ⌈c⌉₊+2
  refine ⟨D,by omega,?_⟩
  intro r
  have hcD : c+2 ≤ (D:ℝ) := by
    dsimp [D]; push_cast; linarith [Nat.le_ceil c]
  have hq : (S07V27.selQ ε A r:ℝ) ≤ c*r+2 := by
    unfold S07V27.selQ
    push_cast
    have hnon : 0 ≤ 4*(A:ℝ)*r/min ε 1 := by positivity
    have hh := Nat.ceil_lt_add_one hnon
    have heq : 4*(A:ℝ)*r/min ε 1 = c*r := by dsimp [c]; ring
    linarith
  have hR : (S07V27.selQ ε A r:ℝ) ≤ D*(r+1) := by
    have := mul_le_mul_of_nonneg_right hcD (show (0:ℝ) ≤ r by positivity)
    nlinarith
  exact_mod_cast hR

theorem payment_window (κ μ τ : ℝ) (hκ : 0 < κ) (hμ : 0 < μ) (hτ : 0 < τ)
    (A D : ℕ) :
    ∃ (δ : ℝ) (n₀ : ℕ), 0 < δ ∧
      ∀ n N r b q : ℕ, n₀ ≤ n → μ*n ≤ N → q ≤ D*(r+1) →
        (r:ℝ) ≤ δ*n → (b:ℝ) ≤ δ*n →
        ∃ p : ℕ, 0 < p ∧
          ((n*(61*r+60*q)/p +
            2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) < κ*N ∧
          ((max (A*r) (60*r+61*q)+2*(61*r+60*q+p):ℕ):ℝ) ≤ τ*n ∧
          ((3*(61*r+60*q)+2*p:ℕ):ℝ) ≤ τ*n := by
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
  let δ := min (κ*μ/(4*C)) (τ/(12*T))
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
      C*δ*n+8*γ*n := by
    have hcR : ((n*(61*r+60*q)/p +
        2*(max (A*r) (60*r+61*q)+r+b+3*(61*r+60*q)+2*p):ℕ):ℝ) ≤
        (J+8)*T*(r+1)+2*r+2*b+4*p := by exact_mod_cast hcost
    have hscaled := mul_le_mul_of_nonneg_left (show (r:ℝ)+1 ≤ 2*δ*n by linarith)
      (show (0:ℝ) ≤ (J+8)*T by positivity)
    dsimp [C]
    nlinarith
  have hδC : C*δ ≤ κ*μ/4 := by
    have h := min_le_left (κ*μ/(4*C)) (τ/(12*T))
    change δ ≤ _ at h
    have := (le_div_iff₀ (show 0 < 4*C by positivity)).mp h
    linarith
  have hγK : 8*γ ≤ κ*μ/4 := by
    have := min_le_left (κ*μ/32) (τ/8)
    change γ ≤ _ at this
    linarith
  have hδT : 6*T*δ ≤ τ/2 := by
    have h := min_le_right (κ*μ/(4*C)) (τ/(12*T))
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
    have h3 := mul_le_mul_of_nonneg_left hN hκ.le
    have h4 : 0 < κ*μ*n := by positivity
    nlinarith
  · push_cast at hyR hzR ⊢
    nlinarith
  · push_cast at hyR hzR ⊢
    nlinarith

end TypedTriangle.CorePaid
