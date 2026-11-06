/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RealStratumConstants
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.CatalogNative

/-- Linear degree/deletion windows support quadratically many rounds of a
fixed finite catalog. All constants and the size threshold precede the host. -/
theorem quadratic_bank_budget (ε δ : ℝ) (E B : ℕ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ q z : ℕ, 0 < q ∧ (z:ℝ) ≤ δ*n ∧
        ((q+B*E:ℕ):ℝ) ≤ ε*n ∧
        2*E*B*⌊κ*(n:ℝ)^2⌋₊ ≤ q*z ∧
        ε/4*n ≤ (q:ℝ) := by
  let κ := ε*δ/(32*((E*B:ℕ)+1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ,hκ,max 1 (max ⌈4/ε⌉₊ (max ⌈2/δ⌉₊ ⌈2*(B*E:ℕ)/ε⌉₊)),?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hne : 4 ≤ ε*n := by
    have hc : ⌈4/ε⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hh := (Nat.le_ceil (4/ε)).trans (show (⌈4/ε⌉₊:ℝ) ≤ n by exact_mod_cast hc)
    rw [div_le_iff₀ hε] at hh
    linarith
  have hnd : 2 ≤ δ*n := by
    have hc : ⌈2/δ⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (Nat.le_ceil (2/δ)).trans (show (⌈2/δ⌉₊:ℝ) ≤ n by exact_mod_cast hc)
    rw [div_le_iff₀ hδ] at hh
    linarith
  have hnB : 2*(B*E:ℕ) ≤ ε*n := by
    have hc : ⌈2*(B*E:ℕ)/ε⌉₊ ≤ n :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (Nat.le_ceil (2*(B*E:ℕ)/ε)).trans
      (show (⌈2*(B*E:ℕ)/ε⌉₊:ℝ) ≤ n by exact_mod_cast hc)
    rw [div_le_iff₀ hε] at hh
    linarith
  let q := ⌊ε*n/2⌋₊
  let z := ⌊δ*n⌋₊
  have hqu : (q:ℝ) ≤ ε*n/2 := Nat.floor_le (by positivity)
  have hzu : (z:ℝ) ≤ δ*n := Nat.floor_le (by positivity)
  have hql : ε/4*n ≤ (q:ℝ) := by
    have hh := Nat.sub_one_lt_floor (ε*n/2)
    change ε*n/2-1 < (q:ℝ) at hh
    linarith
  have hzl : δ/2*n ≤ (z:ℝ) := by
    have hh := Nat.sub_one_lt_floor (δ*n)
    change δ*n-1 < (z:ℝ) at hh
    linarith
  have hqp : 0 < q := by
    have hh : (0:ℝ) < q := by linarith
    exact_mod_cast hh
  have hcoef : 2*(E:ℝ)*B*κ ≤ ε*δ/8 := by
    have hd : (0:ℝ) < 32*((E*B:ℕ)+1) := by positivity
    change 2*(E:ℝ)*B*(ε*δ/(32*((E*B:ℕ)+1))) ≤ ε*δ/8
    rw [←mul_div_assoc,div_le_iff₀ hd]
    push_cast
    nlinarith [mul_pos hε hδ,
      mul_nonneg (mul_pos hε hδ).le (by positivity : (0:ℝ) ≤ (E:ℝ)*B)]
  have hN : (⌊κ*(n:ℝ)^2⌋₊:ℝ) ≤ κ*(n:ℝ)^2 := Nat.floor_le (by positivity)
  have hcap : (2:ℝ)*E*B*(⌊κ*(n:ℝ)^2⌋₊:ℝ) ≤ (q:ℝ)*z := by
    have h₁ := mul_le_mul_of_nonneg_left hN (by positivity : (0:ℝ) ≤ 2*E*B)
    have h₂ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n:ℝ))
    have h₃ := mul_le_mul hql hzl (by positivity : (0:ℝ) ≤ δ/2*n) (by positivity : (0:ℝ) ≤ q)
    nlinarith only [h₁,h₂,h₃]
  refine ⟨q,z,hqp,hzu,?_,by exact_mod_cast hcap,hql⟩
  push_cast
  push_cast at hnB
  linarith
end TypedTriangle.CatalogNative
