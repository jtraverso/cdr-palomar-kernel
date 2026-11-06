/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4ActualMomentCap
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The terminal prefix capacity follows from the sampled core's quadratic
bank size once the monitor tolerance is chosen after the bank density. -/

namespace TypedTriangle.StockEntry

theorem final_bank_capacity_of_sample_size
    (κ q η : ℝ) (n w : ℕ) (hκ : 0 < κ) (hq : 0 < q)
    (hw : q * n / 2 ≤ w) (hη : η ≤ κ * q ^ 2 / 8)
    (hlarge : 8 ≤ κ * q ^ 2 * (n : ℝ) ^ 2) :
    1 + η * (n : ℝ) ^ 2 ≤
      2 * (⌊κ * (w : ℝ) ^ 2⌋₊ : ℕ) := by
  let N := ⌊κ * (w : ℝ) ^ 2⌋₊
  have hfloor : κ * (w : ℝ) ^ 2 < (N : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hqn : (0 : ℝ) ≤ q * n / 2 := by positivity
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hsq : (q * n / 2) ^ 2 ≤ (w : ℝ) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hw) (add_nonneg hw0 hqn)
    nlinarith only [hprod]
  have hsqκ := mul_le_mul_of_nonneg_left hsq hκ.le
  have hηn := mul_le_mul_of_nonneg_right hη
    (sq_nonneg (n : ℝ))
  change 1 + η * (n : ℝ) ^ 2 ≤ 2 * (N : ℝ)
  nlinarith only [hfloor, hsqκ, hηn, hlarge]

theorem eventually_large_for_bank (κ q : ℝ) (hκ : 0 < κ) (hq : 0 < q) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      8 ≤ κ * q ^ 2 * (n : ℝ) ^ 2 := by
  let a := κ * q ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨⌈8 / a⌉₊ + 1, ?_⟩
  intro n hn
  have hnOne : 1 ≤ n := by omega
  have hbound : 8 / a ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_trans
      (Nat.le_add_right _ _) hn))
  have hlinear : 8 ≤ a * (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hbound
  have hquad : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    nlinarith
  have hgrow := mul_le_mul_of_nonneg_left hquad ha.le
  dsimp [a] at hlinear hgrow
  nlinarith only [hlinear, hgrow]

end TypedTriangle.StockEntry

#print axioms TypedTriangle.StockEntry.final_bank_capacity_of_sample_size
