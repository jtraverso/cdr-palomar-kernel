/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07.RandomCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Sample entire basal blocks, not individual edges. A local load only sees
its incident blocks. Thus its variance budget is local even when the total
number of blocks is quadratic. The graph/packing incidence adapter and its
large-order window are separate obligations; this lemma does not assert G4. -/

noncomputable section
open Finset Classical S07V24
namespace TypedTriangle.BasalSampling

variable {B : Type*} [Fintype B] [DecidableEq B]

lemma singleton_mean (q : ℝ) (S : Finset B) :
    bexp q univ (fun W => (ccount S (fun b => {b}) W : ℝ)) = q * S.card := by
  have hf : (fun W => (ccount S (fun b => {b}) W : ℝ)) =
      (fun W => ∑ b ∈ S, if ({b} : Finset B) ⊆ W then (1 : ℝ) else 0) := by
    funext W
    simp only [ccount, sum_boole]
  rw [hf, bexp_sum]
  simp_rw [bexp_subset_ind univ _ (subset_univ _), card_singleton, pow_one]
  simp [mul_comm]

/-- An upper load bound depends on the incident-block count, not `card B`. -/
theorem load_tail {q N : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (S : Finset B)
    (hS : (S.card : ℝ) ≤ N) :
    bprob q univ (fun W => 2 * q * N ≤ (ccount S (fun b => {b}) W : ℝ)) ≤
      Real.exp (-(q ^ 2 * N / 4)) := by
  let c : B → ℝ := fun b => if b ∈ S then 1 else 0
  let f : Finset B → ℝ := fun W => ccount S (fun b => {b}) W
  have hc : ∀ b : B, 0 ≤ c b := by intro b; dsimp [c]; split_ifs <;> norm_num
  have hc1 : ∀ b : B, c b ≤ 1 := by intro b; dsimp [c]; split_ifs <;> norm_num
  have hf : ∀ W ⊆ (univ : Finset B), ∀ b ∈ (univ : Finset B), b ∉ W →
      |f (insert b W) - f W| ≤ c b := by
    intro W _ b _ _
    have ht := ccount_diff S (fun b => ({b} : Finset B)) W b
    by_cases hb : b ∈ S <;> simpa [f, c, Finset.filter_eq, hb] using ht
  have hs : ∑ b ∈ (univ : Finset B), c b ^ 2 = (S.card : ℝ) := by
    simp [c]
  have hm : bexp q univ f = q * S.card := singleton_mean q S
  have hl : 0 ≤ q / 2 := by positivity
  have ht := tail_upper hq.le hq1 c hl univ f hf
    (fun b _ => by nlinarith [hc b, hc1 b]) (q * N)
  calc
    bprob q univ (fun W => 2 * q * N ≤ (ccount S (fun b => {b}) W : ℝ))
        ≤ bprob q univ (fun W => bexp q univ f + q * N ≤ f W) := by
          apply bprob_mono hq.le hq1
          intro W hW
          rw [hm]
          dsimp only [f] at hW ⊢
          have := mul_le_mul_of_nonneg_left hS hq.le
          linarith
    _ ≤ Real.exp (-(q / 2 * (q * N)) + (q / 2) ^ 2 * ∑ b ∈ univ, c b ^ 2) := ht
    _ ≤ Real.exp (-(q ^ 2 * N / 4)) := by
      apply Real.exp_le_exp.mpr
      rw [hs]
      nlinarith [mul_le_mul_of_nonneg_left hS (sq_nonneg (q / 2))]

/-- Two simultaneous events: small root loads and many retained two-block
completions. The explicit probability window is to be derived from the original
host parameters; it is not an added hypothesis of the target theorem. -/
theorem simultaneous_sample {κ τ ι : Type*} [Fintype κ] [Fintype τ] [DecidableEq ι]
    (q N L : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (S : κ → Finset B) (J : τ → Finset ι) (dep : τ → ι → Finset B)
    (hS : ∀ k, ((S k).card : ℝ) ≤ N)
    (hJ : ∀ t, L ≤ (J t).card)
    (hsize : ∀ t i, i ∈ J t → (dep t i).card ≤ 2)
    (hload : ∀ t b, (((J t).filter (fun i => b ∈ dep t i)).card : ℝ) ≤ 4)
    (hwindow : Fintype.card κ * Real.exp (-(q ^ 2 * N / 4)) +
      Fintype.card τ * Real.exp (-(L * q ^ 4 / 128)) < 1) :
    ∃ W : Finset B,
      (∀ k, (ccount (S k) (fun b => {b}) W : ℝ) < 2 * q * N) ∧
      (∀ t, L * q ^ 2 / 2 ≤ (ccount (J t) (dep t) W : ℝ)) := by
  let bad : κ ⊕ τ → Finset B → Prop := fun j W => match j with
    | .inl k => 2 * q * N ≤ (ccount (S k) (fun b => {b}) W : ℝ)
    | .inr t => (ccount (J t) (dep t) W : ℝ) < L * q ^ 2 / 2
  have hbad : ∑ j ∈ (univ : Finset (κ ⊕ τ)), bprob q univ (bad j) < 1 := by
    rw [Fintype.sum_sum_type]
    apply lt_of_le_of_lt _ hwindow
    apply add_le_add
    · calc
        ∑ k : κ, bprob q univ (bad (.inl k)) ≤
            ∑ _k : κ, Real.exp (-(q ^ 2 * N / 4)) := by
              apply sum_le_sum; intro k _; exact load_tail hq hq1 (S k) (hS k)
        _ = _ := by simp [mul_comm]
    · calc
        ∑ t : τ, bprob q univ (bad (.inr t)) ≤
            ∑ _t : τ, Real.exp (-(L * q ^ 4 / 128)) := by
              apply sum_le_sum
              intro t _
              have ht := count_tail (V := B) hq hq1 (J t) (dep t)
                (r := 2) (by norm_num) (hsize t) (Δ := 4) (by norm_num) (hload t) (hJ t)
              norm_num [bad] at ht ⊢
              exact ht
        _ = _ := by simp [mul_comm]
  obtain ⟨W, _, hW⟩ := exists_good hq.le hq1 (univ : Finset B) univ bad hbad
  exact ⟨W, fun k => lt_of_not_ge (hW (.inl k) (mem_univ _)),
    fun t => le_of_not_gt (hW (.inr t) (mem_univ _))⟩

/-- The finite probability window follows from an order threshold fixed from
the sampling rate and supply rate, independently of the host and block count. -/
theorem sampling_window {q β : ℝ} (hq : 0 < q) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ n a b : ℕ, n₀ ≤ n → a ≤ n → b ≤ n ^ 2 →
      (a : ℝ) * Real.exp (-(q ^ 2 * n / 4)) +
      b * Real.exp (-(β * n * q ^ 4 / 128)) < 1 := by
  let θ : ℝ := min (q ^ 2 / 4) (β * q ^ 4 / 128)
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  refine ⟨⌈96 / θ ^ 4⌉₊ + 1, ?_⟩
  intro n a b hn ha hb
  have hnR : (96 / θ ^ 4 : ℝ) < n := by
    have h1 := Nat.le_ceil (96 / θ ^ 4)
    have h2 : ((⌈96 / θ ^ 4⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have haR : (a : ℝ) ≤ n := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hb
  have e1 : Real.exp (-(q ^ 2 * n / 4)) ≤ Real.exp (-(θ * n)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left (q ^ 2 / 4) (β * q ^ 4 / 128)) hn0
    dsimp only [θ]
    nlinarith
  have e2 : Real.exp (-(β * n * q ^ 4 / 128)) ≤ Real.exp (-(θ * n)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right (q ^ 2 / 4) (β * q ^ 4 / 128)) hn0
    dsimp only [θ]
    nlinarith
  have hpoly : (n : ℝ) + (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_left hn1 hn0
    have h2 := mul_le_mul_of_nonneg_left hn1 (sq_nonneg (n : ℝ))
    nlinarith
  calc
    _ ≤ (n : ℝ) * Real.exp (-(θ * n)) + (n : ℝ) ^ 2 * Real.exp (-(θ * n)) :=
      add_le_add (mul_le_mul haR e1 (Real.exp_pos _).le hn0)
        (mul_le_mul hbR e2 (Real.exp_pos _).le (sq_nonneg _))
    _ = ((n : ℝ) + (n : ℝ) ^ 2) * Real.exp (-(θ * n)) := by ring
    _ ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-(θ * n)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ < 1 := four_cube_exp_lt hθ hnR

/-- A block can influence only centers in its own three-vertex support. -/
lemma completion_load_le_four {V : Type*} [DecidableEq V]
    (J : Finset V) (dep : V → Finset B) (supp : B → Finset V)
    (hmem : ∀ v ∈ J, ∀ b ∈ dep v, v ∈ supp b)
    (hcard : ∀ b, (supp b).card ≤ 3) (b : B) :
    ((J.filter (fun v => b ∈ dep v)).card : ℝ) ≤ 4 := by
  have hs : J.filter (fun v => b ∈ dep v) ⊆ supp b := by
    intro v hv
    exact hmem v (mem_filter.mp hv).1 b (mem_filter.mp hv).2
  have ht := (card_le_card hs).trans (hcard b)
  have : ((J.filter (fun v => b ∈ dep v)).card : ℝ) ≤ 3 := by exact_mod_cast ht
  linarith

/-- No extra finite probability hypothesis: the order threshold is fixed
before all blocks, load monitors and completion tests. -/
theorem simultaneous_sample_large {κ τ ι : Type*} [Fintype κ] [Fintype τ] [DecidableEq ι]
    (q β : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Fintype.card κ ≤ n → Fintype.card τ ≤ n ^ 2 →
      ∀ (S : κ → Finset B) (J : τ → Finset ι) (dep : τ → ι → Finset B),
      (∀ k, (S k).card ≤ n) → (∀ t, β * n ≤ (J t).card) →
      (∀ t i, i ∈ J t → (dep t i).card ≤ 2) →
      (∀ t b, (((J t).filter (fun i => b ∈ dep t i)).card : ℝ) ≤ 4) →
      ∃ W : Finset B,
        (∀ k, (ccount (S k) (fun b => {b}) W : ℝ) < 2 * q * n) ∧
        (∀ t, β * n * q ^ 2 / 2 ≤ (ccount (J t) (dep t) W : ℝ)) := by
  obtain ⟨n₀, hn₀⟩ := sampling_window hq hβ
  refine ⟨n₀, ?_⟩
  intro n hn hκ hτ S J dep hS hJ hsize hload
  exact simultaneous_sample q n (β * n) hq hq1 S J dep
    (fun k => by exact_mod_cast hS k) hJ hsize hload
    (hn₀ n (Fintype.card κ) (Fintype.card τ) hn hκ hτ)

end TypedTriangle.BasalSampling
