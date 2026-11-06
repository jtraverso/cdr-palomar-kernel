/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.RandomCore

@[expose] public section

/-!
# V24 / S07 §2: one-test failure bounds for each family (full finite process)

Each lemma bounds the Bernoulli(`q`) probability that ONE prescribed test fails, with an
exponent linear in `n = |V|` and a rate depending only on the constants:

* `fam_paths` — `a n^m` paths of length `m+1`: fewer than `a q^m n^m / 2` with all internal
  vertices in `W` has probability `≤ exp(-(a q^(2m)/(16 m²)) n)`.
* `fam_pool` — a pool `P` with `|P| ≥ β n`: `|P ∩ W| < qβn/2` has probability
  `≤ exp(-(βq²/16) n)`.
* `fam_size_lo`, `fam_size_hi` — `|W| < qn/2`, resp. `|W| ≥ 2qn`.
* `exp_beats_poly` — `K n^4 e^{-θ n} < 1` once `n > 120 K / θ^5`.
-/

open Finset

namespace S07V24

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fam_paths {a q : ℝ} {m : ℕ} (ha : 0 < a) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < m)
    (hn : 0 < Fintype.card V) (L : SimpleGraph V) [DecidableRel L.Adj] (x y : V)
    (hcount : a * (Fintype.card V : ℝ) ^ m ≤ (pathsLen L (m + 1) x y).card) :
    bprob q univ (fun W => ((pathsIn L m x y W).card : ℝ) <
        a * (Fintype.card V : ℝ) ^ m * q ^ m / 2) ≤
      Real.exp (-(a * q ^ (2 * m) / (16 * m ^ 2) * Fintype.card V)) := by
  set n := Fintype.card V
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set I := pathsLen L (m + 1) x y
  have hle : bprob q univ (fun W => ((pathsIn L m x y W).card : ℝ) <
        a * (n : ℝ) ^ m * q ^ m / 2) ≤
      bprob q univ (fun W => (ccount I (fun p => intlSet m p) W : ℝ) <
        a * (n : ℝ) ^ m * q ^ m / 2) :=
    bprob_mono hq.le hq1 (fun W h => by simpa [ccount, pathsIn] using h)
  refine hle.trans ((count_tail hq hq1 I (fun p => intlSet m p) hm
    (fun p _ => (card_image_le).trans (by simp)) (Δ := m * (n : ℝ) ^ (m - 1))
    (by positivity) ?_ hcount).trans ?_)
  · intro z
    have hA : ∀ p ∈ I, p.length = m + 1 := by
      intro p hp
      simp only [I, pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp
      exact hp.1
    have := card_through_le m x y I hA {z}
    have heq : (I.filter fun p => z ∈ intlSet m p) =
        I.filter fun p => ∃ i : Fin m, intl m p i ∈ ({z} : Finset V) := by
      apply Finset.filter_congr; intro p _; simp [mem_intlSet]
    rw [heq]
    have h2 : ((I.filter fun p => ∃ i : Fin m, intl m p i ∈ ({z} : Finset V)).card : ℝ) ≤
        (({z} : Finset V).card * m * Fintype.card V ^ (m - 1) : ℕ) := by exact_mod_cast this
    push_cast at h2; simpa using h2
  · apply Real.exp_le_exp.2
    have e : a * (n : ℝ) ^ m * q ^ (2 * m) / (16 * (m * (n : ℝ) ^ (m - 1)) * m) =
        a * q ^ (2 * m) / (16 * m ^ 2) * n := by
      have : (n : ℝ) ^ m = (n : ℝ) ^ (m - 1) * n := by
        rw [← pow_succ, Nat.sub_add_cancel hm]
      rw [this]; field_simp
    rw [e]

theorem fam_pool {β q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (P : Finset V)
    (hP : β * Fintype.card V ≤ P.card) :
    bprob q univ (fun W => ((P ∩ W).card : ℝ) < β * Fintype.card V * q ^ 1 / 2) ≤
      Real.exp (-(β * q ^ 2 / 16 * Fintype.card V)) := by
  have := count_tail hq hq1 P (fun a => ({a} : Finset V)) one_pos
    (fun _ _ => by simp) (Δ := 1) one_pos (fun z => by
      have : (P.filter fun a => z ∈ ({a} : Finset V)) ⊆ {z} := by
        intro w hw; simp only [mem_filter, mem_singleton] at hw; simp [hw.2]
      exact_mod_cast (card_le_card this).trans (by simp)) hP
  simp only [ccount_singleton] at this
  refine this.trans (Real.exp_le_exp.2 (le_of_eq ?_))
  push_cast; ring

theorem fam_size_lo {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    bprob q univ (fun W : Finset V => (W.card : ℝ) < Fintype.card V * q ^ 1 / 2) ≤
      Real.exp (-(q ^ 2 / 16 * Fintype.card V)) := by
  have := count_tail hq hq1 (univ : Finset V) (fun a => ({a} : Finset V)) one_pos
    (fun _ _ => by simp) (Δ := 1) one_pos (fun z => by
      have : ((univ : Finset V).filter fun a => z ∈ ({a} : Finset V)) ⊆ {z} := by
        intro w hw; simp only [mem_filter, mem_singleton] at hw; simp [hw.2]
      exact_mod_cast (card_le_card this).trans (by simp))
    (L := Fintype.card V) (by rw [card_univ])
  simp only [ccount_singleton, univ_inter] at this
  refine this.trans (Real.exp_le_exp.2 (le_of_eq ?_))
  push_cast; ring

theorem fam_size_hi {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    bprob q univ (fun W : Finset V => q * Fintype.card V + q * Fintype.card V ≤ (W.card : ℝ)) ≤
      Real.exp (-(q ^ 2 / 4 * Fintype.card V)) := by
  have ht := tail_upper hq.le hq1 (fun _ : V => (1 : ℝ)) (l := q / 2) (by positivity)
    (univ : Finset V)
    (fun W : Finset V => (W.card : ℝ)) (fun W _ a _ haW => by
      simp only [Finset.card_insert_of_notMem haW]; push_cast; simp)
    (fun _ _ => by linarith) (q * Fintype.card V)
  rw [bexp_card] at ht
  refine ht.trans (Real.exp_le_exp.2 (le_of_eq ?_))
  simp only [sum_const, card_univ, nsmul_eq_mul]; ring

/-- `K n^4 e^{-θ n} < 1` for `n > 120 K / θ^5` -/
lemma exp_beats_poly {θ K : ℝ} (hθ : 0 < θ) (hK : 0 < K) {n : ℕ} (hn : 120 * K / θ ^ 5 < n) :
    K * (n : ℝ) ^ 4 * Real.exp (-(θ * n)) < 1 := by
  have hnpos : (0 : ℝ) < n := lt_trans (by positivity) hn
  have hx : 0 ≤ θ * n := by positivity
  have h1 := Real.pow_div_factorial_le_exp (θ * n) hx 5
  norm_num [Nat.factorial] at h1
  have hexp : Real.exp (-(θ * n)) ≤ 120 / (θ * n) ^ 5 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 120)]; linarith
  calc K * (n : ℝ) ^ 4 * Real.exp (-(θ * n)) ≤ K * (n : ℝ) ^ 4 * (120 / (θ * n) ^ 5) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 120 * K / (θ ^ 5 * n) := by field_simp
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hn; linarith

end S07V24
