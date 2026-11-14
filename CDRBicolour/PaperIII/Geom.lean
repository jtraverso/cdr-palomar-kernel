/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.Near

/-!
# T4: the geometric profiles

For `k = m + 2`, `m ≥ 3`: `p = (A, B, r, r/2, r/4, …, r/2^{m-1})` with `B = A + r/2` (so
`p 0 + p 2 = p 1 + p 3`), `A + B + r s = 1` and `A² + B² + r² s₂ = 1/3`, where `s = Σ_{j<m} 2^{-j}`
and `s₂ = Σ_{j<m} 4^{-j}`. The radius `r ∈ [0.09, 0.13]` comes from the intermediate value
theorem, uniformly in `m`.

Criterion `(Σ_S p)² < 3 Σ_S p²` for every proper nonempty `S`:
* tail subsets: `tail_ineq`, induction on the minimum (the rest of a dyadic tail sums to less
  than its first term);
* sets containing exactly one of the two big classes: the big class exceeds `2r`;
* sets containing both: by the global identities the defect equals `r P_D (2 - r P_D) - 3 r² Q_D`
  for the missing tail part `D ≠ ∅`, positive because `5 r < 2`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

open Finset

/-! ### Dyadic tails -/

theorem geom_Ioc (a : ℕ) : ∀ M, a ≤ M → ∑ n ∈ Ioc a M, ((1 : ℝ) / 2) ^ n = (1 / 2) ^ a - (1 / 2) ^ M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top hM, ih, pow_succ]; ring

theorem tail_lt (a : ℕ) (s : Finset ℕ) (hs : ∀ x ∈ s, a < x) :
    ∑ n ∈ s, ((1 : ℝ) / 2) ^ n < (1 / 2) ^ a := by
  set M := a + s.sup id with hM
  have hsub : s ⊆ Ioc a M := by
    intro x hx
    rw [mem_Ioc]
    exact ⟨hs x hx, by have := le_sup (f := id) hx; simp only [id] at this; omega⟩
  calc ∑ n ∈ s, ((1 : ℝ) / 2) ^ n ≤ ∑ n ∈ Ioc a M, ((1 : ℝ) / 2) ^ n :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (1 / 2) ^ a - (1 / 2) ^ M := geom_Ioc a M (by omega)
    _ < (1 / 2) ^ a := by have : (0 : ℝ) < (1 / 2) ^ M := by positivity
                          linarith

/-- **Dyadic tail inequality.** -/
theorem tail_ineq (J : Finset ℕ) :
    (∑ j ∈ J, ((1 : ℝ) / 2) ^ j) ^ 2 ≤ 3 * ∑ j ∈ J, (((1 : ℝ) / 2) ^ j) ^ 2 ∧
      (J.Nonempty → (∑ j ∈ J, ((1 : ℝ) / 2) ^ j) ^ 2 < 3 * ∑ j ∈ J, (((1 : ℝ) / 2) ^ j) ^ 2) := by
  induction J using Finset.induction_on_min with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert ha, sum_insert ha]
    have hP := tail_lt a s hlt
    have hP0 : 0 ≤ ∑ n ∈ s, ((1 : ℝ) / 2) ^ n := sum_nonneg fun _ _ => by positivity
    have hy : (0 : ℝ) < (1 / 2) ^ a := by positivity
    have h1 := ih.1
    have strict : ((1 / 2 : ℝ) ^ a + ∑ j ∈ s, ((1 : ℝ) / 2) ^ j) ^ 2 <
        3 * (((1 / 2 : ℝ) ^ a) ^ 2 + ∑ j ∈ s, (((1 : ℝ) / 2) ^ j) ^ 2) := by
      nlinarith [mul_lt_mul_of_pos_left hP hy]
    exact ⟨strict.le, fun _ => strict⟩

theorem tail_sq_le (J : Finset ℕ) :
    ∑ j ∈ J, (((1 : ℝ) / 2) ^ j) ^ 2 ≤ ∑ j ∈ J, ((1 : ℝ) / 2) ^ j := by
  refine sum_le_sum fun j _ => ?_
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
  have h1 : ((1 : ℝ) / 2) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem tail_pos (J : Finset ℕ) (hJ : J.Nonempty) : 0 < ∑ j ∈ J, ((1 : ℝ) / 2) ^ j :=
  sum_pos (fun _ _ => by positivity) hJ

theorem tail_le_range (m : ℕ) (J : Finset ℕ) (hJ : J ⊆ range m) :
    ∑ j ∈ J, ((1 : ℝ) / 2) ^ j ≤ ∑ j ∈ range m, ((1 : ℝ) / 2) ^ j :=
  sum_le_sum_of_subset_of_nonneg hJ fun _ _ _ => by positivity

theorem range_geom (m : ℕ) : ∑ j ∈ range m, ((1 : ℝ) / 2) ^ j = 2 - 2 * (1 / 2) ^ m := by
  rw [geom_sum_eq (by norm_num)]; ring

theorem range_geom2 (m : ℕ) :
    ∑ j ∈ range m, (((1 : ℝ) / 2) ^ j) ^ 2 = 4 / 3 - 4 / 3 * (1 / 4) ^ m := by
  have e : ∀ j : ℕ, (((1 : ℝ) / 2) ^ j) ^ 2 = (1 / 4) ^ j := fun j => by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  simp only [e]
  rw [geom_sum_eq (by norm_num)]; ring

/-! ### The profile -/

/-- The geometric profile on `Fin (m + 2)`. -/
def gprof (m : ℕ) (A r : ℝ) : Fin (m + 2) → ℝ :=
  Fin.cons A (Fin.cons (A + r / 2) (fun i : Fin m => r * (1 / 2) ^ (i : ℕ)))

/-- Splitting a subset sum over `Fin (m + 2)`. -/
theorem sum_split {m : ℕ} (f : Fin (m + 2) → ℝ) (S : Finset (Fin (m + 2))) :
    ∑ X ∈ S, f X = (if 0 ∈ S then f 0 else 0) + ((if Fin.succ 0 ∈ S then f (Fin.succ 0) else 0) +
      ∑ i : Fin m, (if i.succ.succ ∈ S then f i.succ.succ else 0)) := by
  classical
  have : ∑ X ∈ S, f X = ∑ X, if X ∈ S then f X else 0 := by
    rw [← sum_filter]; congr 1; ext X; simp
  rw [this, Fin.sum_univ_succ, Fin.sum_univ_succ]

/-- The tail index set of `S`. -/
def tailJ {m : ℕ} (S : Finset (Fin (m + 2))) : Finset ℕ :=
  (univ.filter (fun i : Fin m => i.succ.succ ∈ S)).map Fin.valEmbedding

theorem tailJ_sub {m : ℕ} (S : Finset (Fin (m + 2))) : tailJ S ⊆ range m := by
  intro j hj
  simp only [tailJ, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply] at hj
  obtain ⟨i, -, rfl⟩ := hj
  exact mem_range.2 i.2

theorem tail_sum {m : ℕ} (S : Finset (Fin (m + 2))) (g : ℕ → ℝ) :
    ∑ i : Fin m, (if i.succ.succ ∈ S then g i else 0) = ∑ j ∈ tailJ S, g j := by
  classical
  rw [tailJ, sum_map, ← sum_filter]
  rfl

theorem mem_tailJ {m : ℕ} (S : Finset (Fin (m + 2))) (i : Fin m) :
    (i : ℕ) ∈ tailJ S ↔ i.succ.succ ∈ S := by
  simp only [tailJ, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i', h, hi⟩; rwa [← Fin.ext hi]
  · intro h; exact ⟨i, h, rfl⟩

theorem fin_geom (m : ℕ) (r : ℝ) :
    ∑ i : Fin m, r * (1 / 2 : ℝ) ^ (i : ℕ) = r * ∑ j ∈ range m, ((1 : ℝ) / 2) ^ j := by
  rw [← mul_sum]; congr 1; exact Fin.sum_univ_eq_sum_range (fun j => ((1 : ℝ) / 2) ^ j) m

theorem fin_geom2 (m : ℕ) (r : ℝ) :
    ∑ i : Fin m, (r * (1 / 2 : ℝ) ^ (i : ℕ)) ^ 2 = r ^ 2 * ∑ j ∈ range m, (((1 : ℝ) / 2) ^ j) ^ 2 := by
  rw [mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun j => r ^ 2 * (((1 : ℝ) / 2) ^ j) ^ 2) m]
  exact sum_congr rfl fun i _ => by ring

theorem tail_sum' {m : ℕ} (S : Finset (Fin (m + 2))) (c : ℝ) (e : ℕ) :
    ∑ i : Fin m, (if i.succ.succ ∈ S then c * ((1 : ℝ) / 2) ^ ((i : ℕ) * e) else 0) =
      c * ∑ j ∈ tailJ S, ((1 : ℝ) / 2) ^ (j * e) := by
  exact (tail_sum S (fun j => c * ((1 : ℝ) / 2) ^ (j * e))).trans (Finset.mul_sum _ _ _).symm

set_option maxHeartbeats 1000000 in
/-- **The criterion for the geometric profile.** -/
theorem gprof_crit {m : ℕ} {A r : ℝ} (hr : 0 < r) (hr25 : 5 * r < 2) (hA : 2 * r < A)
    (h1 : ∑ X, gprof m A r X = 1) (h2 : ∑ X, gprof m A r X ^ 2 = 1 / 3)
    (S : Finset (Fin (m + 2))) (hS : S.Nonempty) (hSu : S ≠ univ) :
    (∑ X ∈ S, gprof m A r X) ^ 2 < 3 * ∑ X ∈ S, gprof m A r X ^ 2 := by
  classical
  set J := tailJ S with hJ
  set P := ∑ j ∈ J, ((1 : ℝ) / 2) ^ j with hP
  set Q := ∑ j ∈ J, (((1 : ℝ) / 2) ^ j) ^ 2 with hQ
  set s := ∑ j ∈ range m, ((1 : ℝ) / 2) ^ j with hs
  set s2 := ∑ j ∈ range m, (((1 : ℝ) / 2) ^ j) ^ 2 with hs2
  have eP : ∑ X ∈ S, gprof m A r X =
      (if 0 ∈ S then A else 0) + ((if Fin.succ 0 ∈ S then A + r / 2 else 0) + r * P) := by
    rw [sum_split]
    simp only [gprof, Fin.cons_zero, Fin.cons_succ]
    congr 2
    have := tail_sum' S r 1
    simp only [mul_one] at this
    rw [this]
  have eQ : ∑ X ∈ S, gprof m A r X ^ 2 =
      (if 0 ∈ S then A ^ 2 else 0) +
        ((if Fin.succ 0 ∈ S then (A + r / 2) ^ 2 else 0) + r ^ 2 * Q) := by
    rw [sum_split]
    simp only [gprof, Fin.cons_zero, Fin.cons_succ]
    have e : ∀ i : Fin m, (if i.succ.succ ∈ S then (r * (1 / 2 : ℝ) ^ (i : ℕ)) ^ 2 else 0) =
        (if i.succ.succ ∈ S then r ^ 2 * ((1 : ℝ) / 2) ^ ((i : ℕ) * 2) else 0) := fun i => by
      split_ifs
      · rw [mul_pow, ← pow_mul]
      · rfl
    rw [sum_congr rfl fun i _ => e i, tail_sum' S (r ^ 2) 2, hQ]
    have e2 : ∑ j ∈ tailJ S, ((1 : ℝ) / 2) ^ (j * 2) = ∑ j ∈ tailJ S, (((1 : ℝ) / 2) ^ j) ^ 2 :=
      sum_congr rfl fun j _ => by rw [← pow_mul]
    rw [e2]
  have eP1 : A + (A + r / 2) + r * s = 1 := by
    rw [← h1, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [gprof, Fin.cons_zero, Fin.cons_succ]
    rw [fin_geom]; ring
  have eQ1 : A ^ 2 + (A + r / 2) ^ 2 + r ^ 2 * s2 = 1 / 3 := by
    rw [← h2, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [gprof, Fin.cons_zero, Fin.cons_succ]
    rw [fin_geom2]; ring
  have hPs : P ≤ s := tail_le_range m J (tailJ_sub S)
  have hs2' : s < 2 := by
    rw [hs, range_geom]; have : (0 : ℝ) < (1 / 2) ^ m := by positivity
    linarith
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => by positivity
  have hQP : Q ≤ P := tail_sq_le J
  have ht := tail_ineq J
  have hrP : r * P < 2 * r := by nlinarith
  rw [eP, eQ]
  by_cases h0 : (0 : Fin (m + 2)) ∈ S <;> by_cases h1' : (Fin.succ 0 : Fin (m + 2)) ∈ S <;>
    simp only [h0, h1', ↓reduceIte, zero_add, add_zero]
  · -- both big classes: the missing tail part `D`
    set D := range m \ J with hD
    have hDne : D.Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
      intro hsub
      apply hSu
      ext X
      simp only [mem_univ, iff_true]
      refine Fin.cases h0 (fun Y => Fin.cases h1' (fun i => ?_) Y) X
      exact (mem_tailJ S i).1 (hsub (mem_range.2 i.2))
    have hPD : P = s - ∑ j ∈ D, ((1 : ℝ) / 2) ^ j := by
      rw [hD, sum_sdiff_eq_sub (tailJ_sub S)]; ring
    have hQD : Q = s2 - ∑ j ∈ D, (((1 : ℝ) / 2) ^ j) ^ 2 := by
      rw [hD, sum_sdiff_eq_sub (tailJ_sub S)]; ring
    have hPDpos := tail_pos D hDne
    have hQDle := tail_sq_le D
    have hPDle : ∑ j ∈ D, ((1 : ℝ) / 2) ^ j ≤ s := tail_le_range m D sdiff_subset
    rw [hPD, hQD]
    set PD := ∑ j ∈ D, ((1 : ℝ) / 2) ^ j
    set QD := ∑ j ∈ D, (((1 : ℝ) / 2) ^ j) ^ 2
    have key : 3 * (A ^ 2 + ((A + r / 2) ^ 2 + r ^ 2 * (s2 - QD))) -
        (A + ((A + r / 2) + r * (s - PD))) ^ 2 = r * PD * (2 - r * PD) - 3 * r ^ 2 * QD := by
      linear_combination 3 * eQ1 - (A + (A + r / 2) + r * (s - PD) + 1 - r * PD) * eP1
    have hrPD : r * PD < 2 * r := by nlinarith
    have hq : 3 * r ^ 2 * QD ≤ 3 * r ^ 2 * PD := by nlinarith [sq_nonneg r]
    have : 0 < r * PD * (2 - r * PD) - 3 * r ^ 2 * QD := by nlinarith [mul_pos hr hPDpos]
    linarith
  · -- only `A`
    have hA0 : 0 < A := by linarith
    have e1 := mul_lt_mul_of_pos_left (show r * P < A by linarith) hA0
    have e2 := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg r)
    nlinarith
  · -- only `A + r/2`
    have hB0 : 0 < A + r / 2 := by linarith
    have e1 := mul_lt_mul_of_pos_left (show r * P < A + r / 2 by linarith) hB0
    have e2 := mul_le_mul_of_nonneg_left ht.1 (sq_nonneg r)
    nlinarith
  · -- tail only
    have hJne : J.Nonempty := by
      obtain ⟨X, hX⟩ := hS
      revert hX
      refine Fin.cases (fun h => absurd h h0) (fun Y => Fin.cases (fun h => absurd h h1')
        (fun i h => ⟨i, (mem_tailJ S i).2 h⟩) Y) X
    have := mul_lt_mul_of_pos_left (ht.2 hJne) (pow_pos hr 2)
    nlinarith

/-- **T4.** For every `k ≥ 5` there is a profile satisfying the criterion, with the symmetry
`p 0 + p 2 = p 1 + p 3`. -/
theorem geometric_profile (k : ℕ) (hk : 5 ≤ k) :
    ∃ p : Fin k → ℝ, (∀ X, 0 < p X) ∧ ∑ X, p X = 1 ∧ ∑ X, p X ^ 2 = 1 / 3 ∧
      p ⟨0, by omega⟩ + p ⟨2, by omega⟩ = p ⟨1, by omega⟩ + p ⟨3, by omega⟩ ∧
      p ⟨2, by omega⟩ < p ⟨0, by omega⟩ ∧
      ∀ S : Finset (Fin k), S.Nonempty → S ≠ univ →
        (∑ X ∈ S, p X) ^ 2 < 3 * ∑ X ∈ S, p X ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : 3 ≤ m := by omega
  set s := ∑ j ∈ range m, ((1 : ℝ) / 2) ^ j with hs
  set s2 := ∑ j ∈ range m, (((1 : ℝ) / 2) ^ j) ^ 2 with hs2
  have hhalf : ((1 : ℝ) / 2) ^ m ≤ 1 / 8 := by
    calc ((1 : ℝ) / 2) ^ m ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1 / 8 := by norm_num
  have hquart : ((1 : ℝ) / 4) ^ m ≤ 1 / 64 := by
    calc ((1 : ℝ) / 4) ^ m ≤ (1 / 4) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1 / 64 := by norm_num
  have hs_lo : 7 / 4 ≤ s := by rw [hs, range_geom]; linarith
  have hs_hi : s ≤ 2 := by rw [hs, range_geom]; have : (0 : ℝ) < (1 / 2) ^ m := by positivity
                           linarith
  have hs2_lo : 21 / 16 ≤ s2 := by rw [hs2, range_geom2]; linarith
  have hs2_hi : s2 ≤ 4 / 3 := by rw [hs2, range_geom2]; have : (0 : ℝ) < (1 / 4) ^ m := by positivity
                                 linarith
  -- `A = (1 - r s - r/2)/2`; the equation `F r = 0`
  set F : ℝ → ℝ := fun r => (1 - r * s) ^ 2 / 2 + r ^ 2 / 8 + r ^ 2 * s2 - 1 / 3 with hF
  have hFc : ContinuousOn F (Set.Icc (9 / 100) (13 / 100)) := by
    simp only [hF]; fun_prop
  have hFa : 0 ≤ F (9 / 100) := by simp only [hF]; nlinarith
  have hFb : F (13 / 100) ≤ 0 := by simp only [hF]; nlinarith
  obtain ⟨r, ⟨hr1, hr2⟩, hFr⟩ := intermediate_value_Icc' (by norm_num) hFc ⟨hFb, hFa⟩
  set A := (1 - r * s - r / 2) / 2 with hA
  have hrpos : 0 < r := by linarith
  have hA2r : 2 * r < A := by rw [hA]; nlinarith
  have h1 : ∑ X, gprof m A r X = 1 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [gprof, Fin.cons_zero, Fin.cons_succ]
    rw [fin_geom, ← hs, hA]; ring
  have h2 : ∑ X, gprof m A r X ^ 2 = 1 / 3 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [gprof, Fin.cons_zero, Fin.cons_succ]
    rw [fin_geom2, ← hs2, hA]
    have := hFr; simp only [hF] at this
    linear_combination this
  refine ⟨gprof m A r, fun X => ?_, h1, h2, ?_, ?_, fun S hS hSu =>
    gprof_crit hrpos (by linarith) hA2r h1 h2 S hS hSu⟩
  · refine Fin.cases ?_ (fun Y => Fin.cases ?_ (fun i => ?_) Y) X
    · simp only [gprof, Fin.cons_zero]; linarith
    · simp only [gprof, Fin.cons_succ, Fin.cons_zero]; linarith
    · simp only [gprof, Fin.cons_succ]; positivity
  · show gprof m A r 0 + gprof m A r (Fin.succ (Fin.succ ⟨0, by omega⟩)) =
      gprof m A r 1 + gprof m A r (Fin.succ (Fin.succ ⟨1, by omega⟩))
    simp only [gprof, Fin.cons_zero, Fin.cons_succ, Fin.cons_one]
    norm_num; ring
  · show gprof m A r (Fin.succ (Fin.succ ⟨0, by omega⟩)) < gprof m A r 0
    simp only [gprof, Fin.cons_zero, Fin.cons_succ]
    norm_num; linarith

end CDRBicolour.PaperIII
