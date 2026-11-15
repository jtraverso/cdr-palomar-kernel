/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Pattern.Exists

/-!
# k-bicoloured Latin patterns close to an admissible profile (main statement)

See `CDRBicolour.KBicolor.Pattern.Exists` for the construction.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Pattern

open Finset

variable {k : ℕ}

theorem sum_conePt (E : Finset (Fin k)) (hE : #E = 3) (c : Fin k → ℕ) (q : ℕ) :
    ∑ P, conePt E c q P = 3 * q + 6 * (∑ Q ∈ univ \ E, c Q) * ∑ P, c P := by
  unfold conePt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter,
    show univ.filter (· ∈ E) = E by ext; simp, Finset.sum_const, hE, smul_eq_mul]

/-- Arithmetic of the bumped quadratic form (clean context). -/
theorem ar_q {D k j δ q0 t : ℝ} (hD1 : (k : ℝ) ^ 2 + 1 ≤ D) (hk0 : 0 ≤ k) (hδ : 0 < δ)
    (hj : 4 / δ + 3 ≤ j) (hq0 : -6 * D - k ^ 2 ≤ q0) (hq1 : q0 ≤ 2 * D + 3 * k + 2 * D * k)
    (ht0 : D * δ - 3 ≤ t) (ht1 : t ≤ 3 * D) :
    0 ≤ q0 + 2 * j * t + 2 * j ^ 2 ∧
      q0 + 2 * j * t + 2 * j ^ 2 ≤ (2 + 5 * k + 6 * j + 2 * j ^ 2) * D := by
  have hj3 : 3 ≤ j := by have : 0 ≤ 4 / δ := by positivity
                         linarith
  have hjδ : 4 ≤ j * δ := by
    have h := mul_le_mul_of_nonneg_right hj hδ.le
    rw [add_mul, div_mul_cancel₀ _ hδ.ne'] at h
    nlinarith
  have hD0 : 1 ≤ D := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Clean arithmetic: the cone error. -/
theorem ar_b1 {q σ S C D δ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ C * D) (hσ : D * δ / 2 ≤ σ)
    (hS : D / 2 ≤ S) (hD : 0 < D) (hδ : 0 < δ) : q / (2 * σ * S) ≤ 2 * C / (δ * D) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : D * δ / 2 * (D / 2) ≤ σ * S := mul_le_mul hσ hS (by positivity) hσ0.le
  have hC : 0 ≤ C := by
    by_contra h; push Not at h; nlinarith
  calc q * (δ * D) ≤ C * D * (δ * D) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = 2 * C * (2 * (D * δ / 2 * (D / 2))) := by ring
    _ ≤ 2 * C * (2 * σ * S) := by nlinarith

/-- Clean arithmetic: the final error budget. -/
theorem ar_fin {C δ D ε' K : ℝ} (hδ : 0 < δ) (hD : 0 < D) (hε : 0 < ε')
    (h : (2 * C / δ + 2 * K) / ε' ≤ D) : 2 * C / (δ * D) + 2 * K / D ≤ ε' := by
  rw [div_le_iff₀ hε] at h
  have e : 2 * C / (δ * D) + 2 * K / D = (2 * C / δ + 2 * K) / D := by field_simp
  rw [e, div_le_iff₀ hD]; linarith

/-- Explicit rounding index used in the bounded-pattern construction. -/
noncomputable def patternRoundingIndex (δ : ℝ) : ℕ := ⌈4 / δ + 3⌉₊

noncomputable def patternAccuracy (k : ℕ) (δ η ε : ℝ) : ℝ :=
  min ε (η * δ ^ 2 / (24 * (k : ℝ) ^ 2))

noncomputable def patternRoundingCost (k : ℕ) (δ : ℝ) : ℝ :=
  2 + 5 * k + 6 * patternRoundingIndex δ + 2 * (patternRoundingIndex δ : ℝ) ^ 2

/-- Specified finite scale; there is no choice of an unspecified large integer. -/
noncomputable def patternScale (k : ℕ) (δ η ε : ℝ) : ℕ :=
  ⌈((k : ℝ) ^ 2 + 1) + 2 * (k : ℝ) + (2 / δ + 2) +
    (2 * patternRoundingCost k δ / δ +
      2 * (1 + k + 2 * patternRoundingIndex δ)) / patternAccuracy k δ η ε⌉₊

noncomputable def patternOrderBound (k : ℕ) (δ η ε : ℝ) : ℕ :=
  ⌈3 * patternRoundingCost k δ * patternScale k δ η ε⌉₊ +
    6 * (patternScale k δ η ε + patternRoundingIndex δ) *
      (patternScale k δ η ε + patternRoundingIndex δ)

noncomputable def patternInputThreshold (k : ℕ) (δ η ε : ℝ) : ℕ :=
  max (max (patternScale k δ η ε) ⌈4 / (η * δ ^ 2)⌉₊) 1

set_option maxHeartbeats 1000000 in
theorem exists_pattern_explicit (hG : PaperIII.GaleInt) (hk : 4 ≤ k) {δ η ε : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ (n : ℕ) (c : Fin k → ℕ), patternInputThreshold k δ η ε ≤ n → ∑ P, c P = n →
      3 * ∑ P, (c P : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n → (∀ P, δ * n ≤ c P) →
      (∃ a, SeedData c η a) →
      ∃ m : Fin k → ℕ, (∀ P, 1 ≤ m P) ∧ ∑ P, m P ≤ patternOrderBound k δ η ε ∧
        3 * ∑ P, m P ^ 2 = (∑ P, m P) ^ 2 ∧
        (∀ P, |(m P : ℝ) / (∑ Q, m Q : ℕ) - c P / n| ≤ ε) ∧ ∃ x, IsTour m x := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  set ε' : ℝ := min ε (η * δ ^ 2 / (24 * (k : ℝ) ^ 2)) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by positivity)
  have hε'1 : ε' ≤ ε := min_le_left _ _
  have hε'2 : 6 * (k : ℝ) ^ 2 * ε' ≤ η * δ ^ 2 / 4 := by
    have h := min_le_right ε (η * δ ^ 2 / (24 * (k : ℝ) ^ 2))
    rw [← hε'] at h
    have hk2 : 0 < (k : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  let j := patternRoundingIndex δ
  have hj : 4 / δ + 3 ≤ (j : ℝ) := Nat.le_ceil _
  set C : ℝ := 2 + 5 * k + 6 * j + 2 * (j : ℝ) ^ 2 with hC
  have hC0 : 0 < C := by positivity
  set T4 : ℝ := (2 * C / δ + 2 * (1 + k + 2 * j)) / ε' with hT4
  have hT40 : 0 ≤ T4 := by positivity
  let D := patternScale k δ η ε
  have hD : ((k : ℝ) ^ 2 + 1) + 2 * (k : ℝ) + (2 / δ + 2) + T4 ≤ (D : ℝ) := Nat.le_ceil _
  have h2δ : 0 ≤ 2 / δ := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hD1 : (k : ℝ) ^ 2 + 1 ≤ D := by nlinarith
  have hD2 : 2 * (k : ℝ) ≤ D := by nlinarith
  have hD3 : 2 / δ + 2 ≤ (D : ℝ) := by nlinarith
  have hD4 : T4 ≤ (D : ℝ) := by nlinarith
  have hDpos : (0 : ℝ) < D := by nlinarith
  have hDδ : 2 ≤ (D : ℝ) * δ := by
    have h := mul_le_mul_of_nonneg_right hD3 hδ.le
    rw [add_mul, div_mul_cancel₀ _ hδ.ne'] at h
    nlinarith
  let n1 : ℕ := ⌈4 / (η * δ ^ 2)⌉₊
  have hn1 : 4 / (η * δ ^ 2) ≤ (n1 : ℝ) := Nat.le_ceil _
  have hOrder : patternOrderBound k δ η ε = ⌈3 * C * D⌉₊ + 6 * (D + j) * (D + j) := rfl
  have hThreshold : patternInputThreshold k δ η ε = max (max D n1) 1 := rfl
  rw [hOrder, hThreshold]
  intro n c hn hsum hsq hcls ⟨a, hs⟩
  have hnD : D ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1' : n1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : 0 < n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnDR : (D : ℝ) ≤ n := by exact_mod_cast hnD
  have hsumR : ∑ P, (c P : ℝ) = n := by exact_mod_cast hsum
  have hcn : ∀ P, (c P : ℝ) ≤ n := fun P => by
    rw [← hsumR]; exact Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (mem_univ P)
  -- the scaled profile
  set u : Fin k → ℝ := fun P => (D : ℝ) * c P / n with hu
  have hu0 : ∀ P, 0 ≤ u P := fun P => by positivity
  have huD : ∀ P, u P ≤ D := fun P => by
    simp only [hu]; rw [div_le_iff₀ hnR]; exact mul_le_mul_of_nonneg_left (hcn P) (by positivity)
  have hU1 : ∑ P, u P = D := by
    simp only [hu, ← Finset.sum_div, ← Finset.mul_sum, hsumR]; field_simp
  have hU2 : 3 * ∑ P, u P ^ 2 = (D : ℝ) ^ 2 + 2 * (D : ℝ) ^ 2 / n := by
    have e : ∑ P, u P ^ 2 = ((D : ℝ) / n) ^ 2 * ∑ P, (c P : ℝ) ^ 2 := by
      simp only [hu, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    have : 3 * (((D : ℝ) / n) ^ 2 * ∑ P, (c P : ℝ) ^ 2) = ((D : ℝ) / n) ^ 2 * (n ^ 2 + 2 * n) := by
      rw [← hsq]; ring
    rw [this]; field_simp
  have huδ : ∀ P, (D : ℝ) * δ ≤ u P := fun P => by
    simp only [hu]; rw [le_div_iff₀ hnR]
    calc (D : ℝ) * δ * n = D * (δ * n) := by ring
      _ ≤ D * c P := mul_le_mul_of_nonneg_left (hcls P) (by positivity)
  -- rounding
  set xN : Fin k → ℕ := fun P => ⌊u P⌋₊ with hxN
  have hxu : ∀ P, (xN P : ℝ) ≤ u P := fun P => Nat.floor_le (hu0 P)
  have hux : ∀ P, u P < (xN P : ℝ) + 1 := fun P => Nat.lt_floor_add_one _
  have hx1 : ∀ P, 1 ≤ xN P := fun P => Nat.le_floor (by push_cast; linarith [huδ P])
  obtain ⟨M, hM⟩ := exists_big_class hk hδ.le hsum hsq hcls
  set cN : Fin k → ℕ := fun P => xN P + if P = M then j else 0 with hcN
  have hcR : (fun P => (cN P : ℝ)) = fun P => (xN P : ℝ) + if P = M then (j : ℝ) else 0 := by
    funext P; simp only [hcN]; push_cast; split_ifs <;> simp
  obtain ⟨hql, hqu⟩ := qf_round u (fun P => (xN P : ℝ)) hnR hnDR hDpos.le hxu hux hu0 hU1 hU2
  have hbump := qf_bump (fun P => (xN P : ℝ)) M (j : ℝ)
  rw [← hcR] at hbump
  have hsx : ∑ P, (xN P : ℝ) ≤ D := by
    rw [← hU1]; exact Finset.sum_le_sum fun P _ => hxu P
  have hsx0 : 0 ≤ ∑ P, (xN P : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hsxk : (D : ℝ) - k ≤ ∑ P, (xN P : ℝ) := by
    have : ∑ P, u P ≤ ∑ P, ((xN P : ℝ) + 1) := Finset.sum_le_sum fun P _ => (hux P).le
    rw [Finset.sum_add_distrib, hU1] at this; simp at this; linarith
  have ht0 : (D : ℝ) * δ - 3 ≤ 3 * (xN M : ℝ) - ∑ P, (xN P : ℝ) := by
    have h3u : (D : ℝ) * (1 + δ) ≤ 3 * u M := by
      simp only [hu]
      rw [show 3 * ((D : ℝ) * c M / n) = D * (3 * c M) / n by ring, le_div_iff₀ hnR]
      calc (D : ℝ) * (1 + δ) * n = D * ((1 + δ) * n) := by ring
        _ ≤ D * (3 * c M) := mul_le_mul_of_nonneg_left hM (by positivity)
    have := hux M
    linarith
  have ht1 : 3 * (xN M : ℝ) - ∑ P, (xN P : ℝ) ≤ 3 * D := by linarith [hxu M, huD M]
  obtain ⟨hq0, hqC⟩ := ar_q hD1 (Nat.cast_nonneg k) hδ hj hql hqu ht0 ht1
  rw [← hbump] at hq0 hqC
  -- the integer form `q`
  set Qz : ℤ := 3 * ∑ P, (cN P : ℤ) ^ 2 - (∑ P, (cN P : ℤ)) ^ 2 with hQz
  have hQzR : (Qz : ℝ) = qf (fun P => (cN P : ℝ)) := by simp only [hQz, qf]; push_cast; rfl
  have hQz0 : 0 ≤ Qz := by exact_mod_cast (hQzR ▸ hq0 : (0 : ℝ) ≤ Qz)
  set q : ℕ := Qz.toNat with hq
  have hqZ : (q : ℤ) = Qz := Int.toNat_of_nonneg hQz0
  have hqR : (q : ℝ) ≤ C * D := by
    have : (q : ℝ) = (Qz : ℝ) := by exact_mod_cast hqZ
    rw [this, hQzR]; exact hqC
  -- the cone point
  set E := E3 (by omega : 3 ≤ k) with hEdef
  have hE : #E = 3 := card_E3 _
  set m : Fin k → ℕ := conePt E cN q with hm
  have hcone : 3 * ∑ P, m P ^ 2 = (∑ P, m P) ^ 2 := cone_point E hE cN q (by rw [hqZ])
  set σ' : ℕ := ∑ Q ∈ univ \ E, cN Q with hσ'
  have h3 : (⟨3, by omega⟩ : Fin k) ∈ univ \ E := by
    simp only [Finset.mem_sdiff, mem_univ, true_and]; exact not_mem_E3 hk
  have hσ'x : xN ⟨3, by omega⟩ ≤ σ' :=
    le_trans (Nat.le_add_right _ _) (Finset.single_le_sum (f := cN) (fun _ _ => Nat.zero_le _) h3)
  have hσ'1 : 1 ≤ σ' := le_trans (hx1 _) hσ'x
  have hσ'R : (D : ℝ) * δ / 2 ≤ σ' := by
    have h1 : ((xN ⟨3, by omega⟩ : ℕ) : ℝ) ≤ σ' := by exact_mod_cast hσ'x
    have h2 := hux ⟨3, by omega⟩
    have h3' := huδ ⟨3, by omega⟩
    linarith
  have hS1R : ((∑ P, cN P : ℕ) : ℝ) = ∑ P, (xN P : ℝ) + j := by
    push_cast; simp only [hcN]; push_cast
    rw [Finset.sum_add_distrib]; simp
  have hσS : σ' ≤ ∑ P, cN P :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  -- m ≥ 1
  have hm1 : ∀ P, 1 ≤ m P := by
    intro P
    have : 1 ≤ cN P := le_trans (hx1 P) (Nat.le_add_right _ _)
    have h6 : 1 ≤ 6 * σ' * cN P := by
      calc 1 ≤ 6 * 1 * 1 := by norm_num
        _ ≤ 6 * σ' * cN P := by gcongr
    exact le_trans h6 (Nat.le_add_left _ _)
  have hcloseAll : ∀ P, |(m P : ℝ) / ((∑ Q, m Q : ℕ) : ℝ) - c P / n| ≤ ε' := by
    intro P
    have hclose1 := cone_point_close E hE cN q (by omega) (by
      have := hx1 P; have : 1 ≤ cN P := le_trans this (Nat.le_add_right _ _)
      exact lt_of_lt_of_le (by omega) (Finset.single_le_sum (f := cN) (fun _ _ => Nat.zero_le _)
        (mem_univ P))) P
    rw [← hm] at hclose1
    have hS2 : (D : ℝ) / 2 ≤ ∑ Q, (xN Q : ℝ) + j := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith
    have hclose2 := round_close (u := u) (x := fun P => (xN P : ℝ)) M P hDpos (Nat.cast_nonneg j)
      hxu hux hu0 huD hU1 hS2
    have hcP : (c P : ℝ) / n = u P / D := by simp only [hu]; field_simp
    have hcNP : (cN P : ℝ) = (xN P : ℝ) + if P = M then (j : ℝ) else 0 := congrFun hcR P
    rw [hcNP, hS1R] at hclose1
    rw [hcP]
    -- bound the first error by 2C/(δ D)
    have hb1 : (q : ℝ) / (2 * (σ' : ℝ) * (∑ Q, (xN Q : ℝ) + j)) ≤ 2 * C / (δ * D) :=
      ar_b1 (Nat.cast_nonneg _) hqR hσ'R hS2 hDpos hδ
    have hfin : 2 * C / (δ * D) + 2 * (1 + k + 2 * j) / D ≤ ε' := ar_fin hδ hDpos hε'0 hD4
    calc |(m P : ℝ) / ((∑ Q, m Q : ℕ) : ℝ) - u P / D|
        ≤ |(m P : ℝ) / ((∑ Q, m Q : ℕ) : ℝ) - ((xN P : ℝ) + if P = M then (j : ℝ) else 0) /
            (∑ Q, (xN Q : ℝ) + j)| +
          |((xN P : ℝ) + if P = M then (j : ℝ) else 0) / (∑ Q, (xN Q : ℝ) + j) - u P / D| :=
          abs_sub_le _ _ _
      _ ≤ 2 * C / (δ * D) + 2 * (1 + k + 2 * j) / D := by
          gcongr
          · exact hclose1.trans (by rw [hS1R] at *; exact hb1)
      _ ≤ ε' := hfin
  refine ⟨m, hm1, ?_, hcone, ?_, ?_⟩
  · -- bounded order
    have hN := sum_conePt E hE cN q
    rw [← hm] at hN
    have hS : ((∑ P, cN P : ℕ) : ℝ) ≤ D + j := by rw [hS1R]; linarith
    have hσR : (σ' : ℝ) ≤ D + j := le_trans (by exact_mod_cast hσS) hS
    have hNR : ((∑ P, m P : ℕ) : ℝ) ≤ 3 * C * D + 6 * (D + j) * (D + j) := by
      have hNe : ((∑ P, m P : ℕ) : ℝ) = 3 * (q : ℝ) + 6 * ((σ' : ℝ) * ((∑ P, cN P : ℕ) : ℝ)) := by
        rw [hN, hσ']; push_cast; ring
      have h1 : (σ' : ℝ) * ((∑ P, cN P : ℕ) : ℝ) ≤ (D + j) * (D + j) :=
        mul_le_mul hσR hS (Nat.cast_nonneg _) (by positivity)
      rw [hNe]
      linarith
    have hceil : 3 * C * D ≤ (⌈3 * C * D⌉₊ : ℝ) := Nat.le_ceil _
    have : ((∑ P, m P : ℕ) : ℝ) ≤ (⌈3 * C * D⌉₊ : ℝ) + 6 * (D + j) * (D + j) := by linarith
    exact_mod_cast this
  · exact fun P => (hcloseAll P).trans hε'1
  · -- the tournament
    refine exists_tour hG m hcone fun S => ?_
    by_cases hS0 : S = ∅
    · subst hS0; simp [cutZ]
    by_cases hSu : S = univ
    · subst hSu; rw [cutZ_univ m hcone]
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.2 hS0
    obtain ⟨Q, hQ⟩ : ∃ Q, Q ∉ S := by
      by_contra h; push Not at h; exact hSu (Finset.eq_univ_of_forall h)
    set N : ℝ := ((∑ Q, m Q : ℕ) : ℝ) with hNdef
    have hNpos : 0 < N := by
      have : 1 ≤ ∑ Q, m Q := le_trans (hm1 P) (Finset.single_le_sum (f := m)
        (fun _ _ => Nat.zero_le _) (mem_univ P))
      rw [hNdef]; exact_mod_cast this
    set v : Fin k → ℝ := fun P => (m P : ℝ) / N with hv
    have hv1 : ∀ P, |v P| ≤ 1 := by
      intro P
      rw [abs_of_nonneg (by positivity), hv, div_le_one hNpos, hNdef]
      exact_mod_cast Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (mem_univ P)
    have hvc : ∀ P, |v P - c P / n| ≤ ε' := fun P => hcloseAll P
    have hcut := cut_proper hs hnpos hδ hη hcls hsum (le_trans hn1 (by exact_mod_cast hn1'))
      hε'0.le hε'2 hv1 hvc S hP hQ
    have e : (cutZ S m : ℝ) = N ^ 2 * cutR S v := by
      rw [cutZ_eq, ← cutR_smul]; congr 1; funext P; simp only [hv]; field_simp
    have : (cutZ S m : ℝ) ≤ 0 := by
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hcut
    exact_mod_cast this


/-- Original API, now with the witnesses fixed by the explicit integer formulas above. -/
theorem exists_pattern (hG : PaperIII.GaleInt) (hk : 4 ≤ k) {δ η ε : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ B : ℕ, ∃ n₀ : ℕ, ∀ (n : ℕ) (c : Fin k → ℕ), n₀ ≤ n → ∑ P, c P = n →
      3 * ∑ P, (c P : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n → (∀ P, δ * n ≤ c P) →
      (∃ a, SeedData c η a) →
      ∃ m : Fin k → ℕ, (∀ P, 1 ≤ m P) ∧ ∑ P, m P ≤ B ∧
        3 * ∑ P, m P ^ 2 = (∑ P, m P) ^ 2 ∧
        (∀ P, |(m P : ℝ) / (∑ Q, m Q : ℕ) - c P / n| ≤ ε) ∧ ∃ x, IsTour m x :=
  ⟨patternOrderBound k δ η ε, patternInputThreshold k δ η ε,
    exists_pattern_explicit hG hk hδ hη hε⟩

end CDRBicolour.KBicolor.Pattern
