/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Pattern.Tour
public import CDRBicolour.KBicolor.Host

/-!
# The cut functional: scaling, perturbation and slack from a seed

`cutR S v` is the real form of `cutZ`. Three facts:

* `cutZ_eq` and `cutR_smul`: it is a quadratic form;
* `cutR_close`: it moves by at most `6 k² ε` when `v` moves by `ε` (coordinates in `[-1, 1]`);
* `cutR_seed`: for the class sizes `c` of a profile with an η-seed,
  `cutR S c ≤ c(S) − η c(S) c(Sᶜ)`, which is the slack Gale's theorem needs.

`exists_big_class`: an admissible k-profile (`k ≥ 4`, classes `≥ δn`) has a class with
`3 c_M ≥ (1 + δ) n`.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Pattern

open Finset

variable {k : ℕ}

/-- The cut functional (real form). -/
def cutR (S : Finset (Fin k)) (v : Fin k → ℝ) : ℝ :=
  ∑ P ∈ S, v P ^ 2 - ∑ P ∈ S, ∑ Q ∈ S, (if P < Q then v P * v Q else 0) -
    ∑ P ∈ S, ∑ Q ∈ Sᶜ, v P * v Q

theorem cutZ_eq (S : Finset (Fin k)) (m : Fin k → ℕ) :
    (cutZ S m : ℝ) = cutR S (fun P => (m P : ℝ)) := by
  unfold cutZ cutR
  push_cast
  congr 2
  refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
  unfold x0; split_ifs <;> push_cast <;> rfl

theorem cutR_smul (S : Finset (Fin k)) (v : Fin k → ℝ) (t : ℝ) :
    cutR S (fun P => t * v P) = t ^ 2 * cutR S v := by
  unfold cutR
  have e1 : ∑ P ∈ S, (t * v P) ^ 2 = t ^ 2 * ∑ P ∈ S, v P ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ P ∈ S, ∑ Q ∈ S, (if P < Q then t * v P * (t * v Q) else 0) =
      t ^ 2 * ∑ P ∈ S, ∑ Q ∈ S, (if P < Q then v P * v Q else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Q _ => ?_
    split_ifs <;> ring
  have e3 : ∑ P ∈ S, ∑ Q ∈ Sᶜ, t * v P * (t * v Q) = t ^ 2 * ∑ P ∈ S, ∑ Q ∈ Sᶜ, v P * v Q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun Q _ => by ring
  rw [e1, e2, e3]; ring

theorem abs_sum_le_card {S : Finset (Fin k)} {f : Fin k → ℝ} {B : ℝ} (h : ∀ P, |f P| ≤ B)
    (hB : 0 ≤ B) : |∑ P ∈ S, f P| ≤ k * B := by
  calc |∑ P ∈ S, f P| ≤ ∑ P ∈ S, |f P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _P ∈ S, B := Finset.sum_le_sum fun P _ => h P
    _ = #S * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ k * B := by
      refine mul_le_mul_of_nonneg_right ?_ hB
      have := Finset.card_le_univ S
      rw [Fintype.card_fin] at this
      exact_mod_cast this

theorem prod_close {a b c d ε : ℝ} (ha : |a| ≤ 1) (hd : |d| ≤ 1) (h1 : |a - c| ≤ ε)
    (h2 : |b - d| ≤ ε) : |a * b - c * d| ≤ 2 * ε := by
  have e : a * b - c * d = a * (b - d) + d * (a - c) := by ring
  rw [e]
  calc |a * (b - d) + d * (a - c)| ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * ε + 1 * ε := by
        gcongr
    _ = 2 * ε := by ring

/-- **Perturbation.** -/
theorem cutR_close (S : Finset (Fin k)) {v w : Fin k → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hv : ∀ P, |v P| ≤ 1) (hw : ∀ P, |w P| ≤ 1) (hvw : ∀ P, |v P - w P| ≤ ε) :
    |cutR S v - cutR S w| ≤ 6 * k ^ 2 * ε := by
  have hp : ∀ P Q, |v P * v Q - w P * w Q| ≤ 2 * ε :=
    fun P Q => prod_close (hv P) (hw Q) (hvw P) (hvw Q)
  have e : cutR S v - cutR S w =
      ∑ P ∈ S, (v P * v P - w P * w P) -
      ∑ P ∈ S, ∑ Q ∈ S, ((if P < Q then v P * v Q else 0) - (if P < Q then w P * w Q else 0)) -
      ∑ P ∈ S, ∑ Q ∈ Sᶜ, (v P * v Q - w P * w Q) := by
    unfold cutR
    simp only [Finset.sum_sub_distrib, sq]
    ring
  have b1 : |∑ P ∈ S, (v P * v P - w P * w P)| ≤ k * (2 * ε) :=
    abs_sum_le_card (fun P => hp P P) (by positivity)
  have b2 : |∑ P ∈ S, ∑ Q ∈ S, ((if P < Q then v P * v Q else 0) -
      (if P < Q then w P * w Q else 0))| ≤ k * (k * (2 * ε)) := by
    refine abs_sum_le_card (fun P => abs_sum_le_card (fun Q => ?_) (by positivity)) (by positivity)
    split_ifs
    · exact hp P Q
    · simp; positivity
  have b3 : |∑ P ∈ S, ∑ Q ∈ Sᶜ, (v P * v Q - w P * w Q)| ≤ k * (k * (2 * ε)) :=
    abs_sum_le_card (fun P => abs_sum_le_card (fun Q => hp P Q) (by positivity)) (by positivity)
  rw [e]
  have hk : (k : ℝ) ≤ k ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
  calc |∑ P ∈ S, (v P * v P - w P * w P) -
        ∑ P ∈ S, ∑ Q ∈ S, ((if P < Q then v P * v Q else 0) - (if P < Q then w P * w Q else 0)) -
        ∑ P ∈ S, ∑ Q ∈ Sᶜ, (v P * v Q - w P * w Q)|
      ≤ |∑ P ∈ S, (v P * v P - w P * w P)| +
        |∑ P ∈ S, ∑ Q ∈ S, ((if P < Q then v P * v Q else 0) -
          (if P < Q then w P * w Q else 0))| +
        |∑ P ∈ S, ∑ Q ∈ Sᶜ, (v P * v Q - w P * w Q)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
    _ ≤ k * (2 * ε) + k * (k * (2 * ε)) + k * (k * (2 * ε)) := by linarith
    _ ≤ 6 * k ^ 2 * ε := by nlinarith

/-- **Slack from an η-seed.** -/
theorem cutR_seed {c : Fin k → ℕ} {η : ℝ} {a : Fin k → Fin k → ℝ} (hs : SeedData c η a)
    (S : Finset (Fin k)) :
    cutR S (fun P => (c P : ℝ)) ≤
      ∑ P ∈ S, (c P : ℝ) - η * ((∑ P ∈ S, (c P : ℝ)) * ∑ Q ∈ Sᶜ, (c Q : ℝ)) := by
  obtain ⟨hsym, hge, hrow⟩ := hs
  set g : Fin k → Fin k → ℝ := fun X Y => if X = Y then 0 else (c X : ℝ) * c Y * a X Y with hg
  -- row identities, multiplied by `c X`
  have hrowg : ∀ X, ∑ Y, g X Y = (c X : ℝ) * c X - c X := by
    intro X
    have := congrArg (fun t => (c X : ℝ) * t) (hrow X)
    simp only [Finset.mul_sum] at this
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun Y => Y ≠ X)]
    have e2 : ∑ Y ∈ univ.filter (fun Y => ¬ Y ≠ X), g X Y = 0 :=
      Finset.sum_eq_zero fun Y hY => by
        simp only [Finset.mem_filter, not_not] at hY; simp [hg, hY.2]
    rw [e2, add_zero]
    have e3 : ∑ Y ∈ univ.filter (fun Y => Y ≠ X), g X Y =
        ∑ Y ∈ univ.filter (fun Y => Y ≠ X), (c X : ℝ) * ((c Y : ℝ) * a X Y) :=
      Finset.sum_congr rfl fun Y hY => by
        simp only [Finset.mem_filter] at hY
        simp [hg, Ne.symm hY.2, mul_assoc]
    rw [e3, this]; ring
  -- inside `S`
  have hin : ∑ X ∈ S, ∑ Y ∈ S, g X Y = ∑ X ∈ S, ∑ Y ∈ S, (if X < Y then (c X : ℝ) * c Y else 0) := by
    have split : ∀ X Y, g X Y = (if X < Y then (c X : ℝ) * c Y * a X Y else 0) +
        (if Y < X then (c X : ℝ) * c Y * a X Y else 0) := by
      intro X Y
      rcases lt_trichotomy X Y with h | h | h
      · simp [hg, h, h.ne, not_lt.2 h.le]
      · subst h; simp [hg]
      · simp [hg, h, h.ne', not_lt.2 h.le]
    simp only [split, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun X Y => if Y < X then (c X : ℝ) * c Y * a X Y else 0),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    split_ifs with h
    · have := hsym X Y h.ne
      linear_combination ((c X : ℝ) * c Y) * this
    · simp
  -- across the cut
  have hout : ∑ X ∈ S, ∑ Y ∈ Sᶜ, g X Y ≤ (1 - η) * ∑ X ∈ S, ∑ Y ∈ Sᶜ, (c X : ℝ) * c Y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun X hX => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun Y hY => ?_
    have hne : X ≠ Y := by rintro rfl; exact (Finset.mem_compl.1 hY) hX
    have h1 := hsym X Y hne
    have h2 := hge Y X (Ne.symm hne)
    have hcc : (0 : ℝ) ≤ (c X : ℝ) * c Y := by positivity
    simp only [hg, hne, if_false]
    nlinarith
  have htot : ∑ X ∈ S, ((c X : ℝ) * c X - c X) =
      ∑ X ∈ S, ∑ Y ∈ S, g X Y + ∑ X ∈ S, ∑ Y ∈ Sᶜ, g X Y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [← hrowg X, Finset.sum_add_sum_compl]
  have hprod : (∑ P ∈ S, (c P : ℝ)) * ∑ Q ∈ Sᶜ, (c Q : ℝ) = ∑ X ∈ S, ∑ Y ∈ Sᶜ, (c X : ℝ) * c Y :=
    Finset.sum_mul_sum _ _ _ _
  unfold cutR
  rw [hprod]
  simp only [Finset.sum_sub_distrib, sq] at htot ⊢
  rw [hin] at htot
  linarith

/-- An admissible k-profile with all classes `≥ δ n` has a class with `3 c_M ≥ (1 + δ) n`. -/
theorem exists_big_class (hk : 4 ≤ k) {c : Fin k → ℕ} {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hsum : ∑ P, c P = n) (hsq : 3 * ∑ P, (c P : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n)
    (hcls : ∀ P, δ * n ≤ c P) : ∃ M, (1 + δ) * n ≤ 3 * (c M : ℝ) := by
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨M, -, hM⟩ := Finset.exists_max_image univ (fun P => c P) hne
  refine ⟨M, ?_⟩
  have hsumR : ∑ P, (c P : ℝ) = n := by exact_mod_cast hsum
  -- n c_M ≥ Σ c² = (n² + 2n)/3
  have h1 : ∑ P, (c P : ℝ) ^ 2 ≤ (c M : ℝ) * n := by
    rw [← hsumR, Finset.mul_sum]
    refine Finset.sum_le_sum fun P _ => ?_
    have := hM P (mem_univ _)
    have : (c P : ℝ) ≤ c M := by exact_mod_cast this
    nlinarith [(Nat.cast_nonneg (c P) : (0 : ℝ) ≤ c P)]
  -- Σ c_P (c_M − c_P) ≥ δ n (k c_M − n)
  have h2 : δ * n * ((k : ℝ) * c M - n) ≤ (c M : ℝ) * n - ∑ P, (c P : ℝ) ^ 2 := by
    have e : (c M : ℝ) * n - ∑ P, (c P : ℝ) ^ 2 = ∑ P, (c P : ℝ) * (c M - c P) := by
      rw [← hsumR, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : δ * n * ((k : ℝ) * c M - n) = ∑ P, δ * n * ((c M : ℝ) - c P) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul, hsumR]
    rw [e, e2]
    refine Finset.sum_le_sum fun P _ => ?_
    have := hM P (mem_univ _)
    have : (0 : ℝ) ≤ (c M : ℝ) - c P := by
      have : (c P : ℝ) ≤ c M := by exact_mod_cast this
      linarith
    exact mul_le_mul_of_nonneg_right (hcls P) this
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hcM0 : (0 : ℝ) ≤ c M := Nat.cast_nonneg _
  -- 3 c_M ≥ n + 2
  have h3 : (n : ℝ) ≤ 3 * c M := by
    by_cases hn : (n : ℝ) = 0
    · rw [hn]; positivity
    · have hnpos : 0 < (n : ℝ) := lt_of_le_of_ne hn0 (Ne.symm hn)
      nlinarith
  have h4 : δ * n * (n / 3) ≤ δ * n * ((k : ℝ) * c M - n) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  nlinarith
end CDRBicolour.KBicolor.Pattern
