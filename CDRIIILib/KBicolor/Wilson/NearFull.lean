/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.Placement

/-!
# Near-full Wilson placements from bounded Latin patterns

For fixed `g ≥ 1` and a reserved fraction `0 < ρ ≤ 1/2`, every sufficiently large
robust profile admits a Wilson setup covering at least `(1-ρ)n` points. Its
pattern order is uniformly bounded, and the free Latin squares have order at
least `n / (4gB)`. No decomposition of the residual is assumed in this result.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset

variable {k g : ℕ}

theorem exists_near_full_setup (hk : 4 ≤ k) (hg : 1 ≤ g) {δ η ρ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      3 * ∑ P, (ksz lab P : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n →
      (∀ P, δ * n ≤ ksz lab P) → (∃ a, SeedData (ksz lab) η a) →
      ∃ (m : Fin k → ℕ) (t : ℕ), (∀ P, 1 ≤ m P) ∧ ∑ P, m P ≤ B ∧
        (1 - ρ) * n ≤ ((g * (∑ P, m P) * t : ℕ) : ℝ) ∧
        (n : ℝ) / (4 * g * B) ≤ t ∧
        Nonempty (Setup lab (fun x : (Σ P, Fin (m P)) => x.1) g t) := by
  have hε : 0 < ρ * δ / 4 := by positivity
  obtain ⟨B₀, nP, hP⟩ := Pattern.exists_kbls hk hδ hη hε
  let B := max B₀ 1
  have hB : 1 ≤ B := le_max_right _ _
  have hBR : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hgR : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg)
  refine ⟨B, hB, max nP (max 1 ⌈4 * (g : ℝ) * B / ρ⌉₊),
    fun n lab hn hsq hcls hseed => ?_⟩
  have hnP : nP ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) (le_of_max_le_right hn)
  have hnceil : ⌈4 * (g : ℝ) * B / ρ⌉₊ ≤ n :=
    le_trans (le_max_right _ _) (le_of_max_le_right hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnlarge : 4 * (g : ℝ) * B / ρ ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnceil)
  have hsum : ∑ P, ksz lab P = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  obtain ⟨m, hm, hmB, hclose, τ, hrow, hcol, hbic⟩ :=
    hP n (ksz lab) hnP hsum hsq hcls hseed
  let N := ∑ P, m P
  have hN1 : 1 ≤ N := by
    have hi := hm ⟨0, by omega⟩
    have hsingle : m ⟨0, by omega⟩ ≤ N :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
    omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hNB : N ≤ B := hmB.trans (le_max_left _ _)
  have hNBR : (N : ℝ) ≤ B := by exact_mod_cast hNB
  let t := ⌊(1 - ρ / 2) * n / ((g : ℝ) * N)⌋₊
  have harg : 0 ≤ (1 - ρ / 2) * n / ((g : ℝ) * N) :=
    div_nonneg (mul_nonneg (by linarith) hnR.le) (by positivity)
  have htlo : (1 - ρ / 2) * n / ((g : ℝ) * N) - 1 < t :=
    Nat.sub_one_lt_floor _
  have hthi : (t : ℝ) ≤ (1 - ρ / 2) * n / ((g : ℝ) * N) := Nat.floor_le harg
  have hmult : (g : ℝ) * N * t ≤ (1 - ρ / 2) * n :=
    by nlinarith [(le_div_iff₀ (mul_pos hgR hNR)).mp hthi]
  have hsmall : (g : ℝ) * N ≤ ρ * n / 4 := by
    have hgn : (g : ℝ) * N ≤ g * B := mul_le_mul_of_nonneg_left hNBR hgR.le
    have := (div_le_iff₀ hρ).mp hnlarge
    linarith
  have hcovered : (1 - ρ) * n ≤ (g : ℝ) * N * t := by
    have hfloor := (div_lt_iff₀ (mul_pos hgR hNR)).mp (show
      (1 - ρ / 2) * n / ((g : ℝ) * N) < (t : ℝ) + 1 by linarith)
    nlinarith
  have htlin : (n : ℝ) / (4 * g * B) ≤ t := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * g * B)).mpr
    have hgn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNBR hgR.le) (Nat.cast_nonneg t)
    have hhalf : (n : ℝ) / 2 ≤ (g : ℝ) * N * t := by nlinarith
    nlinarith
  refine ⟨m, t, hm, hNB, ?_, htlin, ?_⟩
  · exact_mod_cast hcovered
  · apply exists_setup lab (fun x : (Σ P, Fin (m P)) => x.1) τ hrow hcol hbic
    intro X
    rw [Pattern.csize_sigma]
    apply proportional_fit (N := N) (n := n) (δ := δ) (ε := ρ * δ / 4) (ρ := ρ / 2)
      (by omega) (by omega) hδ.le (by positivity) (by linarith) (by positivity)
      (by nlinarith) (hcls X) (by
        have hcl := (abs_le.mp (hclose X)).2
        change (m X : ℝ) / N - (ksz lab X : ℝ) / n ≤ ρ * δ / 4 at hcl
        linarith)
    exact_mod_cast (by nlinarith [hmult] : (g : ℝ) * t * N ≤ (1 - ρ / 2) * n)

end CDRBicolour.KBicolor.Wilson
