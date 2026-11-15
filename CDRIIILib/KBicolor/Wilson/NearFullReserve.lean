/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.ReserveSize

/-!
# Near-full Wilson placements with a linear reserve in every colour

For fixed `g ≥ 1` and a reserved fraction `0 < ρ ≤ 1/2`, every sufficiently large
robust profile admits a Wilson setup covering at least `(1-ρ)n` points. Its
pattern order is uniformly bounded, and the free Latin squares have order at
least `n / (4gB)`. The pattern lies exactly on the quadratic cone and approximates the profile to
any prescribed positive accuracy `ξ`. Every colour retains at least `ρδn/4` reserved points. No residual decomposition is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset

variable {k g : ℕ}

/-- Explicit uniform bound on the finite pattern order in the placement. -/
def wilsonPatternBound (k : ℕ) (δ η ρ ξ : ℝ) : ℕ :=
  max (Pattern.patternOrderBound k δ η (min (ρ * δ / 4) ξ)) 1

/-- Explicit order threshold for placement, including a linear reserve per colour. -/
def wilsonPlacementThreshold (k g : ℕ) (δ η ρ ξ : ℝ) : ℕ :=
  max (Pattern.patternInputThreshold k δ η (min (ρ * δ / 4) ξ))
    (max 1 ⌈4 * (g : ℝ) * wilsonPatternBound k δ η ρ ξ / ρ⌉₊)

theorem exists_near_full_setup_reserve_explicit (hk : 4 ≤ k) (hg : 1 ≤ g) {δ η ρ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∀ (n : ℕ) (lab : Fin n → Fin k), wilsonPlacementThreshold k g δ η ρ ξ ≤ n →
      3 * ∑ P, (ksz lab P : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n →
      (∀ P, δ * n ≤ ksz lab P) → (∃ a, SeedData (ksz lab) η a) →
      ∃ (m : Fin k → ℕ) (t : ℕ), (∀ P, 1 ≤ m P) ∧ ∑ P, m P ≤ wilsonPatternBound k δ η ρ ξ ∧
        3 * ∑ P, m P ^ 2 = (∑ P, m P) ^ 2 ∧
        (∀ P, |(m P : ℝ) / (∑ Q, m Q : ℕ) - ksz lab P / n| ≤ ξ) ∧
        (1 - ρ) * n ≤ ((g * (∑ P, m P) * t : ℕ) : ℝ) ∧
        (n : ℝ) / (4 * g * wilsonPatternBound k δ η ρ ξ) ≤ t ∧
        (∃ h : Setup lab (fun x : (Σ P, Fin (m P)) => x.1) g t,
          ∀ X, ρ * δ / 4 * n ≤ #((reserve h).filter fun v => lab v = X)) := by
  have hε : 0 < min (ρ * δ / 4) ξ := lt_min (by positivity) hξ
  let B₀ := Pattern.patternOrderBound k δ η (min (ρ * δ / 4) ξ)
  let nP := Pattern.patternInputThreshold k δ η (min (ρ * δ / 4) ξ)
  have hP := Pattern.exists_pattern_explicit Palomar.galeInt hk hδ hη hε
  let B := max B₀ 1
  have hB : 1 ≤ B := le_max_right _ _
  have hBR : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hgR : (0 : ℝ) < g := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg)
  intro n lab hn hsq hcls hseed
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
  obtain ⟨m, hm, hmB, hcone, hclose, x, hx⟩ :=
    hP n (ksz lab) hnP hsum hsq hcls hseed
  obtain ⟨τ, hrow, hcol, hbic⟩ := Pattern.kbls_of_tournament
    (fun u : (Σ P, Fin (m P)) => u.1) (Pattern.csize_sigma m) hx
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
  refine ⟨m, t, hm, hNB, hcone, (fun P => (hclose P).trans (min_le_right _ _)), ?_, htlin, ?_⟩
  · exact_mod_cast hcovered
  · have hsetup : Nonempty (Setup lab (fun x : (Σ P, Fin (m P)) => x.1) g t) := by
      apply exists_setup lab (fun x : (Σ P, Fin (m P)) => x.1) τ hrow hcol hbic
      intro X
      rw [Pattern.csize_sigma]
      apply proportional_fit (N := N) (n := n) (δ := δ) (ε := ρ * δ / 4) (ρ := ρ / 2)
        (by omega) (by omega) hδ.le (by positivity) (by linarith) (by positivity)
        (by nlinarith) (hcls X) (by
          have hcl := (abs_le.mp (hclose X)).2
          change (m X : ℝ) / N - (ksz lab X : ℝ) / n ≤ min (ρ * δ / 4) ξ at hcl
          linarith [min_le_left (ρ * δ / 4) ξ])
      exact_mod_cast (by nlinarith [hmult] : (g : ℝ) * t * N ≤ (1 - ρ / 2) * n)
    obtain ⟨h⟩ := hsetup
    refine ⟨h, fun X => ?_⟩
    have hcard := reserve_class_card h X
    rw [Pattern.csize_sigma] at hcard
    have hcardR : (#((reserve h).filter fun v => lab v = X) : ℝ) +
        (g : ℝ) * m X * t = ksz lab X := by exact_mod_cast hcard
    have hmargin := proportional_reserve (N := N) (m := m X) (n := n) (g := g) (t := t)
      (by omega) (by omega) hδ.le hρ.le (by linarith) (hcls X) (by
        have hcl := (abs_le.mp (hclose X)).2
        change (m X : ℝ) / N - (ksz lab X : ℝ) / n ≤ min (ρ * δ / 4) ξ at hcl
        linarith [min_le_left (ρ * δ / 4) ξ]) hmult
    linarith


/-- Existential interface retained for callers that do not need the numeric bounds. -/
theorem exists_near_full_setup_reserve (hk : 4 ≤ k) (hg : 1 ≤ g) {δ η ρ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      3 * ∑ P, (ksz lab P : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n →
      (∀ P, δ * n ≤ ksz lab P) → (∃ a, SeedData (ksz lab) η a) →
      ∃ (m : Fin k → ℕ) (t : ℕ), (∀ P, 1 ≤ m P) ∧ ∑ P, m P ≤ B ∧
        3 * ∑ P, m P ^ 2 = (∑ P, m P) ^ 2 ∧
        (∀ P, |(m P : ℝ) / (∑ Q, m Q : ℕ) - ksz lab P / n| ≤ ξ) ∧
        (1 - ρ) * n ≤ ((g * (∑ P, m P) * t : ℕ) : ℝ) ∧
        (n : ℝ) / (4 * g * B) ≤ t ∧
        (∃ h : Setup lab (fun x : (Σ P, Fin (m P)) => x.1) g t,
          ∀ X, ρ * δ / 4 * n ≤ #((reserve h).filter fun v => lab v = X)) :=
  ⟨wilsonPatternBound k δ η ρ ξ, le_max_right _ _,
    wilsonPlacementThreshold k g δ η ρ ξ,
    exists_near_full_setup_reserve_explicit hk hg hδ hη hρ hρ1 hξ⟩

end CDRBicolour.KBicolor.Wilson
