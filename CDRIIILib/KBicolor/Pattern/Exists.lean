/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Pattern.Cone
public import CDRIIILib.KBicolor.Pattern.CutBound

/-!
# Existence of k-bicoloured Latin patterns close to a profile

`exists_pattern`: for `k ≥ 4`, every admissible k-profile `c` of order `n` (classes `≥ δ n`, an
η-seed) admits, for `n` large, class sizes `m` of **bounded** total `N ≤ B(k, δ, η, ε)` with

* `3 Σ m² = N²` and `m_P ≥ 1`,
* `|m_P / N − c_P / n| ≤ ε` for every class,
* an integer tournament `IsTour m x` (hence a k-bicoloured Latin square, `kbls_of_tournament`).

Construction: `c′ = ⌊D c / n⌋ + j·1_M` (`M` a class with `3 c_M ≥ (1 + δ) n`, so that
`Q(c′) = 3 Σ c′² − (Σ c′)² ≥ 0`), then the cone point `m = Q(c′) 1_E + 6 σ′ c′`. The tournament
comes from Gale (`exists_tour`); its cut conditions follow from the η-seed (`cutR_seed`) by
perturbation (`cutR_close`).
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Pattern

open Finset

variable {k : ℕ}

/-- The quadratic form `Q(x) = 3 Σ x² − (Σ x)²`. -/
def qf (x : Fin k → ℝ) : ℝ := 3 * ∑ P, x P ^ 2 - (∑ P, x P) ^ 2

/-- Rounding bounds for `Q`. -/
theorem qf_round (u x : Fin k → ℝ) {D n : ℝ} (hn : 0 < n) (hDn : D ≤ n) (hD : 0 ≤ D)
    (hxu : ∀ P, x P ≤ u P) (hux : ∀ P, u P < x P + 1) (hu0 : ∀ P, 0 ≤ u P)
    (hU1 : ∑ P, u P = D) (hU2 : 3 * ∑ P, u P ^ 2 = D ^ 2 + 2 * D ^ 2 / n) :
    -6 * D - (k : ℝ) ^ 2 ≤ qf x ∧ qf x ≤ 2 * D + 3 * k + 2 * D * k := by
  set f : Fin k → ℝ := fun P => u P - x P with hf
  have hf0 : ∀ P, 0 ≤ f P := fun P => by simp only [hf]; linarith [hxu P]
  have hf1 : ∀ P, f P ≤ 1 := fun P => by simp only [hf]; linarith [hux P]
  have hx : ∀ P, x P = u P - f P := fun P => by simp only [hf]; ring
  set F1 := ∑ P, f P with hF1
  set F2 := ∑ P, f P ^ 2 with hF2
  set UF := ∑ P, u P * f P with hUF
  have hF1b : 0 ≤ F1 ∧ F1 ≤ k := by
    constructor
    · exact Finset.sum_nonneg fun P _ => hf0 P
    · calc F1 ≤ ∑ _P : Fin k, (1 : ℝ) := Finset.sum_le_sum fun P _ => hf1 P
        _ = k := by simp
  have hF2b : 0 ≤ F2 ∧ F2 ≤ k := by
    constructor
    · exact Finset.sum_nonneg fun P _ => sq_nonneg _
    · calc F2 ≤ ∑ _P : Fin k, (1 : ℝ) :=
            Finset.sum_le_sum fun P _ => by nlinarith [hf0 P, hf1 P]
        _ = k := by simp
  have hUFb : 0 ≤ UF ∧ UF ≤ D := by
    constructor
    · exact Finset.sum_nonneg fun P _ => mul_nonneg (hu0 P) (hf0 P)
    · calc UF ≤ ∑ P, u P := Finset.sum_le_sum fun P _ => by nlinarith [hu0 P, hf0 P, hf1 P]
        _ = D := hU1
  have hsum : ∑ P, x P = D - F1 := by
    simp only [hx, Finset.sum_sub_distrib, hU1, hF1]
  have hsq : ∑ P, x P ^ 2 = ∑ P, u P ^ 2 - 2 * UF + F2 := by
    simp only [hx, hUF, hF2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun P _ => by ring
  have hq : qf x = 2 * D ^ 2 / n - 6 * UF + 3 * F2 + 2 * D * F1 - F1 ^ 2 := by
    unfold qf; rw [hsum, hsq]; linarith [hU2]
  have hDn' : 2 * D ^ 2 / n ≤ 2 * D := by
    rw [div_le_iff₀ hn]; nlinarith
  have hDn0 : 0 ≤ 2 * D ^ 2 / n := by positivity
  have hkk : (k : ℝ) * k = (k : ℝ) ^ 2 := by ring
  rw [hq]
  constructor
  · nlinarith [hF1b.1, hF1b.2, hF2b.1, hUFb.2]
  · nlinarith [hF1b.1, hF1b.2, hF2b.2, hUFb.1]

/-- Bumping one coordinate. -/
theorem qf_bump (x : Fin k → ℝ) (M : Fin k) (j : ℝ) :
    qf (fun P => x P + if P = M then j else 0) =
      qf x + 2 * j * (3 * x M - ∑ P, x P) + 2 * j ^ 2 := by
  unfold qf
  have e1 : ∑ P, (x P + if P = M then j else 0) ^ 2 = ∑ P, x P ^ 2 + 2 * j * x M + j ^ 2 := by
    have : ∀ P, (x P + if P = M then j else 0) ^ 2 =
        x P ^ 2 + ((if P = M then 2 * j * x P else 0) + if P = M then j ^ 2 else 0) := by
      intro P; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have e2 : ∑ P, (x P + if P = M then j else 0) = ∑ P, x P + j := by
    simp [Finset.sum_add_distrib]
  rw [e1, e2]; ring

/-- Three classes `0, 1, 2`. -/
def E3 (hk : 3 ≤ k) : Finset (Fin k) := (univ : Finset (Fin 3)).map (Fin.castLEEmb hk)

theorem card_E3 (hk : 3 ≤ k) : #(E3 hk) = 3 := by simp [E3]

theorem not_mem_E3 (hk : 4 ≤ k) : (⟨3, by omega⟩ : Fin k) ∉ E3 (by omega : 3 ≤ k) := by
  simp only [E3, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
  intro i h
  have := congrArg Fin.val h
  simp at this
  omega

/-- Closeness of the rounded profile. -/
theorem round_close {u x : Fin k → ℝ} {D : ℝ} {j : ℝ} (M P : Fin k) (hD : 0 < D) (hj : 0 ≤ j)
    (hxu : ∀ P, x P ≤ u P) (hux : ∀ P, u P < x P + 1) (hu0 : ∀ P, 0 ≤ u P)
    (huD : ∀ P, u P ≤ D) (hU1 : ∑ P, u P = D) (hS : D / 2 ≤ ∑ P, x P + j) :
    |(x P + if P = M then j else 0) / (∑ Q, x Q + j) - u P / D| ≤ 2 * (1 + k + 2 * j) / D := by
  set S1 := ∑ Q, x Q + j with hS1
  have hS0 : 0 < S1 := by linarith
  have hF : 0 ≤ D - ∑ Q, x Q ∧ D - ∑ Q, x Q ≤ k := by
    constructor
    · rw [← hU1, ← Finset.sum_sub_distrib]; exact Finset.sum_nonneg fun Q _ => by linarith [hxu Q]
    · rw [← hU1, ← Finset.sum_sub_distrib]
      calc ∑ Q, (u Q - x Q) ≤ ∑ _Q : Fin k, (1 : ℝ) :=
            Finset.sum_le_sum fun Q _ => by linarith [hux Q]
        _ = k := by simp
  have hfP : 0 ≤ u P - x P ∧ u P - x P ≤ 1 := ⟨by linarith [hxu P], by linarith [hux P]⟩
  have hite : 0 ≤ (if P = M then j else 0) ∧ (if P = M then j else 0) ≤ j := by
    split_ifs <;> constructor <;> linarith
  have e : (x P + if P = M then j else 0) / S1 - u P / D =
      (D * ((if P = M then j else 0) - (u P - x P)) - u P * (j - (D - ∑ Q, x Q))) / (D * S1) := by
    field_simp; rw [hS1]; ring
  rw [e, abs_div, abs_of_pos (mul_pos hD hS0), div_le_div_iff₀ (mul_pos hD hS0) hD]
  have hnum : |D * ((if P = M then j else 0) - (u P - x P)) - u P * (j - (D - ∑ Q, x Q))| ≤
      D * (1 + k + 2 * j) := by
    have h1 : |D * ((if P = M then j else 0) - (u P - x P))| ≤ D * (1 + j) := by
      rw [abs_mul, abs_of_pos hD]
      exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith) hD.le
    have h2 : |u P * (j - (D - ∑ Q, x Q))| ≤ D * (k + j) := by
      rw [abs_mul, abs_of_nonneg (hu0 P)]
      exact mul_le_mul (huD P) (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _) hD.le
    calc _ ≤ |D * ((if P = M then j else 0) - (u P - x P))| + |u P * (j - (D - ∑ Q, x Q))| :=
          abs_sub _ _
      _ ≤ D * (1 + j) + D * (k + j) := add_le_add h1 h2
      _ = D * (1 + k + 2 * j) := by ring
  calc |D * ((if P = M then j else 0) - (u P - x P)) - u P * (j - (D - ∑ Q, x Q))| * D
      ≤ D * (1 + k + 2 * j) * D := mul_le_mul_of_nonneg_right hnum hD.le
    _ = 2 * (D * (1 + k + 2 * j) * (D / 2)) := by ring
    _ ≤ 2 * (D * (1 + k + 2 * j) * S1) := by
        have hpos : 0 ≤ D * (1 + k + 2 * j) := by positivity
        have := mul_le_mul_of_nonneg_left hS hpos
        linarith
    _ = 2 * (1 + k + 2 * j) * (D * S1) := by ring

/-- Gale's cut condition for proper nonempty class sets, from the η-seed by perturbation. -/
theorem cut_proper {c : Fin k → ℕ} {n : ℕ} {δ η ε : ℝ} {a : Fin k → Fin k → ℝ}
    (hs : SeedData c η a) (hn : 0 < n) (hδ : 0 < δ) (hη : 0 < η) (hcls : ∀ P, δ * n ≤ c P)
    (hsum : ∑ P, c P = n) (hn4 : 4 / (η * δ ^ 2) ≤ n) (hε : 0 ≤ ε)
    (hε' : 6 * (k : ℝ) ^ 2 * ε ≤ η * δ ^ 2 / 4)
    {v : Fin k → ℝ} (hv : ∀ P, |v P| ≤ 1) (hvc : ∀ P, |v P - c P / n| ≤ ε)
    (S : Finset (Fin k)) {P Q : Fin k} (hP : P ∈ S) (hQ : Q ∉ S) : cutR S v ≤ 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsumR : ∑ P, (c P : ℝ) = n := by exact_mod_cast hsum
  have hw : ∀ P, |(c P : ℝ) / n| ≤ 1 := by
    intro P
    rw [abs_of_nonneg (by positivity), div_le_one hnR, ← hsumR]
    exact Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (mem_univ P)
  have h1 := cutR_close S hε hv hw hvc
  have h2 : cutR S (fun P => (c P : ℝ) / n) = (1 / (n : ℝ)) ^ 2 * cutR S (fun P => (c P : ℝ)) := by
    rw [← cutR_smul]; congr 1; ext P; ring
  have h3 := cutR_seed hs S
  set cS := ∑ P ∈ S, (c P : ℝ) with hcS
  set cT := ∑ Q ∈ Sᶜ, (c Q : ℝ) with hcT
  have hcS1 : δ * n ≤ cS := (hcls P).trans
    (Finset.single_le_sum (f := fun P => (c P : ℝ)) (fun _ _ => Nat.cast_nonneg _) hP)
  have hcT1 : δ * n ≤ cT := (hcls Q).trans
    (Finset.single_le_sum (f := fun P => (c P : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_compl.2 hQ))
  have hcSn : cS ≤ n := by
    rw [← hsumR]; exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ S)
      (fun _ _ _ => Nat.cast_nonneg _)
  have hprod : η * ((δ * n) * (δ * n)) ≤ η * (cS * cT) := by
    apply mul_le_mul_of_nonneg_left _ hη.le
    exact mul_le_mul hcS1 hcT1 (by positivity) (le_trans (by positivity) hcS1)
  -- cutR S (c/n) ≤ 1/n − η δ²
  have h4 : cutR S (fun P => (c P : ℝ) / n) ≤ 1 / n - η * δ ^ 2 := by
    rw [h2]
    have : cutR S (fun P => (c P : ℝ)) ≤ n - η * ((δ * n) * (δ * n)) := by linarith
    calc (1 / (n : ℝ)) ^ 2 * cutR S (fun P => (c P : ℝ))
        ≤ (1 / (n : ℝ)) ^ 2 * (n - η * ((δ * n) * (δ * n))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / n - η * δ ^ 2 := by field_simp
  have h5 : 1 / (n : ℝ) ≤ η * δ ^ 2 / 4 := by
    rw [div_le_iff₀ hnR]
    have hηδ : 0 < η * δ ^ 2 := by positivity
    rw [div_le_iff₀ hηδ] at hn4
    nlinarith
  have hηδ : 0 < η * δ ^ 2 := by positivity
  have := (abs_le.1 h1).2
  linarith

end CDRBicolour.KBicolor.Pattern
