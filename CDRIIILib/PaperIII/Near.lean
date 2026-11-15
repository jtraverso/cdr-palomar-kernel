/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.SeedGale

/-!
# T5: splits near a good profile are realised

Let `p` be a profile (`p > 0`, `Σ p = 1`, `Σ p² = 1/3`) with `(Σ_S p)² < 3 Σ_S p²` for every proper
nonempty `S` (the criterion T3). By complements, `g_S(p) = 2P_S - P_S² - 3Q_S > 0`; let `σ` be its
minimum. For an integer split `c` of `v` within `ρ v` of `p v` (`ρ ≤ σ/(20k)`), `g_S(c/v) ≥ σ/2`
(`g` is `10k`-Lipschitz on `[0,1]^k`), which gives Gale's cut conditions with `M ≥ 1/σ`. So
`seed_of_gale` provides a seed with `η = 1/M`, and Theorem T (`kbicolour_eventually`) applies.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

open Finset CDRBicolour.KBicolor

variable {k : ℕ}

/-- `g_S(t) = 2 P - P² - 3 Q`. -/
def gS (t : Fin k → ℝ) (S : Finset (Fin k)) : ℝ :=
  2 * ∑ X ∈ S, t X - (∑ X ∈ S, t X) ^ 2 - 3 * ∑ X ∈ S, t X ^ 2

/-- Complement identity: `g_S = 3 Q_{Sᶜ} - P_{Sᶜ}²` when `Σ t = 1`, `Σ t² = 1/3`. -/
theorem gS_compl (t : Fin k → ℝ) (h1 : ∑ X, t X = 1) (h2 : ∑ X, t X ^ 2 = 1 / 3)
    (S : Finset (Fin k)) :
    gS t S = 3 * ∑ X ∈ Sᶜ, t X ^ 2 - (∑ X ∈ Sᶜ, t X) ^ 2 := by
  have e1 := sum_add_sum_compl S t
  have e2 := sum_add_sum_compl S (fun X => t X ^ 2)
  rw [h1] at e1; rw [h2] at e2
  unfold gS
  have hP : ∑ X ∈ Sᶜ, t X = 1 - ∑ X ∈ S, t X := by linarith
  have hQ : ∑ X ∈ Sᶜ, t X ^ 2 = 1 / 3 - ∑ X ∈ S, t X ^ 2 := by linarith
  rw [hP, hQ]; ring

/-- Lipschitz estimate for `g_S` on `[0,1]^k`. -/
theorem gS_lip (t p : Fin k → ℝ) (ρ : ℝ) (ht0 : ∀ X, 0 ≤ t X) (hp0 : ∀ X, 0 ≤ p X)
    (ht1 : ∑ X, t X = 1) (hp1 : ∑ X, p X = 1) (hρ : ∀ X, |t X - p X| ≤ ρ)
    (S : Finset (Fin k)) : gS p S - 10 * k * ρ ≤ gS t S := by
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg _) (hρ ⟨0, by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at ht1
    · exact h⟩)
  have hcard : (S.card : ℝ) ≤ k := by
    have := card_le_univ S; rw [Fintype.card_fin] at this; exact_mod_cast this
  have hle1 : ∀ (u : Fin k → ℝ), (∀ X, 0 ≤ u X) → ∑ X, u X = 1 → 0 ≤ ∑ X ∈ S, u X ∧
      ∑ X ∈ S, u X ≤ 1 := by
    intro u hu hs
    refine ⟨sum_nonneg fun X _ => hu X, ?_⟩
    rw [← hs]; exact sum_le_sum_of_subset_of_nonneg (subset_univ S) fun X _ _ => hu X
  have hu1 : ∀ (u : Fin k → ℝ), (∀ X, 0 ≤ u X) → ∑ X, u X = 1 → ∀ X, u X ≤ 1 := by
    intro u hu hs X
    rw [← hs]; exact single_le_sum (fun Y _ => hu Y) (mem_univ X)
  obtain ⟨hPt0, hPt1⟩ := hle1 t ht0 ht1
  obtain ⟨hPp0, hPp1⟩ := hle1 p hp0 hp1
  have dP : |∑ X ∈ S, t X - ∑ X ∈ S, p X| ≤ k * ρ := by
    rw [← sum_sub_distrib]
    calc _ ≤ ∑ X ∈ S, |t X - p X| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ X ∈ S, ρ := sum_le_sum fun X _ => hρ X
      _ = S.card * ρ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ k * ρ := mul_le_mul_of_nonneg_right hcard hρ0
  have dQ : |∑ X ∈ S, t X ^ 2 - ∑ X ∈ S, p X ^ 2| ≤ 2 * k * ρ := by
    rw [← sum_sub_distrib]
    calc _ ≤ ∑ X ∈ S, |t X ^ 2 - p X ^ 2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ X ∈ S, 2 * ρ := sum_le_sum fun X _ => by
          rw [show t X ^ 2 - p X ^ 2 = (t X - p X) * (t X + p X) by ring, abs_mul]
          have := hρ X; have := hu1 t ht0 ht1 X; have := hu1 p hp0 hp1 X
          have := ht0 X; have := hp0 X
          rw [abs_of_nonneg (by linarith : 0 ≤ t X + p X)]
          nlinarith [abs_nonneg (t X - p X)]
      _ = S.card * (2 * ρ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ k * (2 * ρ) := mul_le_mul_of_nonneg_right hcard (by linarith)
      _ = 2 * k * ρ := by ring
  have dP2 : |(∑ X ∈ S, t X) ^ 2 - (∑ X ∈ S, p X) ^ 2| ≤ 2 * k * ρ := by
    rw [show (∑ X ∈ S, t X) ^ 2 - (∑ X ∈ S, p X) ^ 2 =
      (∑ X ∈ S, t X - ∑ X ∈ S, p X) * (∑ X ∈ S, t X + ∑ X ∈ S, p X) by ring, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ ∑ X ∈ S, t X + ∑ X ∈ S, p X)]
    nlinarith [abs_nonneg (∑ X ∈ S, t X - ∑ X ∈ S, p X)]
  unfold gS
  have a1 := (abs_le.1 dP).1; have a2 := (abs_le.1 dQ).2; have a3 := (abs_le.1 dP2).2
  nlinarith

/-- **T5.** Splits near a profile satisfying the criterion are realised. -/
theorem near_profile_bicolourable (hG : GaleInt) (hk : 2 ≤ k) (p : Fin k → ℝ)
    (hp : ∀ X, 0 < p X) (h1 : ∑ X, p X = 1) (h2 : ∑ X, p X ^ 2 = 1 / 3)
    (hcrit : ∀ S : Finset (Fin k), S.Nonempty → S ≠ univ →
      (∑ X ∈ S, p X) ^ 2 < 3 * ∑ X ∈ S, p X ^ 2) :
    ∃ ρ > 0, ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Odd v → ∀ c : Fin k → ℕ, ∑ X, c X = v →
      3 * ∑ X, c X * (c X - 1) = v * (v - 1) → (∀ X Y, X ≠ Y → Even (c X * c Y)) →
      (∀ X, |(c X : ℝ) - p X * v| ≤ ρ * v) → Bicolourable v k := by
  classical
  -- the slack `σ`
  set Fam := (univ : Finset (Finset (Fin k))).filter (fun S => S.Nonempty ∧ S ≠ univ) with hFam
  have hFne : Fam.Nonempty := ⟨{⟨0, by omega⟩}, by
    simp only [hFam, mem_filter, mem_univ, true_and]
    refine ⟨singleton_nonempty _, fun h => ?_⟩
    have := congrArg card h; rw [card_singleton, card_univ, Fintype.card_fin] at this; omega⟩
  obtain ⟨S₀, hS₀, hmin⟩ := Fam.exists_min_image (gS p) hFne
  set σ := gS p S₀ with hσ
  have hpos_g : ∀ S ∈ Fam, 0 < gS p S := by
    intro S hS
    simp only [hFam, mem_filter, mem_univ, true_and] at hS
    rw [gS_compl p h1 h2]
    have hne : Sᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]; exact hS.2
    have hnu : Sᶜ ≠ univ := by
      intro h; exact hS.1.ne_empty ((compl_eq_univ_iff S).1 h)
    linarith [hcrit Sᶜ hne hnu]
  have hσ0 : 0 < σ := hpos_g S₀ hS₀
  -- the minimal class
  obtain ⟨X₀, -, hX₀⟩ := (univ : Finset (Fin k)).exists_min_image p ⟨⟨0, by omega⟩, mem_univ _⟩
  set pm := p X₀ with hpm
  have hpm0 : 0 < pm := hp X₀
  have hp1 : ∀ X, p X ≤ 1 := fun X => by
    rw [← h1]; exact single_le_sum (fun Y _ => (hp Y).le) (mem_univ X)
  -- constants
  set ρ : ℝ := min (pm / 2) (σ / (20 * k)) with hρ
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hρ0 : 0 < ρ := lt_min (by linarith) (by positivity)
  set M : ℕ := ⌈1 / σ⌉₊ + 3 with hM
  have hM3 : 3 ≤ M := by omega
  have hMσ : 1 / σ ≤ (M : ℝ) := by
    have := Nat.le_ceil (1 / σ); push_cast [hM]; linarith
  obtain ⟨n₀, hT⟩ := kbicolour_eventually k hk (δ := pm / 2) (η := 1 / (M : ℝ))
    (by linarith) (by linarith [hp1 X₀]) (by positivity)
  refine ⟨ρ, hρ0, n₀, fun v hv hodd c hs hd heven hnear => ?_⟩
  have hvpos : 0 < v := by obtain ⟨m, hm⟩ := hodd; omega
  have hvR : (0 : ℝ) < v := by exact_mod_cast hvpos
  -- normalised split
  set t : Fin k → ℝ := fun X => (c X : ℝ) / v with ht
  have htp : ∀ X, |t X - p X| ≤ ρ := by
    intro X
    rw [show t X - p X = ((c X : ℝ) - p X * v) / v by simp only [ht]; field_simp,
      abs_div, abs_of_pos hvR, div_le_iff₀ hvR]
    exact hnear X
  have ht0 : ∀ X, 0 ≤ t X := fun X => by simp only [ht]; positivity
  have hsR : ∑ X, (c X : ℝ) = v := by exact_mod_cast hs
  have ht1 : ∑ X, t X = 1 := by simp only [ht]; rw [← sum_div, hsR, div_self hvR.ne']
  have hlow : ∀ X, pm / 2 * (v : ℝ) ≤ c X := by
    intro X
    have a := (abs_le.1 (hnear X)).1
    have b : pm ≤ p X := hX₀ X (mem_univ X)
    have c' : ρ ≤ pm / 2 := min_le_left _ _
    nlinarith
  have hc1 : ∀ X, 1 ≤ c X := fun X => by
    have := hlow X
    have : (0 : ℝ) < c X := lt_of_lt_of_le (by positivity) this
    exact_mod_cast this
  -- divisibility in ℤ
  have hqZ : 3 * ∑ X, ((c X : ℤ)) ^ 2 = (v : ℤ) ^ 2 + 2 * v := by
    have hdZ : ((3 * ∑ X, c X * (c X - 1) : ℕ) : ℤ) = ((v * (v - 1) : ℕ) : ℤ) := by
      exact_mod_cast hd
    push_cast [Nat.cast_sub (hc1 _), Nat.cast_sub (by omega : 1 ≤ v)] at hdZ
    have hsZ : ∑ X, (c X : ℤ) = v := by exact_mod_cast hs
    have : ∑ X, (c X : ℤ) * ((c X : ℤ) - 1) = ∑ X, ((c X : ℤ)) ^ 2 - ∑ X, (c X : ℤ) := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun X _ => by ring
    rw [this, hsZ] at hdZ
    linarith
  -- cut conditions
  have hcut : ∀ S : Finset (Fin k), ∑ X ∈ S, (M : ℤ) * c X * (3 * c X - v - 2) ≤
      ∑ X ∈ S, ∑ Y ∈ Sᶜ, ((M : ℤ) - 2) * c X * c Y := by
    intro S
    by_cases hS : S ∈ Fam
    · -- proper nonempty: via `g_S(t) ≥ σ/2`
      have hg : σ / 2 ≤ gS t S := by
        have := gS_lip t p ρ ht0 (fun X => (hp X).le) ht1 h1 htp S
        have := hmin S hS
        have : 10 * k * ρ ≤ σ / 2 := by
          have := min_le_right (pm / 2) (σ / (20 * k))
          calc 10 * (k : ℝ) * ρ ≤ 10 * k * (σ / (20 * k)) := by gcongr
            _ = σ / 2 := by field_simp; ring
        linarith
      -- translate to the unnormalised inequality
      have hPQ : ∀ X, (c X : ℝ) = v * t X := fun X => by simp only [ht]; field_simp
      have hcross : ∑ X ∈ S, ∑ Y ∈ Sᶜ, t X * t Y = (∑ X ∈ S, t X) * (1 - ∑ X ∈ S, t X) := by
        rw [← sum_mul_sum]
        congr 1
        have := sum_add_sum_compl S t; rw [ht1] at this; linarith
      have hR : (∑ X ∈ S, (M : ℝ) * c X * (3 * c X - v - 2) : ℝ) ≤
          ∑ X ∈ S, ∑ Y ∈ Sᶜ, ((M : ℝ) - 2) * c X * c Y := by
        simp only [hPQ]
        have eL : ∑ X ∈ S, (M : ℝ) * (v * t X) * (3 * (v * t X) - v - 2) =
            (M : ℝ) * v ^ 2 * (3 * ∑ X ∈ S, t X ^ 2 - ∑ X ∈ S, t X) -
              2 * M * v * ∑ X ∈ S, t X := by
          have e : ∀ X, (M : ℝ) * (v * t X) * (3 * (v * t X) - v - 2) =
              ((M : ℝ) * v ^ 2) * (3 * t X ^ 2) - ((M : ℝ) * v ^ 2) * t X - (2 * M * v) * t X :=
            fun X => by ring
          simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring
        have eR : ∑ X ∈ S, ∑ Y ∈ Sᶜ, ((M : ℝ) - 2) * (v * t X) * (v * t Y) =
            ((M : ℝ) - 2) * v ^ 2 * ((∑ X ∈ S, t X) * (1 - ∑ X ∈ S, t X)) := by
          rw [← hcross, mul_sum]
          exact sum_congr rfl fun X _ => by rw [mul_sum]; exact sum_congr rfl fun Y _ => by ring
        rw [eL, eR]
        have hP0 : 0 ≤ ∑ X ∈ S, t X := sum_nonneg fun X _ => ht0 X
        have hP1 : ∑ X ∈ S, t X ≤ 1 := by
          rw [← ht1]; exact sum_le_sum_of_subset_of_nonneg (subset_univ S) fun X _ _ => ht0 X
        -- `M g ≥ 1/2 ≥ 2 P (1 - P)` gives the claim
        unfold gS at hg
        set P := ∑ X ∈ S, t X
        set Q := ∑ X ∈ S, t X ^ 2
        have hMg : (1 : ℝ) / 2 ≤ M * (2 * P - P ^ 2 - 3 * Q) := by
          have : (M : ℝ) * (σ / 2) ≤ M * (2 * P - P ^ 2 - 3 * Q) :=
            mul_le_mul_of_nonneg_left hg (by positivity)
          have h' : 1 / 2 ≤ (M : ℝ) * (σ / 2) := by
            rw [div_le_iff₀ hσ0] at hMσ; nlinarith
          linarith
        have hPP : 2 * P * (1 - P) ≤ 1 / 2 := by nlinarith [sq_nonneg (P - 1 / 2)]
        have hv2 : (0 : ℝ) ≤ (v : ℝ) ^ 2 := by positivity
        have : (M : ℝ) * (3 * Q - P) ≤ ((M : ℝ) - 2) * (P * (1 - P)) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this hv2, mul_nonneg (mul_nonneg (by positivity :
          (0 : ℝ) ≤ 2 * M) hvR.le) hP0]
      exact_mod_cast hR
    · -- `S = ∅` or `S = univ`
      simp only [hFam, mem_filter, mem_univ, true_and, not_and_or, not_not,
        not_nonempty_iff_eq_empty] at hS
      rcases hS with rfl | rfl
      · simp
      · simp only [compl_univ, sum_empty, sum_const_zero]
        have : ∑ X, (M : ℤ) * c X * (3 * c X - v - 2) =
            (M : ℤ) * (3 * ∑ X, ((c X : ℤ)) ^ 2 - (v + 2) * ∑ X, (c X : ℤ)) := by
          rw [mul_sum, Finset.mul_sum, ← sum_sub_distrib, mul_sum]
          exact sum_congr rfl fun X _ => by ring
        have hsZ : ∑ X, (c X : ℤ) = v := by exact_mod_cast hs
        rw [this, hqZ, hsZ]; ring_nf; rfl
  -- assemble
  obtain ⟨a, ha⟩ := seed_of_gale hG c hM3 hc1 hs hqZ hcut
  obtain ⟨lab, hlab⟩ := exists_lab c hs
  have hkk : ksz lab = c := funext hlab
  have hposk : ∀ X, 0 < ksz lab X := fun X => by rw [hlab]; exact hc1 X
  obtain ⟨D, hD⟩ := hT v lab hv hodd (fun X => by rw [hlab]; exact hlow X)
    (fun X Y h => by rw [hkk]; exact heven X Y h) (by rw [hkk]; exact hd) ⟨a, by rw [hkk]; exact ha⟩
  exact bicolourable_of_decomposition lab hposk D hD

end CDRBicolour.PaperIII
