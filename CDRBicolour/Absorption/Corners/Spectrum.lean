/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Symmetry
public import CDRBicolour.Absorption.Exact.Final

/-!
# The exact spectrum of block types (item 3)

`LowerNec a b c t`: the arithmetic condition of the lower corner (`lower_nec`, `corner_lower`).
`ExactNec a b c t`: `2t ≤ a(a−1)`, `LowerNec a b c t` and `LowerNec a c b (a(a−1)/2 − t)` (the upper
corner, read through the exchange `B ↔ C`).

**`cdr_type_spectrum`**: for every sufficiently large admissible profile, `t` is the number of
`AAC` blocks of some strictly bicoloured STS with the prescribed classes **iff** `ExactNec a b c t`.
Sufficiency: the lower corner (`corner_lower`), the upper corner (`corner_lower` for `(a, c, b)`),
and in between all six type counts are `≥ 10⁻¹⁷ n²` (`large_counts_R`), where `cdr_aac_exact`
applies.
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.BlockTypes

/-- The arithmetic condition of the lower corner. -/
def LowerNec (a b c t : ℕ) : Prop :=
  ∃ d q r : Fin 3 → ℕ, (∀ X, r X < sz a b c X) ∧
    (∀ X, (d X : ℤ) = sz a b c X - 1 - sz a b c (X + 1) + 2 * q X) ∧
    (∀ X, sz a b c X * d X + 2 * r X = 2 * (sz a b c (X + 2) * q (X + 2) + r (X + 2))) ∧
    (∀ X, ¬ (d X = 0 ∧ (r X = 1 ∨ r X = 2))) ∧ c * q 2 + r 2 = t

/-- **The exact condition** on `t = N_AAC`. -/
def ExactNec (a b c t : ℕ) : Prop :=
  2 * t ≤ a * (a - 1) ∧ LowerNec a b c t ∧ LowerNec a c b (a * (a - 1) / 2 - t)

/-- `t` is the number of `AAC` blocks of a strictly bicoloured STS with the prescribed classes. -/
def AACSpec (a b c t : ℕ) : Prop :=
  ∃ S : STS (Fin (a + b + c)), IsStrictBicolouring S (col3 a b c) ∧ typeCount S (col3 a b c) 0 2 = t

theorem adm_swap23 {a b c : ℕ} (h : AdmissibleProfile a b c) : AdmissibleProfile a c b := by
  obtain ⟨ha, hb, hc, hm, hq, e1, e2, e3⟩ := h
  refine ⟨ha, hc, hb, by omega, by push_cast; linear_combination hq, e2, e1, ?_⟩
  rintro ⟨h1, h2⟩; exact e3 ⟨h2, h1⟩

theorem fin3_cover : ∀ X X₀ : Fin 3, X = X₀ ∨ X = X₀ + 2 ∨ X = X₀ + 1 := by decide
theorem fin3_add4 : ∀ X : Fin 3, X + 2 + 2 = X + 1 := by decide

/-- **Large counts away from the corner** (real arithmetic). -/
theorem large_counts_R (N : ℝ) (S D Q R : Fin 3 → ℝ) (hN : 10 ^ 40 ≤ N) (hS : ∀ X, N / 4 ≤ S X)
    (hSN : ∀ X, S X ≤ N) (hdiff : ∀ X, (S X - S (X + 1)) ^ 2 ≤ 2 * N) (hQ : ∀ X, 0 ≤ Q X)
    (hR : ∀ X, 0 ≤ R X) (hD : ∀ X, D X = S X - 1 - S (X + 1) + 2 * Q X)
    (hE : ∀ X, S X * D X + 2 * R X = 2 * (S (X + 2) * Q (X + 2) + R (X + 2))) (X₀ : Fin 3)
    (hfail : N < 10 ^ 15 * (D X₀ + Q X₀ + 1)) : ∀ X, N ^ 2 / 10 ^ 17 ≤ S X * Q X + R X := by
  have hN0 : 0 < N := by linarith [show (0 : ℝ) < 10 ^ 40 by norm_num]
  -- `|α| ≤ N / 10¹⁷`
  have hα : ∀ X, |S X - 1 - S (X + 1)| ≤ N / 10 ^ 17 := by
    intro X
    have h1 := hdiff X
    have h2 : (S X - 1 - S (X + 1)) ^ 2 ≤ 4 * N + 2 := by
      nlinarith [sq_nonneg (S X - S (X + 1) + 1)]
    have h3 : 4 * N + 2 ≤ (N / 10 ^ 17) ^ 2 := by
      have : (10 : ℝ) ^ 40 * N ≤ N * N := by nlinarith
      nlinarith
    have hB : 0 ≤ N / 10 ^ 17 := by positivity
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (S X - 1 - S (X + 1) - N / 10 ^ 17),
      sq_nonneg (S X - 1 - S (X + 1) + N / 10 ^ 17)]
  -- the relation `K_{X+2} = K_X + S_X α_X / 2`
  have hrel : ∀ X, S (X + 2) * Q (X + 2) + R (X + 2) =
      S X * Q X + R X + S X * (S X - 1 - S (X + 1)) / 2 := by
    intro X; have := hE X; rw [hD X] at this; linarith
  have hstep : ∀ X, S X * Q X + R X - N ^ 2 / (2 * 10 ^ 17) ≤
      S (X + 2) * Q (X + 2) + R (X + 2) := by
    intro X
    rw [hrel X]
    have hb := abs_le.1 (hα X)
    have hs0 : 0 ≤ S X := le_trans (by positivity) (hS X)
    have : -(S X * (N / 10 ^ 17)) ≤ S X * (S X - 1 - S (X + 1)) := by nlinarith [hb.1]
    have : S X * (N / 10 ^ 17) ≤ N * (N / 10 ^ 17) :=
      mul_le_mul_of_nonneg_right (hSN X) (by positivity)
    have : N * (N / 10 ^ 17) = N ^ 2 / 10 ^ 17 := by ring
    linarith
  -- the failing class is large
  have hq0 : N / (6 * 10 ^ 15) ≤ Q X₀ := by
    have hb := abs_le.1 (hα X₀)
    have hd := hD X₀
    have : N < 10 ^ 15 * (N / 10 ^ 17 + 3 * Q X₀ + 1) := by nlinarith
    have : (10 : ℝ) ^ 15 ≤ N / 100 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hK0 : N ^ 2 / (24 * 10 ^ 15) ≤ S X₀ * Q X₀ + R X₀ := by
    have h1 : N / 4 * (N / (6 * 10 ^ 15)) ≤ S X₀ * Q X₀ :=
      mul_le_mul (hS X₀) hq0 (by positivity) (le_trans (by positivity) (hS X₀))
    have h2 : N / 4 * (N / (6 * 10 ^ 15)) = N ^ 2 / (24 * 10 ^ 15) := by ring
    linarith [hR X₀]
  have hK2 := hstep X₀
  have hK4 := hstep (X₀ + 2)
  rw [fin3_add4] at hK4
  have hfin : N ^ 2 / 10 ^ 17 ≤ N ^ 2 / (24 * 10 ^ 15) - N ^ 2 / (2 * 10 ^ 17) - N ^ 2 / (2 * 10 ^ 17) := by
    have : 0 ≤ N ^ 2 := by positivity
    rw [show N ^ 2 / (24 * 10 ^ 15) - N ^ 2 / (2 * 10 ^ 17) - N ^ 2 / (2 * 10 ^ 17) =
      N ^ 2 * (1 / (24 * 10 ^ 15) - 1 / 10 ^ 17) by ring, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (by norm_num) this
  intro X
  rcases fin3_cover X X₀ with rfl | rfl | rfl
  · have : N ^ 2 / 10 ^ 17 ≤ N ^ 2 / (24 * 10 ^ 15) := by
      have : 0 ≤ N ^ 2 := by positivity
      rw [div_eq_mul_one_div, div_eq_mul_one_div (N ^ 2)]
      exact mul_le_mul_of_nonneg_left (by norm_num) this
    linarith
  · have : 0 ≤ N ^ 2 / (2 * 10 ^ 17) := by positivity
    linarith
  · linarith

/-! ### Transport through the exchange `B ↔ C` -/

theorem swap_transport {a b c : ℕ} (S : STS (Fin (a + b + c)))
    (hS : IsStrictBicolouring S (col3 a b c)) :
    ∃ S' : STS (Fin (a + c + b)), IsStrictBicolouring S' (col3 a c b) ∧
      typeCount S' (col3 a c b) 0 2 = typeCount S (col3 a b c) 0 1 ∧
      typeCount S' (col3 a c b) 0 1 = typeCount S (col3 a b c) 0 2 := by
  obtain ⟨e, he⟩ := exists_swap12 a b c
  refine ⟨S.map e, strict_map he hS, ?_, ?_⟩
  · have := typeCount_map S he 0 1
    simpa [sw12, Equiv.swap_apply_of_ne_of_ne] using this
  · have := typeCount_map S he 0 2
    simpa [sw12, Equiv.swap_apply_of_ne_of_ne] using this

theorem choose_counts {a b c : ℕ} (S : STS (Fin (a + b + c)))
    (hS : IsStrictBicolouring S (col3 a b c)) :
    a * (a - 1) = 2 * (typeCount S (col3 a b c) 0 1 + typeCount S (col3 a b c) 0 2) := by
  have := classSize_choose S (col3 a b c) hS (i := 0) (j := 1) (k := 2) (by decide) (by decide)
    (by decide)
  rwa [classSize_col3] at this

theorem lowerNec_of_spec {a b c t : ℕ} (h : AdmissibleProfile a b c) (hspec : AACSpec a b c t) :
    LowerNec a b c t := by
  obtain ⟨S, hS, rfl⟩ := hspec
  exact lower_nec h S hS

/-- **Necessity of the exact condition.** -/
theorem exactNec_of_spec {a b c t : ℕ} (h : AdmissibleProfile a b c) (hspec : AACSpec a b c t) :
    ExactNec a b c t := by
  obtain ⟨S, hS, rfl⟩ := hspec
  have hc := choose_counts S hS
  obtain ⟨S', hS', h1, -⟩ := swap_transport S hS
  refine ⟨by omega, lower_nec h S hS, ?_⟩
  have : a * (a - 1) / 2 - typeCount S (col3 a b c) 0 2 = typeCount S' (col3 a c b) 0 2 := by
    rw [h1]; omega
  rw [this]
  exact lower_nec (adm_swap23 h) S' hS'

/-! ### Sufficiency -/

theorem cast_half {a : ℕ} : ((a * (a - 1) / 2 : ℕ) : ℝ) = ch (a : ℝ) := by
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self a
  have e : a * (a - 1) / 2 = k := by omega
  rw [e, ch]
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    have : k = 0 := by simp at hk; omega
    subst this; simp
  · have h1 : ((a * (a - 1) : ℕ) : ℝ) = ((k + k : ℕ) : ℝ) := by rw [hk]
    rw [Nat.cast_mul, Nat.cast_sub h0] at h1
    push_cast at h1
    linarith

set_option maxHeartbeats 4000000 in
/-- **Item 3: the exact spectrum of block types.** For every sufficiently large admissible
profile, `t` is the number of `AAC` blocks of a strictly bicoloured STS with the prescribed classes
if and only if `ExactNec a b c t`. -/
theorem cdr_type_spectrum : ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
    ∀ t : ℕ, AACSpec a b c t ↔ ExactNec a b c t := by
  obtain ⟨nL, hL⟩ := corner_lower
  obtain ⟨n₁, h₁⟩ := CDRBicolour.Absorption.Exact.cdr_aac_exact (1 / 10 ^ 17) (by norm_num)
  refine ⟨max (max nL n₁) (10 ^ 40), fun a b c h hn t => ⟨exactNec_of_spec h, fun hE => ?_⟩⟩
  have hnL : nL ≤ a + b + c := le_trans (le_max_left _ _) (le_of_max_le_left hn)
  have hn₁ : n₁ ≤ a + b + c := le_trans (le_max_right _ _) (le_of_max_le_left hn)
  have hn40 : 10 ^ 40 ≤ a + b + c := le_of_max_le_right hn
  obtain ⟨h2t, ⟨d, q, r, hr, hdq, hEq, hex, ht⟩, ⟨d', q', r', hr', hdq', hEq', hex', ht'⟩⟩ := hE
  have h' := adm_swap23 h
  -- lower corner
  by_cases hlow : ∀ X, 10 ^ 15 * (d X + q X + 1) ≤ a + b + c
  · obtain ⟨S, hS, -, -, -, hcount⟩ := hL a b c h hnL d q r hr hdq hEq hex hlow
    exact ⟨S, hS, by rw [hcount, ht]⟩
  -- upper corner
  by_cases hup : ∀ X, 10 ^ 15 * (d' X + q' X + 1) ≤ a + c + b
  · obtain ⟨S', hS', -, -, -, hcount⟩ := hL a c b h' (by omega) d' q' r' hr' hdq' hEq' hex' hup
    obtain ⟨S, hS, -, h2⟩ := swap_transport (a := a) (b := c) (c := b) S' hS'
    have hc := choose_counts S hS
    refine ⟨S, hS, ?_⟩
    have : typeCount S (col3 a b c) 0 1 = a * (a - 1) / 2 - t := by
      rw [h2, hcount, ht']
    omega
  -- in between: all six counts are large
  push Not at hlow hup
  obtain ⟨X₀, hX₀⟩ := hlow
  obtain ⟨Y₀, hY₀⟩ := hup
  have h400 : 400 ≤ a + b + c := le_trans (by norm_num) hn40
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  set N : ℝ := ((a + b + c : ℕ) : ℝ) with hNdef
  have hN40 : (10 : ℝ) ^ 40 ≤ N := by rw [hNdef]; exact_mod_cast hn40
  have hszl : ∀ X, N / 4 ≤ (sz a b c X : ℝ) := by
    intro X
    have : a + b + c ≤ 4 * sz a b c X := by fin_cases X <;> simp [sz] <;> omega
    have : (((a + b + c : ℕ) : ℝ)) ≤ 4 * (sz a b c X : ℝ) := by exact_mod_cast this
    rw [hNdef]; linarith
  have hszu : ∀ X, (sz a b c X : ℝ) ≤ N := by
    intro X
    have : sz a b c X ≤ a + b + c := by fin_cases X <;> simp [sz] <;> omega
    rw [hNdef]; exact_mod_cast this
  have hszl' : ∀ X, N / 4 ≤ (sz a c b X : ℝ) := by
    intro X
    have : a + b + c ≤ 4 * sz a c b X := by fin_cases X <;> simp [sz] <;> omega
    have : (((a + b + c : ℕ) : ℝ)) ≤ 4 * (sz a c b X : ℝ) := by exact_mod_cast this
    rw [hNdef]; linarith
  have hszu' : ∀ X, (sz a c b X : ℝ) ≤ N := by
    intro X
    have : sz a c b X ≤ a + b + c := by fin_cases X <;> simp [sz] <;> omega
    rw [hNdef]; exact_mod_cast this
  have hdiff : ∀ X, ((sz a b c X : ℝ) - sz a b c (X + 1)) ^ 2 ≤ 2 * N := by
    intro X; have := sq_diff_le h X; rw [sz_csz, sz_csz] at this; exact this
  have hdiff' : ∀ X, ((sz a c b X : ℝ) - sz a c b (X + 1)) ^ 2 ≤ 2 * N := by
    intro X
    have := sq_diff_le h' X; rw [sz_csz, sz_csz] at this
    rw [hNdef, show a + b + c = a + c + b by omega]; exact this
  have hlarge := large_counts_R N (fun X => sz a b c X) (fun X => d X) (fun X => q X) (fun X => r X)
    hN40 hszl hszu hdiff (fun X => by positivity) (fun X => by positivity)
    (fun X => by have := hdq X; exact_mod_cast this)
    (fun X => by have := hEq X; exact_mod_cast this) X₀
    (by rw [hNdef]; exact_mod_cast hX₀)
  have hlarge' := large_counts_R N (fun X => sz a c b X) (fun X => d' X) (fun X => q' X)
    (fun X => r' X) hN40 hszl' hszu' hdiff' (fun X => by positivity) (fun X => by positivity)
    (fun X => by have := hdq' X; exact_mod_cast this)
    (fun X => by have := hEq' X; exact_mod_cast this) Y₀
    (by rw [hNdef, show a + b + c = a + c + b by omega]; exact_mod_cast hY₀)
  -- the six counts
  have hq := h.2.2.2.2.1
  have hqR : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 - a * b - a * c - b * c = a + b + c := by
    exact_mod_cast hq
  have hNabc : N = (a : ℝ) + b + c := by rw [hNdef]; push_cast; ring
  have ht2 : (c : ℝ) * q 2 + r 2 = t := by exact_mod_cast ht
  have hthalf : ((a * (a - 1) / 2 - t : ℕ) : ℝ) = ch a - t := by
    rw [Nat.cast_sub (by omega), cast_half]
  have ht2' : (b : ℝ) * q' 2 + r' 2 = ch a - t := by rw [← hthalf]; exact_mod_cast ht'
  have E0 := hEq 0; have E2 := hEq 2; have D0 := hdq 0; have D2 := hdq 2
  have E0' := hEq' 0; have E2' := hEq' 2; have D0' := hdq' 0; have D2' := hdq' 2
  simp only [sz] at E0 E2 D0 D2 E0' E2' D0' D2'
  norm_num at E0 E2 D0 D2 E0' E2' D0' D2'
  have e0 : ((a * d 0 + 2 * r 0 : ℕ) : ℝ) = ((2 * (c * q 2 + r 2) : ℕ) : ℝ) := by rw [E0]
  have e2 : ((c * d 2 + 2 * r 2 : ℕ) : ℝ) = ((2 * (b * q 1 + r 1) : ℕ) : ℝ) := by rw [E2]
  have e0' : ((a * d' 0 + 2 * r' 0 : ℕ) : ℝ) = ((2 * (b * q' 2 + r' 2) : ℕ) : ℝ) := by rw [E0']
  have e2' : ((b * d' 2 + 2 * r' 2 : ℕ) : ℝ) = ((2 * (c * q' 1 + r' 1) : ℕ) : ℝ) := by rw [E2']
  have d0 : (d 0 : ℝ) = a - 1 - b + 2 * q 0 := by exact_mod_cast D0
  have d2 : (d 2 : ℝ) = c - 1 - a + 2 * q 2 := by exact_mod_cast D2
  have d0' : (d' 0 : ℝ) = a - 1 - c + 2 * q' 0 := by exact_mod_cast D0'
  have d2' : (d' 2 : ℝ) = b - 1 - a + 2 * q' 2 := by exact_mod_cast D2'
  push_cast at e0 e2 e0' e2'
  have L0 := hlarge 0; have L1 := hlarge 1; have L2 := hlarge 2
  have U0 := hlarge' 0; have U1 := hlarge' 1; have U2 := hlarge' 2
  simp only [sz] at L0 L1 L2 U0 U1 U2
  norm_num at L0 L1 L2 U0 U1 U2
  unfold ch at ht2'
  have hK0 : (a : ℝ) * q 0 + r 0 = a * b / 2 - a * (a - 1) / 2 + t := by
    linear_combination (1 / 2) * e0 - ((a : ℝ) / 2) * d0 + ht2
  have hK1 : (b : ℝ) * q 1 + r 1 = b * c / 2 - b * (b - 1) / 2 + a * b / 2 - a * (a - 1) / 2 + t := by
    linear_combination (-1 / 2) * e2 + ((c : ℝ) / 2) * d2 + ht2 + (1 / 2) * hqR
  have hK0' : (a : ℝ) * q' 0 + r' 0 = a * c / 2 - t := by
    linear_combination (1 / 2) * e0' - ((a : ℝ) / 2) * d0' + ht2'
  have hK1' : (c : ℝ) * q' 1 + r' 1 = b * (b - 1) / 2 - a * b / 2 + a * (a - 1) / 2 - t := by
    linear_combination (-1 / 2) * e2' + ((b : ℝ) / 2) * d2' + ht2'
  have hδ : 1 / 10 ^ 17 * N ^ 2 = N ^ 2 / 10 ^ 17 := by ring
  obtain ⟨S, hS, -, -, -, hcount⟩ := h₁ a b c h hn₁ t (by
    simp only [cntAAB, cntAAC, cntBBC, cntABB, cntACC, cntBCC, ch]
    rw [← hNdef, hδ]
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩)
  exact ⟨S, hS, hcount⟩

end CDRBicolour.Absorption.Corners
