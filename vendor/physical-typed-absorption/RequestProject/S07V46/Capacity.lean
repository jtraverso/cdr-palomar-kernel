/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# V46 §3 — prefix capacity arithmetic (localized scale, real constants)

Step costs `a ℓ ≥ 0` obey the chain recurrence `a ℓ ≤ A (1 + b ℓ + M ∑_{k<ℓ} a k)` (§2), where
`b ℓ` is the step monitor of the ORIGINAL charge.  Prefix sums of stratum lengths:
`S t = ∑_{i ≤ t} m i`.

* `geomG A M t = A ∑_{k ≤ t} (1+AM)^k` and `gammaL A M L = A (L+1) (1+AM)^L` (host-free).
* `cum_bound` : if `b ℓ ≤ E` for `ℓ ≤ t` then `∑_{k ≤ t} a k ≤ geomG t · (1 + E)`.
* `local_scale` : the LOCALIZED monitor scale `η n |Z|` is converted, BEFORE any recurrence, into a
  multiple of the prefix length: from `γ n ≤ q` and `q |Z| ≤ c S` one gets `η n |Z| ≤ (η c / γ) S`.
* `prefix_capacity` (the criterion): with `θ = η c / γ ≤ 1`, `2 Γ ≤ P`, `1 ≤ m 0`, localized step
  bounds `b ℓ ≤ θ S ℓ` for `ℓ < J` and the FULL bound `b J ≤ τ'` only at the last step, and
  `1 + τ' ≤ S J`, every prefix satisfies `∑_{k ≤ t} a k ≤ P · S t` (`t ≤ J`).

The full budget `τ'` (= `τ n²`) enters ONLY the last prefix `t = J`; the prefixes `t < J` are
checked against `θ S t` alone, so short strata are not charged a host-quadratic error.  The
additive `1` (bounded torsion: a zero monitor does not mean a zero class) is absorbed by
`S t ≥ 1` and the colour multiplicity `P ≥ 2Γ`.
-/

@[expose] public section

namespace S07V46

open Finset

/-- `A ∑_{k ≤ t} (1 + A M)^k` -/
noncomputable def geomG (A M : ℕ) (t : ℕ) : ℝ := A * ∑ k ∈ range (t + 1), ((1 : ℝ) + A * M) ^ k

/-- the host-free constant `A (L+1) (1+AM)^L` -/
def gammaL (A M L : ℕ) : ℕ := A * (L + 1) * (1 + A * M) ^ L

lemma geomG_succ (A M t : ℕ) :
    geomG A M (t + 1) = (1 + A * M) * geomG A M t + A := by
  unfold geomG
  rw [sum_range_succ', pow_zero, mul_add, mul_sum, mul_sum, mul_sum]
  simp only [pow_succ]
  rw [mul_one]
  congr 1
  exact sum_congr rfl fun i _ => by ring

lemma geomG_nonneg (A M t : ℕ) : 0 ≤ geomG A M t := by
  unfold geomG; positivity

lemma geomG_le_gammaL {A M L t : ℕ} (ht : t ≤ L) : geomG A M t ≤ gammaL A M L := by
  unfold geomG gammaL
  push_cast
  have h1 : (1 : ℝ) ≤ 1 + A * M := by nlinarith [(Nat.cast_nonneg A : (0:ℝ) ≤ A),
    (Nat.cast_nonneg M : (0:ℝ) ≤ M)]
  have hs : ∑ k ∈ range (t + 1), ((1 : ℝ) + A * M) ^ k ≤ ((L : ℝ) + 1) * (1 + A * M) ^ L := by
    calc ∑ k ∈ range (t + 1), ((1 : ℝ) + A * M) ^ k
        ≤ ∑ _k ∈ range (t + 1), ((1 : ℝ) + A * M) ^ L :=
          sum_le_sum fun k hk => pow_le_pow_right₀ h1 (by simp at hk; omega)
      _ = (t + 1) * (1 + A * M) ^ L := by simp
      _ ≤ ((L : ℝ) + 1) * (1 + A * M) ^ L := by
          gcongr
  calc (A : ℝ) * ∑ k ∈ range (t + 1), ((1 : ℝ) + A * M) ^ k
      ≤ A * (((L : ℝ) + 1) * (1 + A * M) ^ L) := by gcongr
    _ = A * (L + 1) * (1 + A * M) ^ L := by ring

/-- **cumulative bound** of the chain recurrence under a uniform step-monitor bound `E` -/
theorem cum_bound (A M : ℕ) (a b : ℕ → ℝ) (E : ℝ) :
    ∀ t, (∀ ℓ ≤ t, a ℓ ≤ A * (1 + b ℓ + M * ∑ k ∈ range ℓ, a k)) → (∀ ℓ ≤ t, b ℓ ≤ E) →
      ∑ k ∈ range (t + 1), a k ≤ geomG A M t * (1 + E) := by
  intro t
  induction t with
  | zero =>
    intro hrec hb
    have := hrec 0 le_rfl
    have hb0 := hb 0 le_rfl
    simp only [range_zero, sum_empty, mul_zero, add_zero] at this ⊢
    unfold geomG
    simp only [zero_add, range_one, sum_singleton, pow_zero, mul_one]
    calc a 0 ≤ A * (1 + b 0) := this
      _ ≤ A * (1 + E) := by gcongr
  | succ t ih =>
    intro hrec hb
    have ih' := ih (fun ℓ hℓ => hrec ℓ (by omega)) (fun ℓ hℓ => hb ℓ (by omega))
    have ht := hrec (t + 1) le_rfl
    have hbt := hb (t + 1) le_rfl
    rw [sum_range_succ, geomG_succ]
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    set Cs := ∑ k ∈ range (t + 1), a k
    calc Cs + a (t + 1) ≤ Cs + A * (1 + E + M * Cs) := by
          gcongr
          calc a (t + 1) ≤ A * (1 + b (t + 1) + M * Cs) := ht
            _ ≤ A * (1 + E + M * Cs) := by gcongr
      _ = (1 + A * M) * Cs + A * (1 + E) := by ring
      _ ≤ (1 + A * M) * (geomG A M t * (1 + E)) + A * (1 + E) := by
          gcongr
      _ = ((1 + A * M) * geomG A M t + A) * (1 + E) := by ring

/-- **localized scale ⇒ prefix scale** (`n / q` cancelled before any recurrence) -/
theorem local_scale {eta gamma : ℝ} (hγ : 0 < gamma) (hη : 0 ≤ eta) {n q z c S : ℕ}
    (hq : gamma * n ≤ q) (hpre : q * z ≤ c * S) :
    eta * n * z ≤ (eta * c / gamma) * S := by
  have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hpre' : (q : ℝ) * z ≤ c * S := by exact_mod_cast hpre
  have h1 : gamma * (n * z) ≤ c * S := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
  nlinarith

/-- **The prefix-capacity criterion.** -/
theorem prefix_capacity (A M P L J : ℕ) (hJL : J ≤ L) (m : ℕ → ℕ) (a b : ℕ → ℝ)
    {θ τ' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hτ : 0 ≤ τ')
    (hrec : ∀ ℓ ≤ J, a ℓ ≤ A * (1 + b ℓ + M * ∑ k ∈ range ℓ, a k))
    (hloc : ∀ ℓ < J, b ℓ ≤ θ * ∑ i ∈ range (ℓ + 1), (m i : ℝ))
    (hfull : b J ≤ τ')
    (hP : 2 * gammaL A M L ≤ P) (hm0 : 1 ≤ m 0)
    (hSJ : 1 + τ' ≤ ∑ i ∈ range (J + 1), (m i : ℝ)) :
    ∀ t ≤ J, ∑ k ∈ range (t + 1), a k ≤ P * ∑ i ∈ range (t + 1), (m i : ℝ) := by
  intro t ht
  have hSmono : ∀ {s s' : ℕ}, s ≤ s' →
      ∑ i ∈ range (s + 1), (m i : ℝ) ≤ ∑ i ∈ range (s' + 1), (m i : ℝ) := fun h =>
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun _ _ _ => Nat.cast_nonneg _
  have hS1 : (1 : ℝ) ≤ ∑ i ∈ range (t + 1), (m i : ℝ) := by
    calc (1 : ℝ) ≤ m 0 := by exact_mod_cast hm0
      _ = ∑ i ∈ range (0 + 1), (m i : ℝ) := by simp
      _ ≤ _ := hSmono (Nat.zero_le t)
  set St := ∑ i ∈ range (t + 1), (m i : ℝ)
  have hG := geomG_le_gammaL (A := A) (M := M) (ht.trans hJL)
  have hG0 := geomG_nonneg A M t
  have hP' : (2 : ℝ) * gammaL A M L ≤ P := by exact_mod_cast hP
  have hSt0 : 0 ≤ St := by linarith
  rcases lt_or_eq_of_le ht with hlt | heq
  · -- a prefix strictly before the last step: localized bounds only
    have hb : ∀ ℓ ≤ t, b ℓ ≤ θ * St := fun ℓ hℓ =>
      (hloc ℓ (by omega)).trans (mul_le_mul_of_nonneg_left (hSmono hℓ) hθ0)
    have hc := cum_bound A M a b (θ * St) t (fun ℓ hℓ => hrec ℓ (by omega)) hb
    calc ∑ k ∈ range (t + 1), a k ≤ geomG A M t * (1 + θ * St) := hc
      _ ≤ gammaL A M L * (St + St) := by
          refine mul_le_mul hG (by nlinarith) (by positivity) (by positivity)
      _ = 2 * gammaL A M L * St := by ring
      _ ≤ P * St := by gcongr
  · -- the last prefix: the full budget enters only here
    subst heq
    have hb : ∀ ℓ ≤ t, b ℓ ≤ θ * St + τ' := by
      intro ℓ hℓ
      rcases lt_or_eq_of_le hℓ with h | h
      · have := (hloc ℓ h).trans (mul_le_mul_of_nonneg_left (hSmono hℓ) hθ0); linarith
      · subst h; nlinarith
    have hc := cum_bound A M a b (θ * St + τ') t hrec hb
    calc ∑ k ∈ range (t + 1), a k ≤ geomG A M t * (1 + (θ * St + τ')) := hc
      _ ≤ gammaL A M L * (St + St) := by
          refine mul_le_mul hG (by nlinarith) (by positivity) (by positivity)
      _ = 2 * gammaL A M L * St := by ring
      _ ≤ P * St := by gcongr

end S07V46
