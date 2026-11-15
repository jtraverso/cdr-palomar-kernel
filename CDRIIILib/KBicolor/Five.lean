/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Four

/-!
# Five colour classes: CDR Conjecture 3.6 for large orders from a near-profile split

Colbourn–Dinitz–Rosa (1999), Conjecture 3.6: a 5-bicolourable STS(v) exists iff
`v ≡ 1, 3 (mod 6)`, `v ≥ 31`, `v ≠ 33, 37, 43, 45, 61`.

For five classes the closed-form seed of `Four.lean` is not available (the square identity forces
class gaps ≈ v/3). We add a fixed rational circulation `F5` to it: the seed
`a X Y = 1/2 + 3 (c X - c Y)/(2v) + F5 X Y · v² / (c X · c Y)` still satisfies the row identities
exactly (a circulation contributes nothing), and it is `≥ 1/100` whenever every class is within
`v/400` of `P5 X · v`, for the profile `P5 ≈ (0.115, 0.424, 0.369, 0.060, 0.032)`. The profile has
`P5 0 + P5 2 = P5 1 + P5 3`, so the target direction of the three-squares representation has
middle coordinate `0` and the cap is symmetric under `b ↦ -b`; of `(a, b, c)` and `(a, -b, c)`
exactly one gives an integral split, so no congruence condition is needed.

**Arithmetic input (`Near5 v`).** A 5-split of `v` (divisibility identity) with `c 4` even and
`|c X - P5 X · v| ≤ v/400`. With `c 4` even, `w = v - c 4` is odd and the remaining four classes
correspond to a representation of `M = 4 (v(v+2)/3 - c₄²) - w² ≡ 3 (mod 8)` as a sum of three
squares in a small cap; by Duke–Schulze-Pillot (Theorem 3(ii)) such a representation exists for
all large `v` (as for `CapRep`). Not formalized here.

`conj36_of_near5`: if `Near5 v` holds for all large admissible `v`, every large admissible `v`
has a 5-bicolourable STS.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

/-- The target profile. -/
def P5 : Fin 5 → ℝ := ![72 / 625, 1059 / 2500, 7373 / 20000, 241 / 4000, 323 / 10000]

/-- A rational circulation on the five classes. -/
def F5 : Fin 5 → Fin 5 → ℝ :=
  ![![0, 0, -169 / 50000, 219 / 100000, 119 / 100000],
    ![0, 0, 169 / 50000, -89 / 50000, -1 / 625],
    ![169 / 50000, -169 / 50000, 0, 17 / 50000, -17 / 50000],
    ![-219 / 100000, 89 / 50000, -17 / 50000, 0, 3 / 4000],
    ![-119 / 100000, 1 / 625, 17 / 50000, -3 / 4000, 0]]

theorem F5_antisymm (X Y : Fin 5) : F5 X Y + F5 Y X = 0 := by
  fin_cases X <;> fin_cases Y <;> norm_num [F5]

theorem F5_diag (X : Fin 5) : F5 X X = 0 := by
  fin_cases X <;> norm_num [F5]

theorem F5_row (X : Fin 5) : ∑ Y, F5 X Y = 0 := by
  rw [Fin.sum_univ_five]; fin_cases X <;> norm_num [F5]

/-- The profile is exactly symmetric: `P5 0 + P5 2 = P5 1 + P5 3` (needed by the arithmetic). -/
theorem P5_symm : P5 0 + P5 2 = P5 1 + P5 3 := by norm_num [P5]

theorem P5_sum : ∑ X, P5 X = 1 := by rw [Fin.sum_univ_five]; norm_num [P5]

/-- The arithmetic input for five classes. -/
def Near5 (v : ℕ) : Prop :=
  ∃ cs : Fin 5 → ℕ, ∑ X, cs X = v ∧ 3 * ∑ X, cs X * (cs X - 1) = v * (v - 1) ∧ cs 4 % 2 = 0 ∧
    ∀ X, |(cs X : ℝ) - P5 X * v| ≤ v / 400

/-! ### Parity -/

theorem nat_sq_mod_four (n : ℕ) : n * n % 4 = n % 2 := by
  have h : n * n % 4 = (n % 4) * (n % 4) % 4 := Nat.mul_mod _ _ _
  have h2 : n % 2 = n % 4 % 2 := by omega
  rw [h, h2]
  have h4 := Nat.mod_lt n (by norm_num : 0 < 4)
  generalize n % 4 = r at h4 ⊢
  interval_cases r <;> rfl

set_option maxHeartbeats 1000000 in
/-- The arithmetic core of the parity statement. -/
theorem five_parity (c0 c1 c2 c3 c4 v : ℕ) (hv : v % 2 = 1) (hs : c0 + c1 + c2 + c3 + c4 = v)
    (hd : 3 * (c0 * (c0 - 1) + c1 * (c1 - 1) + c2 * (c2 - 1) + c3 * (c3 - 1) + c4 * (c4 - 1)) =
      v * (v - 1)) (h4 : c4 % 2 = 0) :
    ¬ (c0 % 2 = 1 ∧ c1 % 2 = 1) ∧ ¬ (c0 % 2 = 1 ∧ c2 % 2 = 1) ∧
      ¬ (c0 % 2 = 1 ∧ c3 % 2 = 1) ∧ ¬ (c1 % 2 = 1 ∧ c2 % 2 = 1) ∧
      ¬ (c1 % 2 = 1 ∧ c3 % 2 = 1) ∧ ¬ (c2 % 2 = 1 ∧ c3 % 2 = 1) := by
  have q : ∀ n : ℕ, n * (n - 1) + n = n * n := by
    intro n; rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_self _)]
  have q0 := q c0; have q1 := q c1; have q2 := q c2; have q3 := q c3; have q4 := q c4
  have qv := q v
  have s0 := nat_sq_mod_four c0; have s1 := nat_sq_mod_four c1
  have s2 := nat_sq_mod_four c2; have s3 := nat_sq_mod_four c3
  have s4 := nat_sq_mod_four c4; have sv := nat_sq_mod_four v
  generalize c0 * (c0 - 1) = w0 at q0 hd
  generalize c1 * (c1 - 1) = w1 at q1 hd
  generalize c2 * (c2 - 1) = w2 at q2 hd
  generalize c3 * (c3 - 1) = w3 at q3 hd
  generalize c4 * (c4 - 1) = w4 at q4 hd
  generalize v * (v - 1) = W at qv hd
  generalize c0 * c0 = t0 at q0 s0
  generalize c1 * c1 = t1 at q1 s1
  generalize c2 * c2 = t2 at q2 s2
  generalize c3 * c3 = t3 at q3 s3
  generalize c4 * c4 = t4 at q4 s4
  generalize v * v = V2 at qv sv
  omega

/-- With five classes and the last one even, the divisibility identity leaves exactly one odd
class. -/
theorem even_products_five (c : Fin 5 → ℕ) {v : ℕ} (hv : v % 2 = 1) (hs : ∑ X, c X = v)
    (hd : 3 * ∑ X, c X * (c X - 1) = v * (v - 1)) (h4 : c 4 % 2 = 0) :
    ∀ X Y, X ≠ Y → Even (c X * c Y) := by
  rw [Fin.sum_univ_five] at hs hd
  obtain ⟨p01, p02, p03, p12, p13, p23⟩ := five_parity _ _ _ _ _ _ hv hs hd h4
  clear hs hd
  intro X Y h
  rw [Nat.even_mul, Nat.even_iff, Nat.even_iff]
  fin_cases X <;> fin_cases Y <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ne_eq,
      not_true_eq_false] at h ⊢ <;> omega

/-! ### The seed -/

/-- The closed-form part of the seed satisfies the row identities (five classes). -/
theorem seed_row5 (c : Fin 5 → ℝ) (v : ℝ) (hv : v ≠ 0) (hs : ∑ X, c X = v)
    (hq : 3 * ∑ X, c X ^ 2 = v ^ 2 + 2 * v) (X : Fin 5) :
    ∑ Y ∈ univ.filter (fun Y => Y ≠ X), c Y * (1 / 2 + 3 * (c X - c Y) / (2 * v)) = c X - 1 := by
  rw [Finset.filter_ne', Finset.sum_erase_eq_sub (mem_univ X)]
  rw [Fin.sum_univ_five] at hs hq ⊢
  have h2 : (2 * v) ≠ 0 := by positivity
  fin_cases X <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    field_simp
  · linear_combination (v + 3 * c 0) * hs - hq
  · linear_combination (v + 3 * c 1) * hs - hq
  · linear_combination (v + 3 * c 2) * hs - hq
  · linear_combination (v + 3 * c 3) * hs - hq
  · linear_combination (v + 3 * c 4) * hs - hq

/-- The circulation part contributes nothing to the rows. -/
theorem circ_row (c : Fin 5 → ℝ) (v : ℝ) (hc : ∀ X, c X ≠ 0) (X : Fin 5) :
    ∑ Y ∈ univ.filter (fun Y => Y ≠ X), c Y * (F5 X Y * v ^ 2 / (c X * c Y)) = 0 := by
  have e : ∀ Y, c Y * (F5 X Y * v ^ 2 / (c X * c Y)) = F5 X Y * (v ^ 2 / c X) := by
    intro Y; have := hc X; have := hc Y; field_simp
  rw [sum_congr rfl fun Y _ => e Y, ← sum_mul, Finset.filter_ne',
    Finset.sum_erase_eq_sub (mem_univ X), F5_row, F5_diag, sub_zero, zero_mul]

/-- Lower bound for one pair on a box. -/
theorem pair_lb {F lx hx ly hy tx ty : ℝ} (hlx : 0 < lx) (hly : 0 < ly) (h1 : lx ≤ tx)
    (h2 : tx ≤ hx) (h3 : ly ≤ ty) (h4 : ty ≤ hy) :
    1 / 2 + 3 / 2 * (lx - hy) + (if 0 ≤ F then F / (hx * hy) else F / (lx * ly)) ≤
      1 / 2 + 3 / 2 * (tx - ty) + F / (tx * ty) := by
  have htx : 0 < tx := by linarith
  have hty : 0 < ty := by linarith
  have hm1 : lx * ly ≤ tx * ty := mul_le_mul h1 h3 hly.le htx.le
  have hm2 : tx * ty ≤ hx * hy := mul_le_mul h2 h4 hty.le (by linarith)
  split_ifs with hF
  · have : F / (hx * hy) ≤ F / (tx * ty) := div_le_div_of_nonneg_left hF (by positivity) hm2
    linarith
  · push Not at hF
    have : F / (lx * ly) ≤ F / (tx * ty) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith

/-- The explicit seed is `≥ 1/100` on the box `|c X / v - P5 X| ≤ 1/400`. -/
theorem seed5_lower (t : Fin 5 → ℝ) (ht : ∀ X, |t X - P5 X| ≤ 1 / 400) (X Y : Fin 5)
    (h : X ≠ Y) : 1 / 100 ≤ 1 / 2 + 3 / 2 * (t X - t Y) + F5 X Y / (t X * t Y) := by
  have hb : ∀ Z, P5 Z - 1 / 400 ≤ t Z ∧ t Z ≤ P5 Z + 1 / 400 := by
    intro Z; have := abs_le.1 (ht Z); constructor <;> linarith [this.1, this.2]
  have hpos : ∀ Z, 0 < P5 Z - 1 / 400 := by intro Z; fin_cases Z <;> norm_num [P5]
  refine le_trans ?_ (pair_lb (F := F5 X Y) (hpos X) (hpos Y) (hb X).1 (hb X).2 (hb Y).1 (hb Y).2)
  fin_cases X <;> fin_cases Y <;> simp at h <;> norm_num [P5, F5]

/-! ### The theorem -/

/-- **Colbourn–Dinitz–Rosa, Conjecture 3.6, for all large orders, from the arithmetic input.** -/
theorem conj36_of_near5
    (hnear : ∃ V₀ : ℕ, ∀ v, V₀ ≤ v → (v % 6 = 1 ∨ v % 6 = 3) → Near5 v) :
    ∃ n₀ : ℕ, ∀ v, n₀ ≤ v → (v % 6 = 1 ∨ v % 6 = 3) →
      ∃ lab : Fin v → Fin 5, (∀ X, 0 < ksz lab X) ∧
        ∃ D : Finset (Finset (Fin v)), IsDecomposition (kHost lab) (bicF 5) (edges (kHost lab)) D := by
  obtain ⟨V₀, hV⟩ := hnear
  obtain ⟨n₁, hT⟩ := kbicolour_eventually 5 (by norm_num) (δ := 1 / 34) (η := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max (max V₀ n₁) 1000, fun v hv hadm => ?_⟩
  have hv0 : V₀ ≤ v := le_trans (le_max_left _ _) (le_max_left _ _ |>.trans hv)
  have hv1 : n₁ ≤ v := le_trans (le_max_right _ _) (le_max_left _ _ |>.trans hv)
  have hv2 : 1000 ≤ v := le_trans (le_max_right _ _) hv
  obtain ⟨cs, hs, hd, h4, hbox⟩ := hV v hv0 hadm
  have hodd : v % 2 = 1 := by omega
  obtain ⟨lab, hlab⟩ := exists_lab cs hs
  have hk : ksz lab = cs := funext hlab
  have h1000 : (1000 : ℝ) ≤ v := by exact_mod_cast hv2
  have hvR : (0 : ℝ) < v := by linarith
  -- each class is at least `v/34`
  have hlow : ∀ X, (1 / 34 : ℝ) * v ≤ cs X := by
    intro X
    have hb := (abs_le.1 (hbox X)).1
    have hp : (1 / 34 : ℝ) + 1 / 400 ≤ P5 X := by fin_cases X <;> norm_num [P5]
    nlinarith
  have hcpos : ∀ X, (0 : ℝ) < cs X := fun X => by have := hlow X; nlinarith
  have hpos : ∀ X, 0 < ksz lab X := by
    intro X; rw [hlab]; exact_mod_cast hcpos X
  refine ⟨lab, hpos, ?_⟩
  have hoddv : Odd v := ⟨v / 2, by omega⟩
  refine hT v lab hv1 hoddv (fun X => ?_) (fun X Y h => ?_) ?_ ?_
  · rw [hlab]; exact hlow X
  · rw [hk]; exact even_products_five cs hodd hs hd h4 X Y h
  · rw [hk]; exact hd
  · rw [hk]
    have hge : ∀ X, 1 ≤ cs X := fun X => by have := hcpos X; exact_mod_cast this
    have hsR : ∑ X, (cs X : ℝ) = v := by exact_mod_cast hs
    have hqR : 3 * ∑ X, (cs X : ℝ) ^ 2 = (v : ℝ) ^ 2 + 2 * v := by
      have h1 : ((3 * ∑ X, cs X * (cs X - 1) : ℕ) : ℝ) = ((v * (v - 1) : ℕ) : ℝ) := by
        exact_mod_cast hd
      push_cast [Nat.cast_sub (hge _), Nat.cast_sub (by omega : 1 ≤ v)] at h1
      have h2 : ∑ X, (cs X : ℝ) * ((cs X : ℝ) - 1) = ∑ X, (cs X : ℝ) ^ 2 - ∑ X, (cs X : ℝ) := by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun X _ => by ring
      rw [h2, hsR] at h1
      linarith
    refine ⟨fun X Y => 1 / 2 + 3 * ((cs X : ℝ) - cs Y) / (2 * v) +
      F5 X Y * (v : ℝ) ^ 2 / ((cs X : ℝ) * cs Y), fun X Y h => ?_, fun X Y h => ?_, fun X => ?_⟩
    · have := F5_antisymm X Y
      have hX := hcpos X; have hY := hcpos Y
      field_simp
      linear_combination (2 * (v : ℝ) * (v : ℝ) ^ 2) * this
    · have ht : ∀ Z, |(cs Z : ℝ) / v - P5 Z| ≤ 1 / 400 := by
        intro Z
        rw [show (cs Z : ℝ) / v - P5 Z = ((cs Z : ℝ) - P5 Z * v) / v by field_simp, abs_div,
          abs_of_pos hvR, div_le_iff₀ hvR]
        linarith [hbox Z]
      have key := seed5_lower (fun Z => (cs Z : ℝ) / v) ht X Y h
      have hX := hcpos X; have hY := hcpos Y
      have e : 1 / 2 + 3 * ((cs X : ℝ) - cs Y) / (2 * v) + F5 X Y * (v : ℝ) ^ 2 / ((cs X : ℝ) * cs Y)
          = 1 / 2 + 3 / 2 * ((cs X : ℝ) / v - (cs Y : ℝ) / v) +
            F5 X Y / ((cs X : ℝ) / v * ((cs Y : ℝ) / v)) := by
        field_simp
      beta_reduce; rw [e]; exact key
    · have hrow := seed_row5 (fun X => (cs X : ℝ)) v hvR.ne' hsR hqR X
      have hcirc := circ_row (fun X => (cs X : ℝ)) v (fun X => (hcpos X).ne') X
      beta_reduce
      calc _ = ∑ Y ∈ univ.filter (fun Y => Y ≠ X),
            ((cs Y : ℝ) * (1 / 2 + 3 * ((cs X : ℝ) - cs Y) / (2 * v)) +
              (cs Y : ℝ) * (F5 X Y * (v : ℝ) ^ 2 / ((cs X : ℝ) * cs Y))) :=
            sum_congr rfl fun Y _ => by ring
        _ = (cs X : ℝ) - 1 := by rw [sum_add_distrib, hrow, hcirc, add_zero]

end CDRBicolour.KBicolor
