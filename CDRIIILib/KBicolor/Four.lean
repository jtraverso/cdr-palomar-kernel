/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Main

/-!
# Four colour classes: from a sum of three squares to a 4-bicolourable STS

Colbourn–Dinitz–Rosa (1999), Conjecture 3.5: a 4-bicolourable STS(v) exists iff
`v ≡ 1, 3 (mod 6)`, `v ≥ 15`, `v ≠ 21, 31`.

**Arithmetic input (`CapRep v`).** `3 (a² + b² + c²) = v (v + 8)` with `7|b|, 7|c| ≤ a`: a
representation of `N = v(v+8)/3` as a sum of three squares in a cap around an axis. As `v → ∞`
such representations exist by the equidistribution of lattice points on spheres (Duke;
Duke–Schulze-Pillot), which is not formalized here; numerically every admissible `v` in
`[2357, 20000]` has one.

**From `CapRep` to a split.** `N ≡ 3 (mod 8)` forces `a, b, c` odd; with
`f = (a+b+c, a-b-c, -a+b-c, -a-b+c)` and a sign `s = ±1` with `4 ∣ v + s f₀`, the class sizes
`(v + s fᵢ)/4` are integers summing to `v` with `3 Σ c(c-1) = v(v-1)`; at most one is odd
(a mod-4 argument). The cap gives every class `≥ v/16` and `|c_X - c_Y| ≤ (4/7) a`, so the
closed-form seed `a_XY = 1/2 + 3(c_X - c_Y)/(2v)` is `≥ 1/400` once `v ≥ 1000`.

`conj35_of_capRep`: if `CapRep v` holds for all large admissible `v`, then every large
admissible `v` has a 4-bicolourable STS (Theorem T of Paper III via `kbicolour_eventually`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

/-- A representation of `v(v+8)/3` as a sum of three squares in the cap `7|b|, 7|c| ≤ a`. -/
def CapRep (v : ℕ) : Prop :=
  ∃ a b c : ℤ, 3 * (a ^ 2 + b ^ 2 + c ^ 2) = (v : ℤ) * (v + 8) ∧ 7 * |b| ≤ a ∧ 7 * |c| ≤ a

/-! ### Residues -/

theorem sq_mod_eight (a : ℤ) :
    (a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 4) ∧ a % 2 = 0 ∨ a ^ 2 % 8 = 1 ∧ a % 2 = 1 := by
  have h : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := by rw [pow_two, pow_two, Int.mul_emod]
  have h2 : a % 2 = a % 8 % 2 := by omega
  have h0 := Int.emod_nonneg a (by norm_num : (8 : ℤ) ≠ 0)
  have h8 := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 8)
  rw [h, h2]
  generalize a % 8 = r at h0 h8 ⊢
  interval_cases r <;> decide

theorem nat_mul_pred_mod_four (c : ℕ) :
    c * (c - 1) % 4 = 0 ∧ (c % 4 = 0 ∨ c % 4 = 1) ∨ c * (c - 1) % 4 = 2 ∧ (c % 4 = 2 ∨ c % 4 = 3) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have h1 : (c - 1) % 4 = (c % 4 + 3) % 4 := by omega
  have h : c * (c - 1) % 4 = (c % 4) * ((c % 4 + 3) % 4) % 4 := by
    rw [Nat.mul_mod, h1]
  rw [h]
  have h4 := Nat.mod_lt c (by norm_num : 0 < 4)
  generalize c % 4 = r at h4 ⊢
  interval_cases r <;> decide

/-- With four classes, the divisibility identity leaves at most one class odd. -/
theorem even_products_four (c : Fin 4 → ℕ) {v : ℕ} (hv : v % 2 = 1) (hs : ∑ X, c X = v)
    (hd : 3 * ∑ X, c X * (c X - 1) = v * (v - 1)) :
    ∀ X Y, X ≠ Y → Even (c X * c Y) := by
  rw [Fin.sum_univ_four] at hs hd
  have e0 := nat_mul_pred_mod_four (c 0)
  have e1 := nat_mul_pred_mod_four (c 1)
  have e2 := nat_mul_pred_mod_four (c 2)
  have e3 := nat_mul_pred_mod_four (c 3)
  have ev := nat_mul_pred_mod_four v
  generalize c 0 * (c 0 - 1) = w0 at e0 hd
  generalize c 1 * (c 1 - 1) = w1 at e1 hd
  generalize c 2 * (c 2 - 1) = w2 at e2 hd
  generalize c 3 * (c 3 - 1) = w3 at e3 hd
  generalize v * (v - 1) = W at ev hd
  have hpar : ¬ (c 0 % 2 = 1 ∧ c 1 % 2 = 1) ∧ ¬ (c 0 % 2 = 1 ∧ c 2 % 2 = 1) ∧
      ¬ (c 0 % 2 = 1 ∧ c 3 % 2 = 1) ∧ ¬ (c 1 % 2 = 1 ∧ c 2 % 2 = 1) ∧
      ¬ (c 1 % 2 = 1 ∧ c 3 % 2 = 1) ∧ ¬ (c 2 % 2 = 1 ∧ c 3 % 2 = 1) := by
    omega
  intro X Y h
  rw [Nat.even_mul, Nat.even_iff, Nat.even_iff]
  obtain ⟨p01, p02, p03, p12, p13, p23⟩ := hpar
  fin_cases X <;> fin_cases Y <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ne_eq,
      not_true_eq_false] at h ⊢ <;> omega

/-! ### The split -/

/-- From a cap representation: an integral 4-split with the divisibility identity, balanced
classes and nearby class sizes. -/
theorem split_of_cap {v : ℕ} (hv1000 : 1000 ≤ v) (hv : v % 2 = 1) {a b c : ℤ}
    (he : 3 * (a ^ 2 + b ^ 2 + c ^ 2) = (v : ℤ) * (v + 8)) (hb : 7 * |b| ≤ a) (hc : 7 * |c| ≤ a) :
    ∃ cs : Fin 4 → ℕ, ∑ X, cs X = v ∧ 3 * ∑ X, cs X * (cs X - 1) = v * (v - 1) ∧
      (∀ X, v ≤ 16 * cs X) ∧ ∀ X Y, 600 * |(cs X : ℤ) - cs Y| ≤ 199 * v := by
  -- parities
  have pa := sq_mod_eight a
  have pb := sq_mod_eight b
  have pc := sq_mod_eight c
  have pv := sq_mod_eight (v : ℤ)
  have hvz : (v : ℤ) % 2 = 1 := by exact_mod_cast hv
  have hodd : a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 := by
    have he' : 3 * (a ^ 2 + b ^ 2 + c ^ 2) = (v : ℤ) ^ 2 + 8 * v := by rw [he]; ring
    generalize a ^ 2 = A at pa he'
    generalize b ^ 2 = B at pb he'
    generalize c ^ 2 = C at pc he'
    generalize (v : ℤ) ^ 2 = W at pv he'
    omega
  obtain ⟨ha2, hb2, hc2⟩ := hodd
  -- the sign
  have hsgn : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ 4 ∣ (v : ℤ) + s * (a + b + c) ∧
      4 ∣ (v : ℤ) + s * (a - b - c) ∧ 4 ∣ (v : ℤ) + s * (-a + b - c) ∧
      4 ∣ (v : ℤ) + s * (-a - b + c) := by
    by_cases h4 : 4 ∣ (v : ℤ) + (a + b + c)
    · refine ⟨1, Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;> omega
    · refine ⟨-1, Or.inr rfl, ?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨s, hs, d0, d1, d2, d3⟩ := hsgn
  obtain ⟨q0, hq0⟩ := d0
  obtain ⟨q1, hq1⟩ := d1
  obtain ⟨q2, hq2⟩ := d2
  obtain ⟨q3, hq3⟩ := d3
  -- bounds from the cap
  have hb1 : -a ≤ 7 * b := by have := neg_abs_le b; linarith
  have hb2 : 7 * b ≤ a := by have := le_abs_self b; linarith
  have hc1 : -a ≤ 7 * c := by have := neg_abs_le c; linarith
  have hc2 : 7 * c ≤ a := by have := le_abs_self c; linarith
  have hvz : (1000 : ℤ) ≤ v := by exact_mod_cast hv1000
  have hvv : (1000 : ℤ) * v ≤ v * v := by nlinarith
  have h3a : 3 * a ^ 2 ≤ (v : ℤ) * (v + 8) := by nlinarith [sq_nonneg b, sq_nonneg c]
  have ha0 : 0 ≤ a := by linarith
  have a12 : 12 * a ≤ 7 * v := by
    by_contra h; push Not at h
    have := mul_lt_mul'' h h (by positivity) (by positivity)
    nlinarith
  have a24 : 2400 * a ≤ 1393 * v := by
    by_contra h; push Not at h
    have := mul_lt_mul'' h h (by positivity) (by positivity)
    nlinarith
  -- the class sizes
  have hsum : q0 + q1 + q2 + q3 = v := by rcases hs with rfl | rfl <;> linarith
  have hsq : 3 * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2 + q3 ^ 2) = (v : ℤ) ^ 2 + 2 * v := by
    have e0 : (4 * q0) ^ 2 = ((v : ℤ) + s * (a + b + c)) ^ 2 := by rw [hq0]
    have e1 : (4 * q1) ^ 2 = ((v : ℤ) + s * (a - b - c)) ^ 2 := by rw [hq1]
    have e2 : (4 * q2) ^ 2 = ((v : ℤ) + s * (-a + b - c)) ^ 2 := by rw [hq2]
    have e3 : (4 * q3) ^ 2 = ((v : ℤ) + s * (-a - b + c)) ^ 2 := by rw [hq3]
    have h16 : 16 * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2 + q3 ^ 2) = 4 * (v : ℤ) ^ 2 + 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      rcases hs with rfl | rfl <;> linear_combination e0 + e1 + e2 + e3
    linarith
  have lo : ∀ q : ℤ, (4 * q = (v : ℤ) + s * (a + b + c) ∨ 4 * q = (v : ℤ) + s * (a - b - c) ∨
      4 * q = (v : ℤ) + s * (-a + b - c) ∨ 4 * q = (v : ℤ) + s * (-a - b + c)) → (v : ℤ) ≤ 16 * q := by
    intro q hq
    rcases hs with rfl | rfl <;> rcases hq with h | h | h | h <;> linarith
  have g0 : (v : ℤ) ≤ 16 * q0 := lo q0 (Or.inl hq0.symm)
  have g1 : (v : ℤ) ≤ 16 * q1 := lo q1 (Or.inr (Or.inl hq1.symm))
  have g2 : (v : ℤ) ≤ 16 * q2 := lo q2 (Or.inr (Or.inr (Or.inl hq2.symm)))
  have g3 : (v : ℤ) ≤ 16 * q3 := lo q3 (Or.inr (Or.inr (Or.inr hq3.symm)))
  have t0 : ((q0.toNat : ℕ) : ℤ) = q0 := Int.toNat_of_nonneg (by linarith)
  have t1 : ((q1.toNat : ℕ) : ℤ) = q1 := Int.toNat_of_nonneg (by linarith)
  have t2 : ((q2.toNat : ℕ) : ℤ) = q2 := Int.toNat_of_nonneg (by linarith)
  have t3 : ((q3.toNat : ℕ) : ℤ) = q3 := Int.toNat_of_nonneg (by linarith)
  have u0 : 1 ≤ q0.toNat := by omega
  have u1 : 1 ≤ q1.toNat := by omega
  have u2 : 1 ≤ q2.toNat := by omega
  have u3 : 1 ≤ q3.toNat := by omega
  refine ⟨![q0.toNat, q1.toNat, q2.toNat, q3.toNat], ?_, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    omega
  · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have : ((3 * (q0.toNat * (q0.toNat - 1) + q1.toNat * (q1.toNat - 1) +
        q2.toNat * (q2.toNat - 1) + q3.toNat * (q3.toNat - 1)) : ℕ) : ℤ) = ((v * (v - 1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub u0, Nat.cast_sub u1, Nat.cast_sub u2, Nat.cast_sub u3,
        Nat.cast_sub (by omega : 1 ≤ v)]
      rw [t0, t1, t2, t3]
      linear_combination hsq - 3 * hsum
    exact_mod_cast this
  · intro X
    fin_cases X <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;> omega
  · have key : ∀ x y : ℤ, (x = q0 ∨ x = q1 ∨ x = q2 ∨ x = q3) → (y = q0 ∨ y = q1 ∨ y = q2 ∨ y = q3) →
        600 * |x - y| ≤ 199 * (v : ℤ) := by
      intro x y hx hy
      rw [show (600 : ℤ) * |x - y| = |600 * (x - y)| by rw [abs_mul]; norm_num, abs_le]
      rcases hs with rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;> constructor <;> linarith
    intro X Y
    have hX : ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] X : ℕ) : ℤ) = q0 ∨
        ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] X : ℕ) : ℤ) = q1 ∨
        ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] X : ℕ) : ℤ) = q2 ∨
        ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] X : ℕ) : ℤ) = q3 := by
      fin_cases X <;> simp [t0, t1, t2, t3]
    have hY : ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] Y : ℕ) : ℤ) = q0 ∨
        ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] Y : ℕ) : ℤ) = q1 ∨
        ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] Y : ℕ) : ℤ) = q2 ∨
        ((![q0.toNat, q1.toNat, q2.toNat, q3.toNat] Y : ℕ) : ℤ) = q3 := by
      fin_cases Y <;> simp [t0, t1, t2, t3]
    exact key _ _ hX hY

/-! ### The labelling and the theorem -/

/-- A labelling of `Fin n` with prescribed class sizes. -/
theorem exists_lab {k n : ℕ} (c : Fin k → ℕ) (hs : ∑ X, c X = n) :
    ∃ lab : Fin n → Fin k, ∀ X, ksz lab X = c X := by
  classical
  let e : Fin n ≃ (Σ X : Fin k, Fin (c X)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_sigma, hs])
  refine ⟨fun x => (e x).1, fun X => ?_⟩
  unfold ksz
  rw [Finset.card_equiv e (t := univ.filter fun y : (Σ X : Fin k, Fin (c X)) => y.1 = X)
    (by intro x; simp)]
  have : (univ.filter fun y : (Σ X : Fin k, Fin (c X)) => y.1 = X) =
      (univ : Finset (Fin (c X))).map (Function.Embedding.sigmaMk X) := by
    ext ⟨i, j⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.sigmaMk_apply]
    constructor
    · rintro rfl; exact ⟨j, rfl⟩
    · rintro ⟨j', h⟩; exact (Sigma.mk.inj_iff.1 h).1.symm
  rw [this, card_map, card_univ, Fintype.card_fin]

/-- The closed-form seed `1/2 + 3 (c_X - c_Y)/(2v)` satisfies the row identities. -/
theorem seed_row (c : Fin 4 → ℝ) (v : ℝ) (hv : v ≠ 0) (hs : ∑ X, c X = v)
    (hq : 3 * ∑ X, c X ^ 2 = v ^ 2 + 2 * v) (X : Fin 4) :
    ∑ Y ∈ univ.filter (fun Y => Y ≠ X), c Y * (1 / 2 + 3 * (c X - c Y) / (2 * v)) = c X - 1 := by
  rw [Finset.filter_ne', Finset.sum_erase_eq_sub (mem_univ X)]
  rw [Fin.sum_univ_four] at hs hq ⊢
  have h2 : (2 * v) ≠ 0 := by positivity
  fin_cases X <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    field_simp
  · linear_combination (v + 3 * c 0) * hs - hq
  · linear_combination (v + 3 * c 1) * hs - hq
  · linear_combination (v + 3 * c 2) * hs - hq
  · linear_combination (v + 3 * c 3) * hs - hq

/-- **Colbourn–Dinitz–Rosa, Conjecture 3.5, for all large orders, from the arithmetic input.** -/
theorem conj35_of_capRep
    (hcap : ∃ V₀ : ℕ, ∀ v, V₀ ≤ v → (v % 6 = 1 ∨ v % 6 = 3) → CapRep v) :
    ∃ n₀ : ℕ, ∀ v, n₀ ≤ v → (v % 6 = 1 ∨ v % 6 = 3) →
      ∃ lab : Fin v → Fin 4, (∀ X, 0 < ksz lab X) ∧
        ∃ D : Finset (Finset (Fin v)), IsDecomposition (kHost lab) (bicF 4) (edges (kHost lab)) D := by
  obtain ⟨V₀, hV⟩ := hcap
  obtain ⟨n₁, hT⟩ := kbicolour_eventually 4 (by norm_num) (δ := 1 / 16) (η := 1 / 400)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max (max V₀ n₁) 1000, fun v hv hadm => ?_⟩
  have hv0 : V₀ ≤ v := le_trans (le_max_left _ _) (le_max_left _ _ |>.trans hv)
  have hv1 : n₁ ≤ v := le_trans (le_max_right _ _) (le_max_left _ _ |>.trans hv)
  have hv2 : 1000 ≤ v := le_trans (le_max_right _ _) hv
  obtain ⟨a, b, c, he, hb, hc⟩ := hV v hv0 hadm
  have hodd : v % 2 = 1 := by omega
  obtain ⟨cs, hs, hd, hlo, hgap⟩ := split_of_cap hv2 hodd he hb hc
  obtain ⟨lab, hlab⟩ := exists_lab cs hs
  have hk : ksz lab = cs := funext hlab
  have hpos : ∀ X, 0 < ksz lab X := by
    intro X; rw [hlab]; have := hlo X; omega
  refine ⟨lab, hpos, ?_⟩
  have hoddv : Odd v := ⟨v / 2, by omega⟩
  refine hT v lab hv1 hoddv (fun X => ?_) (fun X Y h => ?_) ?_ ?_
  · rw [hlab]; have := hlo X
    have : (v : ℝ) ≤ 16 * (cs X : ℝ) := by exact_mod_cast this
    linarith
  · rw [hk]; exact even_products_four cs hodd hs hd X Y h
  · rw [hk]; exact hd
  · rw [hk]
    have h1000 : (1000 : ℝ) ≤ v := by exact_mod_cast hv2
    have hvR : (0 : ℝ) < v := by linarith
    have hge : ∀ X, 1 ≤ cs X := fun X => by have := hlo X; omega
    have hsR : ∑ X, (cs X : ℝ) = v := by exact_mod_cast hs
    have hqR : 3 * ∑ X, (cs X : ℝ) ^ 2 = (v : ℝ) ^ 2 + 2 * v := by
      have h1 : ((3 * ∑ X, cs X * (cs X - 1) : ℕ) : ℝ) = ((v * (v - 1) : ℕ) : ℝ) := by
        exact_mod_cast hd
      push_cast [Nat.cast_sub (hge _), Nat.cast_sub (by omega : 1 ≤ v)] at h1
      have h2 : ∑ X, (cs X : ℝ) * ((cs X : ℝ) - 1) = ∑ X, (cs X : ℝ) ^ 2 - ∑ X, (cs X : ℝ) := by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun X _ => by ring
      rw [h2, hsR] at h1
      linarith
    refine ⟨fun X Y => 1 / 2 + 3 * ((cs X : ℝ) - cs Y) / (2 * v), fun X Y h => by ring,
      fun X Y h => ?_, fun X => ?_⟩
    · have hg := hgap X Y
      have hgR : 600 * |(cs X : ℝ) - cs Y| ≤ 199 * v := by exact_mod_cast hg
      have hn := neg_abs_le ((cs X : ℝ) - cs Y)
      have : -(199 : ℝ) / 400 ≤ 3 * ((cs X : ℝ) - cs Y) / (2 * v) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith
    · exact seed_row (fun X => (cs X : ℝ)) v hvR.ne' hsR hqR X

end CDRBicolour.KBicolor
