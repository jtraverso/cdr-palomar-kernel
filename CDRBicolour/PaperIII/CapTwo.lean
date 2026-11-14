/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.CapSix
public import CDRBicolour.PaperIII.FourSeedGale

/-!
# A constant-two cap via cut feasibility

The seed is constructed by the imported Gale-Hoffman proof and verified cut
margins. No additional flow or seed hypothesis is introduced. Representation
existence in this wider fixed cone remains an explicit arithmetic input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CDRBicolour.KBicolor
open Finset TypedTriangle

def CapRepTwo (v : ℕ) : Prop :=
  ∃ a b c : ℤ,3*(a^2+b^2+c^2)=(v : ℤ)*(v+8) ∧ 2*|b|≤a ∧ 2*|c|≤a

theorem cap_two_bound {v : ℕ} (hv : 78400≤v) {a b c : ℤ}
    (he : 3*(a^2+b^2+c^2)=(v : ℤ)*(v+8)) (hb : 2*|b|≤a) (hc : 2*|c|≤a) :
    35*(a+|b|+|c|)≤33*v := by
  have hvZ : (78400 : ℤ)≤v := by exact_mod_cast hv
  have hvv : 78400*(v : ℤ)≤(v : ℤ)^2 := by nlinarith
  have hb0 := abs_nonneg b
  have hc0 := abs_nonneg c
  have ha : 0≤a := by omega
  have hp := mul_nonneg (show 0≤a-|b|-|c| by omega) (show 0≤5*a-|b|-|c| by omega)
  have hh : 9*(a+|b|+|c|)^2≤8*(v : ℤ)*(v+8) := by
    nlinarith only [he,hp,sq_abs b,sq_abs c,sq_nonneg (|b|-|c|)]
  by_contra h
  push Not at h
  have hsq := mul_lt_mul'' h h (by positivity) (by positivity)
  nlinarith only [hh,hsq,hvv]

theorem split_of_cap_two {v : ℕ} (hv78400 : 78400 ≤ v) (hv : v % 2 = 1) {a b c : ℤ}
    (he : 3 * (a ^ 2 + b ^ 2 + c ^ 2) = (v : ℤ) * (v + 8)) (hb : 2 * |b| ≤ a) (hc : 2 * |c| ≤ a) :
    ∃ cs : Fin 4 → ℕ, ∑ X, cs X = v ∧ 3 * ∑ X, cs X * (cs X - 1) = v * (v - 1) ∧
      (∀ X, v ≤ 70 * cs X) ∧ ∀ X, 70 * cs X ≤ 34 * v := by
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
  -- The norm equation improves the crude separate coordinate estimates.
  have hL := cap_two_bound hv78400 he hb hc
  have hb0 := abs_nonneg b
  have hc0 := abs_nonneg c
  have hbL := neg_abs_le b
  have hbU := le_abs_self b
  have hcL := neg_abs_le c
  have hcU := le_abs_self c
  have hvz : (78400 : ℤ) ≤ v := by exact_mod_cast hv78400
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
      4 * q = (v : ℤ) + s * (-a + b - c) ∨ 4 * q = (v : ℤ) + s * (-a - b + c)) → (v : ℤ) ≤ 70 * q := by
    intro q hq
    rcases hs with rfl | rfl <;> rcases hq with h | h | h | h <;> linarith
  have g0 : (v : ℤ) ≤ 70 * q0 := lo q0 (Or.inl hq0.symm)
  have g1 : (v : ℤ) ≤ 70 * q1 := lo q1 (Or.inr (Or.inl hq1.symm))
  have g2 : (v : ℤ) ≤ 70 * q2 := lo q2 (Or.inr (Or.inr (Or.inl hq2.symm)))
  have g3 : (v : ℤ) ≤ 70 * q3 := lo q3 (Or.inr (Or.inr (Or.inr hq3.symm)))
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
  · have hi : ∀ q : ℤ, (4*q=(v : ℤ)+s*(a+b+c) ∨ 4*q=(v : ℤ)+s*(a-b-c) ∨
        4*q=(v : ℤ)+s*(-a+b-c) ∨ 4*q=(v : ℤ)+s*(-a-b+c)) → 70*q≤34*v := by
      intro q hq
      rcases hs with rfl | rfl <;> rcases hq with h | h | h | h <;> linarith
    have h0 := hi q0 (Or.inl hq0.symm)
    have h1 := hi q1 (Or.inr (Or.inl hq1.symm))
    have h2 := hi q2 (Or.inr (Or.inr (Or.inl hq2.symm)))
    have h3 := hi q3 (Or.inr (Or.inr (Or.inr hq3.symm)))
    intro X
    fin_cases X <;> simp only [Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons] <;> omega

theorem profile_of_cap_two {v : ℕ} (hv : 78400≤v)
    (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepTwo v) :
    ∃ cs : Fin 4 → ℕ,(∑ X,cs X=v) ∧
      3*∑ X,cs X*(cs X-1)=v*(v-1) ∧ (∀ X,v≤70*cs X) ∧
      (∀ X Y,X≠Y → Even (cs X*cs Y)) ∧ ∃ a,SeedData cs (1/137) a := by
  obtain ⟨a,b,c,he,hb,hc⟩ := hcap
  have hodd : v%2=1 := by omega
  obtain ⟨cs,hs,hd,hlo,hhi⟩ := split_of_cap_two hv hodd he hb hc
  have hqR := Wilson.profile_square_of_div cs hs hd
  have hqZ : 3*∑ X,(cs X : ℤ)^2=(v : ℤ)^2+2*v := by exact_mod_cast hqR
  exact ⟨cs,hs,hd,hlo,even_products_four cs hodd hs hd,
    CDRBicolour.PaperIII.seed_of_robust_four_profile (by omega) cs hs hqZ hlo hhi⟩

def capTwoCountingThreshold (ε : ℝ) : ℕ :=
  max 78400 (Wilson.sharpCountThreshold (k := 4) (by norm_num) (1/70) (1/137) ε)

/-- A labelled four-colour profile and both sharp bounds, at a specified threshold. -/
theorem sharp_counting_of_cap_two {ε : ℝ} (hε : 0 < ε) {v : ℕ}
    (hv : capTwoCountingThreshold ε≤v) (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepTwo v) :
    ∃ lab : Fin v → Fin 4, (∀ X,0<ksz lab X) ∧ 0<kCount lab ∧
      (1/6-ε)*(v : ℝ)^2*Real.log v≤Real.log (kCount lab) ∧
      Real.log (kCount lab)≤(1/6+ε)*(v : ℝ)^2*Real.log v := by
  have hv4 : 78400≤v := (le_max_left _ _).trans hv
  obtain ⟨cs,hs,hd,hlo,heven,hseed⟩ := profile_of_cap_two hv4 hadm hcap
  obtain ⟨lab,hlab⟩ := exists_lab cs hs
  have hsize : ksz lab=cs := funext hlab
  have hpos : ∀ X,0<ksz lab X := by
    intro X
    rw [hlab]
    have := hlo X
    omega
  refine ⟨lab,hpos,?_⟩
  apply Wilson.sharp_counting_at_explicit_order (by norm_num : 4≤4)
    (by norm_num : (0 : ℝ)<1/70) (by norm_num : (0 : ℝ)<1/137) hε v lab
    ((le_max_right _ _).trans hv) (show Odd v from ⟨v/2,by omega⟩)
  · simpa only [hsize] using heven
  · simpa only [hsize] using hd
  · intro X
    rw [hlab]
    have hh : (v : ℝ)≤70*(cs X : ℝ) := by exact_mod_cast hlo X
    linarith
  · simpa only [hsize] using hseed

theorem cap_six_implies_cap_two {v : ℕ} (h : CapRepSix v) : CapRepTwo v := by
  obtain ⟨a,b,c,he,hb,hc⟩ := h
  exact ⟨a,b,c,he,by linarith [abs_nonneg b],by linarith [abs_nonneg c]⟩

theorem cap_two_bicolourable {v : ℕ} (hv : capTwoCountingThreshold (1/12)≤v)
    (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepTwo v) :
    CDRBicolour.PaperIII.Bicolourable v 4 := by
  obtain ⟨lab,hpos,hcount,-,-⟩ := sharp_counting_of_cap_two (by norm_num : (0 : ℝ)<1/12) hv hadm hcap
  exact bicolourable_of_positive_kCount lab hpos hcount

theorem conj35_large_of_cap_two
    (hcap : ∃ V₀ : ℕ,∀ v,V₀≤v → (v%6=1 ∨ v%6=3) → CapRepTwo v) :
    ∃ V₀ : ℕ,∀ v,V₀≤v → CDRBicolour.PaperIII.Admissible v →
      CDRBicolour.PaperIII.Bicolourable v 4 := by
  obtain ⟨V₀,hV⟩ := hcap
  refine ⟨max V₀ (capTwoCountingThreshold (1/12)),fun v hv hadm => ?_⟩
  exact cap_two_bicolourable ((le_max_right _ _).trans hv) hadm
    (hV v ((le_max_left _ _).trans hv) hadm)


end CDRBicolour.KBicolor
