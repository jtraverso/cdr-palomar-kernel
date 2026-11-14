/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.Bridge
public import CDRBicolour.KBicolor.Wilson.ExplicitCounting

/-!
# A wider sufficient cap for the four-colour arithmetic application

The constant six replaces seven in a new, separate interface. The original
CapRep and all earlier theorems are unchanged. A norm-sensitive estimate
preserves the class floor 1/16 with seed margin 1/1000 once v is at least 4096.
Existence of representations in this wider cap remains an arithmetic input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CDRBicolour.KBicolor
open Finset TypedTriangle

def CapRepSix (v : ℕ) : Prop :=
  ∃ a b c : ℤ, 3*(a^2+b^2+c^2)=(v : ℤ)*(v+8) ∧ 6*|b|≤a ∧ 6*|c|≤a

theorem cap_six_bounds {v : ℕ} (hv : 4096 ≤ v) {a b c : ℤ}
    (he : 3*(a^2+b^2+c^2)=(v : ℤ)*(v+8)) (hb : 6*|b|≤a) (hc : 6*|c|≤a) :
    4*(a+|b|+|c|)≤3*v ∧ 750*(a+|b|)≤499*v ∧ 750*(a+|c|)≤499*v := by
  have hvz : (4096 : ℤ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℤ) < v := by omega
  have hvv : 4096*(v : ℤ) ≤ (v : ℤ)^2 := by nlinarith
  have hb0 := abs_nonneg b
  have hc0 := abs_nonneg c
  have ha : 0 ≤ a := by omega
  have hprod := mul_nonneg (show 0 ≤ a-3*(|b|+|c|) by omega)
    (show 0 ≤ 13*a+|b|+|c| by omega)
  have hL : 57*(a+|b|+|c|)^2 ≤ 32*(v : ℤ)*(v+8) := by
    nlinarith [sq_abs b,sq_abs c,sq_nonneg (|b|-|c|)]
  have pair : ∀ x y : ℤ, 0≤x → 0≤y → 6*x≤a →
      3*(a^2+x^2+y^2)=(v : ℤ)*(v+8) → 750*(a+x)≤499*v := by
    intro x y hx hy hxa hnorm
    have hp := mul_nonneg (show 0 ≤ a-6*x by omega) (show 0 ≤ 12*a-2*x by omega)
    have hh : 111*(a+x)^2 ≤ 49*(v : ℤ)*(v+8) := by nlinarith [sq_nonneg y]
    by_contra h
    push Not at h
    have hs := mul_lt_mul'' h h (by positivity) (by positivity)
    nlinarith
  refine ⟨?_,pair |b| |c| hb0 hc0 hb (by simpa only [sq_abs] using he),
    pair |c| |b| hc0 hb0 hc (by nlinarith [sq_abs b,sq_abs c])⟩
  by_contra h
  push Not at h
  have hs := mul_lt_mul'' h h (by positivity) (by positivity)
  nlinarith

theorem split_of_cap_six {v : ℕ} (hv4096 : 4096 ≤ v) (hv : v % 2 = 1) {a b c : ℤ}
    (he : 3 * (a ^ 2 + b ^ 2 + c ^ 2) = (v : ℤ) * (v + 8)) (hb : 6 * |b| ≤ a) (hc : 6 * |c| ≤ a) :
    ∃ cs : Fin 4 → ℕ, ∑ X, cs X = v ∧ 3 * ∑ X, cs X * (cs X - 1) = v * (v - 1) ∧
      (∀ X, v ≤ 16 * cs X) ∧ ∀ X Y, 1500 * |(cs X : ℤ) - cs Y| ≤ 499 * v := by
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
  obtain ⟨hL,hB,hC⟩ := cap_six_bounds hv4096 he hb hc
  have hb0 := abs_nonneg b
  have hc0 := abs_nonneg c
  have hbL := neg_abs_le b
  have hbU := le_abs_self b
  have hcL := neg_abs_le c
  have hcU := le_abs_self c
  have hvz : (4096 : ℤ) ≤ v := by exact_mod_cast hv4096
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
        1500 * |x - y| ≤ 499 * (v : ℤ) := by
      intro x y hx hy
      rw [show (1500 : ℤ) * |x - y| = |1500 * (x - y)| by rw [abs_mul]; norm_num, abs_le]
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


theorem seed_of_cap_six_split {v : ℕ} (hv : 0 < v) (cs : Fin 4 → ℕ)
    (hs : ∑ X,cs X=v) (hd : 3*∑ X,cs X*(cs X-1)=v*(v-1))
    (hgap : ∀ X Y,1500*|(cs X : ℤ)-cs Y|≤499*v) :
    ∃ a,SeedData cs (1/1000) a := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hsR : ∑ X,(cs X : ℝ)=v := by exact_mod_cast hs
  have hqR := Wilson.profile_square_of_div cs hs hd
  refine ⟨fun X Y => 1/2+3*((cs X : ℝ)-cs Y)/(2*v),fun X Y h => by ring,
    fun X Y h => ?_,fun X => ?_⟩
  · have hgR : 1500*|(cs X : ℝ)-cs Y|≤499*v := by exact_mod_cast hgap X Y
    have hn := neg_abs_le ((cs X : ℝ)-cs Y)
    have hh : -(499 : ℝ)/1000≤3*((cs X : ℝ)-cs Y)/(2*v) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  · exact seed_row (fun X => (cs X : ℝ)) v hvR.ne' hsR hqR X

/-- All original combinatorial and robust seed conditions, from a constant-six witness. -/
theorem profile_of_cap_six {v : ℕ} (hv : 4096 ≤ v)
    (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepSix v) :
    ∃ cs : Fin 4 → ℕ, (∑ X,cs X=v) ∧
      3*∑ X,cs X*(cs X-1)=v*(v-1) ∧ (∀ X,v≤16*cs X) ∧
      (∀ X Y,X≠Y → Even (cs X*cs Y)) ∧ ∃ a,SeedData cs (1/1000) a := by
  obtain ⟨a,b,c,he,hb,hc⟩ := hcap
  have hodd : v%2=1 := by omega
  obtain ⟨cs,hs,hd,hlo,hgap⟩ := split_of_cap_six hv hodd he hb hc
  exact ⟨cs,hs,hd,hlo,even_products_four cs hodd hs hd,
    seed_of_cap_six_split (by omega) cs hs hd hgap⟩

def capSixCountingThreshold (ε : ℝ) : ℕ :=
  max 4096 (Wilson.sharpCountThreshold (k := 4) (by norm_num) (1/16) (1/1000) ε)

/-- A labelled four-colour profile and both sharp bounds, at a specified threshold. -/
theorem sharp_counting_of_cap_six {ε : ℝ} (hε : 0 < ε) {v : ℕ}
    (hv : capSixCountingThreshold ε≤v) (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepSix v) :
    ∃ lab : Fin v → Fin 4, (∀ X,0<ksz lab X) ∧ 0<kCount lab ∧
      (1/6-ε)*(v : ℝ)^2*Real.log v≤Real.log (kCount lab) ∧
      Real.log (kCount lab)≤(1/6+ε)*(v : ℝ)^2*Real.log v := by
  have hv4 : 4096≤v := (le_max_left _ _).trans hv
  obtain ⟨cs,hs,hd,hlo,heven,hseed⟩ := profile_of_cap_six hv4 hadm hcap
  obtain ⟨lab,hlab⟩ := exists_lab cs hs
  have hsize : ksz lab=cs := funext hlab
  have hpos : ∀ X,0<ksz lab X := by
    intro X
    rw [hlab]
    have := hlo X
    omega
  refine ⟨lab,hpos,?_⟩
  apply Wilson.sharp_counting_at_explicit_order (by norm_num : 4≤4)
    (by norm_num : (0 : ℝ)<1/16) (by norm_num : (0 : ℝ)<1/1000) hε v lab
    ((le_max_right _ _).trans hv) (show Odd v from ⟨v/2,by omega⟩)
  · simpa only [hsize] using heven
  · simpa only [hsize] using hd
  · intro X
    rw [hlab]
    have hh : (v : ℝ)≤16*(cs X : ℝ) := by exact_mod_cast hlo X
    linarith
  · simpa only [hsize] using hseed

theorem cap_seven_implies_cap_six {v : ℕ} (h : CapRep v) : CapRepSix v := by
  obtain ⟨a,b,c,he,hb,hc⟩ := h
  exact ⟨a,b,c,he,by linarith [abs_nonneg b],by linarith [abs_nonneg c]⟩

theorem bicolourable_of_positive_kCount {v k : ℕ} (lab : Fin v → Fin k)
    (hpos : ∀ X,0<ksz lab X) (hcount : 0<kCount lab) :
    CDRBicolour.PaperIII.Bicolourable v k := by
  classical
  obtain ⟨D,hD⟩ := card_pos.mp hcount
  have hh : _root_.STS.IsSTS D ∧ ∀ B ∈ D,(B.image lab).card=2 := by
    simpa only [kBlocks,mem_filter,mem_univ,true_and] using hD
  refine ⟨D,lab,hh.1,?_,hh.2⟩
  intro X
  have h := hpos X
  unfold ksz at h
  obtain ⟨x,hx⟩ := card_pos.mp h
  exact ⟨x,(mem_filter.mp hx).2⟩

theorem cap_six_bicolourable {v : ℕ} (hv : capSixCountingThreshold (1/12)≤v)
    (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepSix v) :
    CDRBicolour.PaperIII.Bicolourable v 4 := by
  obtain ⟨lab,hpos,hcount,-,-⟩ := sharp_counting_of_cap_six (by norm_num : (0 : ℝ)<1/12) hv hadm hcap
  exact bicolourable_of_positive_kCount lab hpos hcount

theorem conj35_large_of_cap_six
    (hcap : ∃ V₀ : ℕ,∀ v,V₀≤v → (v%6=1 ∨ v%6=3) → CapRepSix v) :
    ∃ V₀ : ℕ,∀ v,V₀≤v → CDRBicolour.PaperIII.Admissible v →
      CDRBicolour.PaperIII.Bicolourable v 4 := by
  obtain ⟨V₀,hV⟩ := hcap
  refine ⟨max V₀ (capSixCountingThreshold (1/12)),fun v hv hadm => ?_⟩
  exact cap_six_bicolourable ((le_max_right _ _).trans hv) hadm
    (hV v ((le_max_left _ _).trans hv) hadm)

end CDRBicolour.KBicolor
