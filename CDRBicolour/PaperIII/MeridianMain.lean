/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.AxisTwoInput

/-!
# The general k-colour theorem from a meridian-only representation input

The original statements and proofs are untouched. The split proof below is
the original proof with its representation provider restricted to directions
whose second coordinate vanishes. The sole changed proof call supplies that
vanishing-coordinate equality explicitly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CDRBicolour.PaperIII
open Finset CDRBicolour.KBicolor

def MeridianThreeSquaresDense : Prop :=
  ∀ u : Fin 3 → ℝ,(∑ i,u i^2)=1 → u 1=0 → ∀ ε>0,∃ N₀ : ℕ,
    ∀ n : ℕ,N₀≤n → n%8=3 → ∃ x : Fin 3 → ℤ,(∑ i,x i^2)=(n : ℤ) ∧
      ∀ i,|(x i : ℝ)-Real.sqrt n*u i|≤ε*Real.sqrt n

theorem meridian_of_threeSquaresDense (hA : ThreeSquaresDense) : MeridianThreeSquaresDense := by
  intro u hu _ ε hε
  exact hA u hu ε hε

theorem split_near_meridian (hA : MeridianThreeSquaresDense) {k : ℕ} (hk : 5 ≤ k) (p : Fin k → ℝ)
    (hp : ∀ X, 0 < p X) (h1 : ∑ X, p X = 1) (h2 : ∑ X, p X ^ 2 = 1 / 3)
    (hsym : p ⟨0, by omega⟩ + p ⟨2, by omega⟩ = p ⟨1, by omega⟩ + p ⟨3, by omega⟩)
    (hne : p ⟨2, by omega⟩ < p ⟨0, by omega⟩) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ V₀ : ℕ, ∀ v, V₀ ≤ v → Admissible v → ∃ c : Fin k → ℕ, ∑ X, c X = v ∧
      3 * ∑ X, c X * (c X - 1) = v * (v - 1) ∧ (∀ X Y, X ≠ Y → Even (c X * c Y)) ∧
      ∀ X, |(c X : ℝ) - p X * v| ≤ ρ * v := by
  classical
  have hk4 : 4 ≤ k := by omega
  -- the four free coordinates and the fixed part
  have hs1 := sum_split4 hk4 p
  have hs2 := sum_split4 hk4 (fun X => p X ^ 2)
  beta_reduce at hs2
  obtain ⟨q0, hq0⟩ : ∃ q, q = p ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ q, q = p ⟨1, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q, q = p ⟨2, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q, q = p ⟨3, by omega⟩ := ⟨_, rfl⟩
  rw [← hq0, ← hq1, ← hq2, ← hq3] at hs1 hs2 hsym
  rw [← hq0, ← hq2] at hne
  obtain ⟨Fx, hFx⟩ : ∃ S : Finset (Fin k), S = univ.filter (fun X : Fin k => 4 ≤ X.val) :=
    ⟨_, rfl⟩
  rw [← hFx] at hs1 hs2
  have hmemFx : ∀ X ∈ Fx, 4 ≤ X.val := fun X hX => by
    rw [hFx] at hX; exact (mem_filter.1 hX).2
  obtain ⟨PF, hPF⟩ : ∃ r : ℝ, r = ∑ X ∈ Fx, p X := ⟨_, rfl⟩
  obtain ⟨QF, hQF⟩ : ∃ r : ℝ, r = ∑ X ∈ Fx, p X ^ 2 := ⟨_, rfl⟩
  rw [← hPF] at hs1
  rw [← hQF] at hs2
  have hq0p : 0 < q0 := by rw [hq0]; exact hp _
  have hq1p : 0 < q1 := by rw [hq1]; exact hp _
  have hq2p : 0 < q2 := by rw [hq2]; exact hp _
  have hq3p : 0 < q3 := by rw [hq3]; exact hp _
  have hW : q0 + q1 + q2 + q3 + PF = 1 := by linarith
  have hSq : q0 ^ 2 + q1 ^ 2 + q2 ^ 2 + q3 ^ 2 + QF = 1 / 3 := by linarith
  have hPF0 : 0 ≤ PF := by rw [hPF]; exact sum_nonneg fun X _ => (hp X).le
  have hPF1 : PF ≤ 1 := by linarith
  -- the direction
  have hq1' : q1 = q0 + q2 - q3 := by linarith
  obtain ⟨u0, hu0⟩ : ∃ u : ℝ, u = 2 * (q0 - q3) := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u : ℝ, u = 2 * (q3 - q2) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ r : ℝ, r = u0 ^ 2 + u2 ^ 2 := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm, hu0, hu2]; exact mpos_aux hne
  have hmW : m = 4 * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2 + q3 ^ 2) - (q0 + q1 + q2 + q3) ^ 2 := by
    rw [hm, hu0, hu2, hq1']; ring
  obtain ⟨sm, hsm⟩ : ∃ s : ℝ, s = Real.sqrt m := ⟨_, rfl⟩
  have hsm0 : 0 < sm := by rw [hsm]; exact Real.sqrt_pos.2 hmpos
  have hsm2 : sm ^ 2 = m := by rw [hsm]; exact Real.sq_sqrt hmpos.le
  have hunit : ∑ i, (![u0 / sm, 0, u2 / sm] : Fin 3 → ℝ) i ^ 2 = 1 := by
    rw [Fin.sum_univ_three]
    show (u0 / sm) ^ 2 + 0 ^ 2 + (u2 / sm) ^ 2 = 1
    have e : (u0 / sm) ^ 2 + 0 ^ 2 + (u2 / sm) ^ 2 = (u0 ^ 2 + u2 ^ 2) / sm ^ 2 := by ring
    rw [e, hsm2, ← hm, div_self hmpos.ne']
  -- the minimal class and the constants
  obtain ⟨X₀, -, hX₀⟩ :=
    (univ : Finset (Fin k)).exists_min_image p ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨pm, hpm⟩ : ∃ r : ℝ, r = p X₀ := ⟨_, rfl⟩
  have hpm0 : 0 < pm := by rw [hpm]; exact hp X₀
  have hq0m : pm ≤ q0 := by rw [hq0, hpm]; exact hX₀ _ (mem_univ _)
  have hq1m : pm ≤ q1 := by rw [hq1, hpm]; exact hX₀ _ (mem_univ _)
  have hq2m : pm ≤ q2 := by rw [hq2, hpm]; exact hX₀ _ (mem_univ _)
  have hq3m : pm ≤ q3 := by rw [hq3, hpm]; exact hX₀ _ (mem_univ _)
  obtain ⟨ρ', hρ'⟩ : ∃ r : ℝ, r = min ρ (pm / 2) := ⟨_, rfl⟩
  have hρ'0 : 0 < ρ' := by rw [hρ']; exact lt_min hρ (by linarith)
  have hρ'ρ : ρ' ≤ ρ := by rw [hρ']; exact min_le_left _ _
  have hρ'pm : ρ' ≤ pm / 2 := by rw [hρ']; exact min_le_right _ _
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨K1, hK1⟩ : ∃ r : ℝ, r = 20 + 4 * k := ⟨_, rfl⟩
  have hK1pos : 0 < K1 := by rw [hK1]; positivity
  obtain ⟨K2, hK2⟩ : ∃ r : ℝ, r = (1 + m) * K1 / (2 * m) := ⟨_, rfl⟩
  have hK2pos : 0 < K2 := by
    rw [hK2]; exact div_pos (mul_pos (by linarith) hK1pos) (by linarith)
  have hsm1 : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.2 (by linarith)
  have hsm1ne : Real.sqrt (m + 1) ≠ 0 := hsm1.ne'
  obtain ⟨ε, hε⟩ : ∃ r : ℝ, r = ρ' / (2 * Real.sqrt (m + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hρ'0 (by linarith)
  obtain ⟨N₀, hN⟩ := hA ![u0 / sm, 0, u2 / sm] hunit (by simp) ε hε0
  have t1 : (0 : ℝ) ≤ (K1 + 1) / m := div_nonneg (by linarith) hmpos.le
  have t2 : (0 : ℝ) ≤ (2 * k + 2 * K2) / ρ' := div_nonneg (by linarith) hρ'0.le
  have t3 : (0 : ℝ) ≤ 2 / ρ' := div_nonneg (by norm_num) hρ'0.le
  have t4 : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
  have t5 : (0 : ℝ) ≤ 16 * k + 4 * k ^ 2 := by positivity
  obtain ⟨B, hB⟩ : ∃ r : ℝ, r = K1 + (K1 + 1) / m + N₀ + (2 * k + 2 * K2) / ρ' + 2 / ρ' +
      (16 * k + 4 * k ^ 2) + 1 := ⟨_, rfl⟩
  refine ⟨⌈B⌉₊, fun v hv hadm => ?_⟩
  have hvB : B ≤ v := Nat.ceil_le.1 hv
  have hv1 : (1 : ℝ) ≤ v := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hvK1 : K1 ≤ v := by linarith
  have hvm : (K1 + 1) / m ≤ v := by linarith
  have hvN₀ : (N₀ : ℝ) ≤ v := by linarith
  have hvρ1 : (2 * k + 2 * K2) / ρ' ≤ v := by linarith
  have hvρ2 : 2 / ρ' ≤ v := by linarith
  have hvbig : 16 * (k : ℝ) + 4 * k ^ 2 ≤ v := by linarith
  have hmv : K1 + 1 ≤ m * v := by have := (div_le_iff₀ hmpos).1 hvm; linarith
  have hρv1 : 2 * k + 2 * K2 ≤ ρ' * v := by have := (div_le_iff₀ hρ'0).1 hvρ1; linarith
  have hρv2 : 2 ≤ ρ' * v := by have := (div_le_iff₀ hρ'0).1 hvρ2; linarith
  have hρv : ρ' * v ≤ ρ * v := mul_le_mul_of_nonneg_right hρ'ρ hv0.le
  -- fixed (even) classes
  obtain ⟨cf, hcf⟩ : ∃ cf : Fin k → ℕ, ∀ X, cf X = 2 * ⌊p X * v / 2⌋₊ := ⟨_, fun _ => rfl⟩
  have hcf_le : ∀ X, (cf X : ℝ) ≤ p X * v := fun X => by
    have := Nat.floor_le (div_nonneg (mul_nonneg (hp X).le (Nat.cast_nonneg v)) zero_le_two)
    rw [hcf]; push_cast; linarith
  have hcf_ge : ∀ X, p X * v - 2 < (cf X : ℝ) := fun X => by
    have := Nat.lt_floor_add_one (p X * v / 2)
    rw [hcf]; push_cast; linarith
  have hdev : ∀ X, -2 < (cf X : ℝ) - p X * v ∧ (cf X : ℝ) - p X * v ≤ 0 := fun X =>
    ⟨by linarith [hcf_ge X], by linarith [hcf_le X]⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ, F = ∑ X ∈ Fx, cf X := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ X ∈ Fx, ((cf X : ℝ) - p X * v) := ⟨_, rfl⟩
  have hFR : (F : ℝ) = PF * v + E := by
    rw [hF, hPF, hE]; push_cast
    rw [sum_mul, ← sum_add_distrib]; exact sum_congr rfl fun X _ => by ring
  have hcardFx : (Fx.card : ℝ) ≤ k := by
    have := card_le_univ Fx; rw [Fintype.card_fin] at this; exact_mod_cast this
  have hE_lo : -(2 * (k : ℝ)) ≤ E := by
    have : ∑ X ∈ Fx, (-2 : ℝ) ≤ E := by rw [hE]; exact sum_le_sum fun X _ => (hdev X).1.le
    rw [sum_const, nsmul_eq_mul] at this; linarith
  have hE_hi : E ≤ 0 := by rw [hE]; exact sum_nonpos fun X _ => (hdev X).2
  have hFv : F ≤ v := by
    have h' := mul_le_mul_of_nonneg_right hPF1 hv0.le
    have : (F : ℝ) ≤ v := by rw [hFR]; linarith
    exact_mod_cast this
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = v - F := ⟨_, rfl⟩
  have hwR : (w : ℝ) = v - F := by rw [hw, Nat.cast_sub hFv]
  have hWv : (w : ℝ) = (q0 + q1 + q2 + q3) * v - E := by
    have e : q0 + q1 + q2 + q3 = 1 - PF := by linarith
    rw [hwR, hFR, e]; ring
  -- residues
  obtain ⟨hvodd, T, hT3, hT4⟩ := T_facts hadm
  have hFeven : F % 2 = 0 := by
    have : F = 2 * ∑ X ∈ Fx, ⌊p X * v / 2⌋₊ := by
      rw [hF, mul_sum]; exact sum_congr rfl fun X _ => hcf X
    rw [this]; exact Nat.mul_mod_right 2 _
  have hwodd : w % 2 = 1 := by rw [hw]; exact wodd_aux hvodd hFeven hFv
  obtain ⟨SQ, hSQ⟩ : ∃ S : ℕ, S = ∑ X ∈ Fx, cf X ^ 2 := ⟨_, rfl⟩
  have hSQ4 : SQ % 4 = 0 := by
    have : SQ = 4 * ∑ X ∈ Fx, ⌊p X * v / 2⌋₊ ^ 2 := by
      rw [hSQ, mul_sum]; exact sum_congr rfl fun X _ => by rw [hcf]; ring
    rw [this]; exact Nat.mul_mod_right 4 _
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = 4 * ((T : ℤ) - SQ) - (w : ℤ) ^ 2 := ⟨_, rfl⟩
  have hM8 : M % 8 = 3 := by
    rw [hM]
    exact M_mod8 _ _ _ (by exact_mod_cast hT4) (by exact_mod_cast hSQ4)
      (by exact_mod_cast hwodd)
  have hTR : (T : ℝ) = ((v : ℝ) ^ 2 + 2 * v) / 3 := by
    have : ((3 * T : ℕ) : ℝ) = ((v * (v + 2) : ℕ) : ℝ) := by rw [hT3]
    push_cast at this; linarith
  have hMR : (M : ℝ) = 4 * (((v : ℝ) ^ 2 + 2 * v) / 3 - SQ) - (w : ℝ) ^ 2 := by
    rw [hM]; push_cast; linarith
  -- second-order terms
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ X ∈ Fx, p X * ((cf X : ℝ) - p X * v) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ∑ X ∈ Fx, ((cf X : ℝ) - p X * v) ^ 2 := ⟨_, rfl⟩
  have hSQR : (SQ : ℝ) = QF * (v : ℝ) ^ 2 + 2 * v * G + H := by
    rw [hSQ, hQF, hG, hH]; push_cast
    rw [sum_mul, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun X _ => by ring
  have hG_lo : -2 ≤ G := by
    have : ∑ X ∈ Fx, p X * (-2) ≤ G := by
      rw [hG]; exact sum_le_sum fun X _ => (mul_dev (hp X).le (hdev X).1 (hdev X).2).1
    rw [← sum_mul, ← hPF] at this; linarith
  have hG_hi : G ≤ 0 := by
    rw [hG]; exact sum_nonpos fun X _ => (mul_dev (hp X).le (hdev X).1 (hdev X).2).2.1
  have hH_lo : 0 ≤ H := by rw [hH]; exact sum_nonneg fun X _ => sq_nonneg _
  have hH_hi : H ≤ 4 * k := by
    have : H ≤ ∑ X ∈ Fx, (4 : ℝ) := by
      rw [hH]; exact sum_le_sum fun X _ => (mul_dev (hp X).le (hdev X).1 (hdev X).2).2.2
    rw [sum_const, nsmul_eq_mul] at this; linarith
  have hMm : |(M : ℝ) - m * (v : ℝ) ^ 2| ≤ K1 * v := by
    rw [hK1]
    exact M_estimate hkR hv0.le hW hSq hmW hWv hSQR hMR hE_lo hE_hi hG_lo hG_hi hH_lo hH_hi
      (by linarith) (by linarith) hvbig
  obtain ⟨hMlow, hMhi⟩ := M_bounds hv0.le hMm hmv hvK1
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := by linarith
    exact_mod_cast this
  -- the representation
  obtain ⟨N, hNM⟩ : ∃ N : ℕ, (N : ℤ) = M := ⟨M.toNat, Int.toNat_of_nonneg hMpos.le⟩
  have hNR : (N : ℝ) = (M : ℝ) := by rw [← hNM]; norm_cast
  have hN8z : (N : ℤ) % 8 = 3 := by rw [hNM]; exact hM8
  have hN8 : N % 8 = 3 := by exact_mod_cast hN8z
  have hNN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) ≤ N := by rw [hNR]; linarith
    exact_mod_cast this
  obtain ⟨x, hx, hxu⟩ := hN N hNN₀ hN8
  rw [Fin.sum_univ_three] at hx
  obtain ⟨ha, hb, hc⟩ := odd3 hx hN8z
  obtain ⟨b', hb'abs, hb'odd, hb'4⟩ :=
    sign_choice (x 0) (x 1) (x 2) w ha hb hc (by exact_mod_cast hwodd)
  obtain ⟨c0, c1, c2, c3, e0, e1, e2, e3⟩ := four_split (x 0) b' (x 2) w ha hb'odd hc hb'4
  obtain ⟨hsum4, hsq4⟩ := four_sums e0 e1 e2 e3
  have hb'sq : b' ^ 2 = x 1 ^ 2 := by rw [← sq_abs, hb'abs, sq_abs]
  -- closeness of the four classes
  have hsN : Real.sqrt N ≤ Real.sqrt (m + 1) * v := by
    calc Real.sqrt N ≤ Real.sqrt ((m + 1) * (v : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [hNR]; exact hMhi)
      _ = Real.sqrt (m + 1) * v := by rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hv0.le]
  have hratio := sqrt_ratio_close hmpos hv0 (Nat.cast_nonneg N)
    (show |(N : ℝ) - m * (v : ℝ) ^ 2| ≤ K1 * v by rw [hNR]; exact hMm)
  rw [← hsm] at hratio
  have hu0b : |u0| ≤ (1 + m) / 2 := by
    have := abs_half u0 u2; rwa [← hm] at this
  have hu2b : |u2| ≤ (1 + m) / 2 := by
    have := abs_half u2 u0; rwa [add_comm (u2 ^ 2), ← hm] at this
  have hεN : ε * Real.sqrt N ≤ ρ' / 2 * v := by
    calc ε * Real.sqrt N ≤ ε * (Real.sqrt (m + 1) * v) :=
          mul_le_mul_of_nonneg_left hsN hε0.le
      _ = ρ' / 2 * v := by rw [hε]; field_simp
  have hx0 : |(x 0 : ℝ) - Real.sqrt N * (u0 / sm)| ≤ ε * Real.sqrt N := hxu 0
  have hx1 : |(x 1 : ℝ) - Real.sqrt N * 0| ≤ ε * Real.sqrt N := hxu 1
  have hx2 : |(x 2 : ℝ) - Real.sqrt N * (u2 / sm)| ≤ ε * Real.sqrt N := hxu 2
  rw [mul_zero, sub_zero] at hx1
  have d0 := dev_bound hsm0 hmpos hx0 hu0b hratio hK1pos.le
  have d2 := dev_bound hsm0 hmpos hx2 hu2b hratio hK1pos.le
  rw [← hK2] at d0 d2
  have d1 : |(b' : ℝ)| ≤ ε * Real.sqrt N + K2 := by
    have : |(b' : ℝ)| = |(x 1 : ℝ)| := by exact_mod_cast hb'abs
    rw [this]; linarith
  have hEabs : |E| ≤ 2 * k := abs_le.2 ⟨by linarith, by linarith⟩
  obtain ⟨cl0, cl1, cl2, cl3⟩ := four_close (c0 := (c0 : ℝ)) (c1 := (c1 : ℝ))
    (c2 := (c2 : ℝ)) (c3 := (c3 : ℝ)) (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
    (w := (w : ℝ)) (W := q0 + q1 + q2 + q3) (v := (v : ℝ)) (E := E) (y0 := (x 0 : ℝ))
    (y1 := (b' : ℝ)) (y2 := (x 2 : ℝ)) (u0 := u0) (u2 := u2) (D := ε * Real.sqrt N + K2)
    (k := k) (by exact_mod_cast e0) (by exact_mod_cast e1) (by exact_mod_cast e2)
    (by exact_mod_cast e3) rfl hq1' hu0 hu2 hWv hEabs d0 d1 d2
  have hbound : (2 * (k : ℝ) + 3 * (ε * Real.sqrt N + K2)) / 4 ≤ ρ' * v := by linarith
  have hc0 : (0 : ℤ) ≤ c0 := by
    have := nonneg_of_close hv0.le hpm0.le hq0m hρ'pm (cl0.trans hbound); exact_mod_cast this
  have hc1 : (0 : ℤ) ≤ c1 := by
    have := nonneg_of_close hv0.le hpm0.le hq1m hρ'pm (cl1.trans hbound); exact_mod_cast this
  have hc2 : (0 : ℤ) ≤ c2 := by
    have := nonneg_of_close hv0.le hpm0.le hq2m hρ'pm (cl2.trans hbound); exact_mod_cast this
  have hc3 : (0 : ℤ) ≤ c3 := by
    have := nonneg_of_close hv0.le hpm0.le hq3m hρ'pm (cl3.trans hbound); exact_mod_cast this
  obtain ⟨n0, hn0⟩ : ∃ n : ℕ, (n : ℤ) = c0 := ⟨c0.toNat, Int.toNat_of_nonneg hc0⟩
  obtain ⟨n1, hn1⟩ : ∃ n : ℕ, (n : ℤ) = c1 := ⟨c1.toNat, Int.toNat_of_nonneg hc1⟩
  obtain ⟨n2, hn2⟩ : ∃ n : ℕ, (n : ℤ) = c2 := ⟨c2.toNat, Int.toNat_of_nonneg hc2⟩
  obtain ⟨n3, hn3⟩ : ∃ n : ℕ, (n : ℤ) = c3 := ⟨c3.toNat, Int.toNat_of_nonneg hc3⟩
  have fin : ∀ (c : ℤ) (n : ℕ) (q : ℝ), (n : ℤ) = c → |(c : ℝ) - q * v| ≤ ρ' * v →
      |(n : ℝ) - q * v| ≤ ρ * v := by
    intro c n q hn hcl
    have : (n : ℝ) = (c : ℝ) := by rw [← hn]; norm_cast
    rw [this]; exact hcl.trans hρv
  have cc0 := fin c0 n0 q0 hn0 (cl0.trans hbound)
  have cc1 := fin c1 n1 q1 hn1 (cl1.trans hbound)
  have cc2 := fin c2 n2 q2 hn2 (cl2.trans hbound)
  have cc3 := fin c3 n3 q3 hn3 (cl3.trans hbound)
  have hsum4' : n0 + n1 + n2 + n3 = w := by
    have : ((n0 + n1 + n2 + n3 : ℕ) : ℤ) = (w : ℤ) := by
      push_cast; rw [hn0, hn1, hn2, hn3]; exact hsum4
    exact_mod_cast this
  have hN' : x 0 ^ 2 + b' ^ 2 + x 2 ^ 2 = M := by rw [hb'sq, hx, hNM]
  have hsq4' : n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2 + SQ = T := by
    have : ((n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2 + SQ : ℕ) : ℤ) = (T : ℤ) := by
      push_cast; rw [hn0, hn1, hn2, hn3]
      have h4 := hsq4; rw [hN', hM] at h4; linarith
    exact_mod_cast this
  -- the split
  obtain ⟨cN, hcN⟩ : ∃ cN : Fin k → ℕ,
      ∀ X, cN X = if X.val < 4 then sel4 n0 n1 n2 n3 X.val else cf X := ⟨_, fun _ => rfl⟩
  have evlt : ∀ X : Fin k, X.val < 4 → cN X = sel4 n0 n1 n2 n3 X.val := fun X h => by
    rw [hcN, if_pos h]
  have evge : ∀ X : Fin k, 4 ≤ X.val → cN X = cf X := fun X h => by
    rw [hcN, if_neg (by omega)]
  have ev0 : cN ⟨0, by omega⟩ = n0 := evlt _ (show (0 : ℕ) < 4 by norm_num)
  have ev1 : cN ⟨1, by omega⟩ = n1 := evlt _ (show (1 : ℕ) < 4 by norm_num)
  have ev2 : cN ⟨2, by omega⟩ = n2 := evlt _ (show (2 : ℕ) < 4 by norm_num)
  have ev3 : cN ⟨3, by omega⟩ = n3 := evlt _ (show (3 : ℕ) < 4 by norm_num)
  have hsplitN := sum_split4 hk4 cN
  have hsplitN2 := sum_split4 hk4 (fun X => cN X ^ 2)
  beta_reduce at hsplitN2
  rw [← hFx] at hsplitN hsplitN2
  have hFxN : ∑ X ∈ Fx, cN X = F := by
    rw [hF]; exact sum_congr rfl fun X hX => evge X (hmemFx X hX)
  have hFxN2 : ∑ X ∈ Fx, cN X ^ 2 = SQ := by
    rw [hSQ]; exact sum_congr rfl fun X hX => by rw [evge X (hmemFx X hX)]
  have hsumN : ∑ X, cN X = v := by
    rw [hsplitN, ev0, ev1, ev2, ev3, hFxN, hsum4', hw]; exact Nat.sub_add_cancel hFv
  have hsqN : ∑ X, cN X ^ 2 = T := by
    rw [hsplitN2, ev0, ev1, ev2, ev3, hFxN2]; exact hsq4'
  refine ⟨cN, hsumN, ?_, ?_, ?_⟩
  · -- divisibility
    have hcc : ∑ X, cN X * (cN X - 1) + v = T := by
      rw [← hsumN, ← hsqN, ← sum_add_distrib]
      exact sum_congr rfl fun X _ => by rw [nat_cc, sq]
    exact div_aux (by exact_mod_cast hv1) hcc hT3
  · -- parity
    have hsq4mod : (n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2) % 4 = 1 := by
      have : (n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2 + SQ) % 4 = 1 := by rw [hsq4']; exact hT4
      generalize n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2 = A at this ⊢
      omega
    have hpar := parity_sel4 n0 n1 n2 n3 hsq4mod
    intro X Y hXY
    by_cases hX4 : 4 ≤ X.val
    · rw [evge X hX4, hcf]; exact (even_two_mul _).mul_right _
    by_cases hY4 : 4 ≤ Y.val
    · rw [evge Y hY4, hcf]; exact (even_two_mul _).mul_left _
    rw [evlt X (not_le.1 hX4), evlt Y (not_le.1 hY4)]
    exact hpar _ _ (not_le.1 hX4) (not_le.1 hY4) (fun h => hXY (Fin.ext h))
  · -- closeness
    intro X
    by_cases hX4 : 4 ≤ X.val
    · rw [evge X hX4, abs_le]
      obtain ⟨a, b⟩ := hdev X
      constructor <;> linarith
    · obtain ⟨a, ha'⟩ := X
      have hal : a < 4 := not_le.1 hX4
      rw [evlt _ hal]
      interval_cases a
      · rw [← hq0]; exact cc0
      · rw [← hq1]; exact cc1
      · rw [← hq2]; exact cc2
      · rw [← hq3]; exact cc3

theorem two_cap_of_meridian (hA : MeridianThreeSquaresDense) :
    ∃ N₀ : ℕ,TwoCapAt N₀ := by
  obtain ⟨N₀,hN⟩ := hA ![1,0,0] (by simp [Fin.sum_univ_three]) (by simp) (1/3) (by norm_num)
  refine ⟨N₀,fun N hlarge hmod => ?_⟩
  obtain ⟨x,hx,hxu⟩ := hN N hlarge hmod
  have h0 := hxu 0
  have h1 := hxu 1
  have h2 := hxu 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons,mul_one,mul_zero,sub_zero] at h0 h1 h2
  have hs := Real.sqrt_nonneg (N : ℝ)
  have h0a := (abs_le.mp h0).1
  refine ⟨x 0,x 1,x 2,?_,?_,?_⟩
  · simpa only [Fin.sum_univ_three] using hx
  · have hh : (2 : ℝ)*|((x 1 : ℤ) : ℝ)|≤((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (2 : ℝ)*|((x 2 : ℤ) : ℝ)|≤((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hh

theorem bicolourable_eventually_of_meridian (hA : MeridianThreeSquaresDense)
    {k : ℕ} (hk : 4≤k) :
    ∃ v₀ : ℕ,∀ v,v₀≤v → Admissible v → Bicolourable v k := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk5
  · exact conj35_large_of_two_radius_caps (two_cap_of_meridian hA)
  have hk5' : 5≤k := hk5
  obtain ⟨p,hp,h1,h2,hsym,hne,hcrit⟩ := geometric_profile k hk5'
  obtain ⟨ρ,hρ,v₁,hnear⟩ := near_profile_bicolourable galeInt_verified (by omega) p hp h1 h2 hcrit
  obtain ⟨V₀,hsplit⟩ := split_near_meridian hA hk5' p hp h1 h2 hsym hne hρ
  refine ⟨max v₁ V₀,fun v hv hadm => ?_⟩
  obtain ⟨c,hsum,hdiv,hpar,hclose⟩ := hsplit v (le_of_max_le_right hv) hadm
  have hodd : Odd v := Nat.odd_iff.mpr (by rcases hadm with h | h <;> omega)
  exact hnear v (le_of_max_le_left hv) hodd c hsum hdiv hpar hclose

theorem conj36_large_of_meridian (hA : MeridianThreeSquaresDense) :
    ∃ v₀ : ℕ,∀ v,v₀≤v → Admissible v → Bicolourable v 5 :=
  bicolourable_eventually_of_meridian hA (by norm_num)

end CDRBicolour.PaperIII
