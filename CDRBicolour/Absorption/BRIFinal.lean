/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.BRIAssembly

/-!
# The bounded right inverse

With every class of size at least `m ≥ 512` and `n ≤ 4m`:

* `abs_xU_le`: the uniform solver is bounded, `|x| ≤ 43 B / (m-1)` for type values `|G| ≤ B`;
* `abs_Phi0_le`: `|Φ₀ d T| ≤ 26000 ‖d‖ / n` on `ker ℓ`;
* `bri_of_balanced`: `M Φ₀` restricted to `ker ℓ` is a contraction perturbation of the identity,
  hence invertible there with inverse of norm `≤ 2`; `Φ = Φ₀ ∘ (M Φ₀|_{ker ℓ})⁻¹ ∘ proj` is a
  bounded right inverse with `K = 52000` (`BRI`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

theorem abs_div_le_of {p q r M : ℝ} (hp : |p| ≤ r) (hq : M ≤ q) (hM : 0 < M) :
    |p / q| ≤ r / M := by
  have hq0 : 0 < q := lt_of_lt_of_le hM hq
  rw [abs_div, abs_of_pos hq0]
  have hr : 0 ≤ r := (abs_nonneg _).trans hp
  calc |p| / q ≤ r / q := div_le_div_of_nonneg_right hp hq0.le
    _ ≤ r / M := div_le_div_of_nonneg_left hr hM hq

/-- **The chain weights are bounded.** -/
theorem chain_bounds {a b c M B : ℝ} (G : Fin 3 → Fin 3 → ℝ) (hM : 2 ≤ M)
    (ha : M + 1 ≤ a) (hb : M + 1 ≤ b) (hc : M + 1 ≤ c) (ha' : a ≤ 6 * M)
    (hG : ∀ X Y, |G X Y| ≤ B) :
    |xAAB b G| ≤ B / M ∧ |xACC c G| ≤ B / M ∧ |xABB a b G| ≤ 7 * B / M ∧
      |xBCC a b c G| ≤ 7 * B / M ∧ |xBBC a b c G| ≤ 43 * B / M := by
  have hM0 : 0 < M := by linarith
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0 0)
  have e1 : |xAAB b G| ≤ B / M := abs_div_le_of (hG 0 0) (by linarith) hM0
  have e2 : |xACC c G| ≤ B / M := abs_div_le_of (hG 0 2) (by linarith) hM0
  have hprod : ∀ {x y : ℝ}, 0 ≤ x → x ≤ 6 * M → |y| ≤ B / M → |x * y| ≤ 6 * B := by
    intro x y hx hxM hy
    rw [abs_mul, abs_of_nonneg hx]
    calc x * |y| ≤ 6 * M * (B / M) := mul_le_mul hxM hy (abs_nonneg _) (by positivity)
      _ = 6 * B := by field_simp
  have e3 : |xABB a b G| ≤ 7 * B / M := by
    apply abs_div_le_of _ (by linarith) hM0
    calc |G 0 1 - (a - 1) * xAAB b G| ≤ |G 0 1| + |(a - 1) * xAAB b G| := abs_sub _ _
      _ ≤ B + 6 * B := add_le_add (hG 0 1) (hprod (by linarith) (by linarith) e1)
      _ = 7 * B := by ring
  have e4 : |xBCC a b c G| ≤ 7 * B / M := by
    apply abs_div_le_of _ (by linarith) hM0
    calc |G 2 2 - a * xACC c G| ≤ |G 2 2| + |a * xACC c G| := abs_sub _ _
      _ ≤ B + 6 * B := add_le_add (hG 2 2) (hprod (by linarith) ha' e2)
      _ = 7 * B := by ring
  have e5 : |xBBC a b c G| ≤ 43 * B / M := by
    apply abs_div_le_of _ (by linarith) hM0
    have : |a * xABB a b G| ≤ 42 * B := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      calc a * |xABB a b G| ≤ 6 * M * (7 * B / M) := mul_le_mul ha' e3 (abs_nonneg _) (by positivity)
        _ = 42 * B := by field_simp; ring
    calc |G 1 1 - a * xABB a b G| ≤ |G 1 1| + |a * xABB a b G| := abs_sub _ _
      _ ≤ B + 42 * B := add_le_add (hG 1 1) this
      _ = 43 * B := by ring
  exact ⟨e1, e2, e3, e4, e5⟩

section Final

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

theorem abs_xU_le {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m)
    (hbal : Fintype.card V ≤ 4 * m) {B : ℝ} (G : Fin 3 → Fin 3 → ℝ)
    (hG : ∀ X Y, |G X Y| ≤ B) (mm : Multiset (Fin 3)) :
    |xU lab G mm| ≤ 43 * B / ((m : ℝ) - 1) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0 0)
  have hx : ∀ k, (m : ℝ) ≤ csz lab k := fun k => by exact_mod_cast hm k
  have hcV : ∀ k, (csz lab k : ℝ) ≤ Fintype.card V := fun k => by
    have : csz lab k ≤ Fintype.card V := by unfold csz; exact (card_filter_le _ _).trans_eq card_univ
    exact_mod_cast this
  have hn : (Fintype.card V : ℝ) ≤ 4 * m := by exact_mod_cast hbal
  have hM : (2 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have ha' : (csz lab 0 : ℝ) ≤ 6 * ((m : ℝ) - 1) := by linarith [hcV 0]
  obtain ⟨e1, e2, e3, e4, e5⟩ := chain_bounds (a := (csz lab 0 : ℝ)) (b := (csz lab 1 : ℝ))
    (c := (csz lab 2 : ℝ)) G hM (by linarith [hx 0]) (by linarith [hx 1]) (by linarith [hx 2]) ha' hG
  have hM0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have l1 : B / ((m : ℝ) - 1) ≤ 43 * B / ((m : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by linarith) hM0.le
  have l7 : 7 * B / ((m : ℝ) - 1) ≤ 43 * B / ((m : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by linarith) hM0.le
  have l0 : (0 : ℝ) ≤ 43 * B / ((m : ℝ) - 1) := by positivity
  unfold xU
  split_ifs
  · exact e1.trans l1
  · simp [xAAC]; exact l0
  · exact e5
  · exact e3.trans l7
  · exact e2.trans l1
  · exact e4.trans l7
  · simp; exact l0

/-- The type values of `Φ₀` are bounded on `ker ℓ`. -/
theorem abs_Gc_le {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h512 : 512 ≤ m)
    (hbal : Fintype.card V ≤ 4 * m) (d : E0 V → ℝ) (hd : ell lab d = 0) (X Y : Fin 3) :
    |Gc lab d X Y| ≤ 65 * ‖d‖ := by
  have h3 : 3 ≤ m := by omega
  have hcls : ∀ k, 3 ≤ csz lab k := fun k => (hm k).trans' h3
  have hmR : (512 : ℝ) ≤ m := by exact_mod_cast h512
  have hnR : (Fintype.card V : ℝ) ≤ 4 * m := by exact_mod_cast hbal
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  set n : ℝ := (Fintype.card V : ℝ)
  set P : ℝ := ((m : ℝ) - 1) * ((m : ℝ) - 1)
  have hP : (m : ℝ) ^ 2 / 2 ≤ P := by simp only [P]; nlinarith
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hPe : ∀ e : E0 V, P ≤ #(pairsF lab (rep e).1 (rep e).2) := by
    intro e
    have := card_pairsF_ge hm (rep e).1 (rep e).2
    have h1 : 1 ≤ m := by omega
    have : ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) ≤ #(pairsF lab (rep e).1 (rep e).2) := by
      exact_mod_cast this
    rwa [Nat.cast_sub h1, Nat.cast_one] at this
  have hut : ∀ e : E0 V, |ut lab e X Y| ≤ 2 / P := by
    intro e
    unfold ut
    have hc : (0 : ℝ) < #(pairsF lab (rep e).1 (rep e).2) := lt_of_lt_of_le hPpos (hPe e)
    rw [abs_mul, abs_of_pos (by positivity)]
    have h2 : |(if matchQ lab (rep e).1 (rep e).2 X Y then (1 : ℝ) else 0) +
        (if matchQ lab (rep e).1 (rep e).2 Y X then 1 else 0)| ≤ 2 := by
      split_ifs <;> norm_num
    calc 1 / (#(pairsF lab (rep e).1 (rep e).2) : ℝ) * |_| ≤ 1 / P * 2 :=
          mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hPpos (hPe e)) h2 (abs_nonneg _)
            (by positivity)
      _ = 2 / P := by ring
  have hGfun : |Gfun lab d X Y| ≤ 64 * ‖d‖ := by
    unfold Gfun
    calc |∑ e, d e * ut lab e X Y| ≤ ∑ e, |d e * ut lab e X Y| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e : E0 V, ‖d‖ * (2 / P) := sum_le_sum fun e _ => by
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d e) (hut e)
            (abs_nonneg _) (norm_nonneg _)
      _ = Fintype.card (E0 V) * (‖d‖ * (2 / P)) := by rw [sum_const, nsmul_eq_mul, card_univ]
      _ ≤ n ^ 2 * (‖d‖ * (2 / P)) := mul_le_mul_of_nonneg_right card_E0_le (by positivity)
      _ ≤ 64 * ‖d‖ := by
          rw [show n ^ 2 * (‖d‖ * (2 / P)) = ‖d‖ * (2 * n ^ 2 / P) by ring]
          have : 2 * n ^ 2 / P ≤ 64 := by
            rw [div_le_iff₀ hPpos]; nlinarith
          nlinarith [norm_nonneg d]
  have hlam := abs_lam_le hcls hm h3 d hd
  have c2 : n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity), show n ^ 2 * (2 * n / P) = 2 * n ^ 3 / P by ring,
      div_le_iff₀ hPpos]
    have hn3 : n ^ 3 ≤ 64 * (m : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hn0 hnR 3; nlinarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
    have h4 : (512 : ℝ) * (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := by
      have := mul_le_mul_of_nonneg_left hmR hm0; nlinarith
    have hPm : 1 * (3 * (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 / 2) ≤ 1 * (3 * (m : ℝ) ^ 2) * P :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  have hl : |lam lab d| ≤ ‖d‖ := by
    calc |lam lab d| ≤ ‖d‖ * n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) := hlam
      _ = ‖d‖ * (n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2)) := by ring
      _ ≤ ‖d‖ * 1 := mul_le_mul_of_nonneg_left c2 (norm_nonneg _)
      _ = ‖d‖ := mul_one _
  have hfix : |Gfix X Y| ≤ 1 := by unfold Gfix; split_ifs <;> norm_num
  unfold Gc
  calc |Gfun lab d X Y - lam lab d * Gfix X Y| ≤ |Gfun lab d X Y| + |lam lab d * Gfix X Y| :=
        abs_sub _ _
    _ ≤ 64 * ‖d‖ + ‖d‖ * 1 := add_le_add hGfun (by
        rw [abs_mul]; exact mul_le_mul hl hfix (abs_nonneg _) (norm_nonneg _))
    _ = 65 * ‖d‖ := by ring

/-- **`Φ₀` is bounded on `ker ℓ`.** -/
theorem abs_Phi0_le {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h512 : 512 ≤ m)
    (hbal : Fintype.card V ≤ 4 * m) (d : E0 V → ℝ) (hd : ell lab d = 0) (T : Finset V) :
    |Phi0 lab d T| ≤ 26000 / Fintype.card V * ‖d‖ := by
  have h3 : 3 ≤ m := by omega
  have hmR : (512 : ℝ) ≤ m := by exact_mod_cast h512
  have hnR : (Fintype.card V : ℝ) ≤ 4 * m := by exact_mod_cast hbal
  have hx : (m : ℝ) ≤ csz lab 0 := by exact_mod_cast hm 0
  have hcV : (csz lab 0 : ℝ) ≤ Fintype.card V := by
    have : csz lab 0 ≤ Fintype.card V := by unfold csz; exact (card_filter_le _ _).trans_eq card_univ
    exact_mod_cast this
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  set n : ℝ := (Fintype.card V : ℝ)
  have h1 := abs_Phi1_le hm h3 d T
  have h2 := abs_xU_le hm h3 hbal (Gc lab d) (abs_Gc_le hm h512 hbal d hd) (T.val.map lab)
  have hsplit : Phi0 lab d T = Phi1 lab d T + xU lab (Gc lab d) (T.val.map lab) := rfl
  rw [hsplit]
  have hM : (m : ℝ) - 1 ≥ n / 8 := by linarith
  have hM0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have a1 : 54 * n * ‖d‖ / (((m : ℝ) - 1) * ((m : ℝ) - 1)) ≤ 3456 / n * ‖d‖ := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : n ^ 2 / 64 ≤ ((m : ℝ) - 1) * ((m : ℝ) - 1) := by nlinarith
    have : 3456 / n * ‖d‖ * (((m : ℝ) - 1) * ((m : ℝ) - 1)) ≥ 3456 / n * ‖d‖ * (n ^ 2 / 64) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e : 3456 / n * ‖d‖ * (n ^ 2 / 64) = 54 * n * ‖d‖ := by field_simp; ring
    linarith
  have a2 : 43 * (65 * ‖d‖) / ((m : ℝ) - 1) ≤ 22360 / n * ‖d‖ := by
    rw [div_le_iff₀ hM0]
    have : 22360 / n * ‖d‖ * ((m : ℝ) - 1) ≥ 22360 / n * ‖d‖ * (n / 8) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have e : 22360 / n * ‖d‖ * (n / 8) = 43 * (65 * ‖d‖) := by field_simp; ring
    linarith
  calc |Phi1 lab d T + xU lab (Gc lab d) (T.val.map lab)|
      ≤ |Phi1 lab d T| + |xU lab (Gc lab d) (T.val.map lab)| := abs_add_le _ _
    _ ≤ 3456 / n * ‖d‖ + 22360 / n * ‖d‖ := add_le_add (h1.trans a1) (h2.trans a2)
    _ ≤ 26000 / n * ‖d‖ := by
        have : 0 ≤ 1 / n * ‖d‖ := by positivity
        have e : 3456 / n * ‖d‖ + 22360 / n * ‖d‖ = 25816 * (1 / n * ‖d‖) := by ring
        have e' : 26000 / n * ‖d‖ = 26000 * (1 / n * ‖d‖) := by ring
        rw [e, e']; nlinarith

/-- **The bounded right inverse** (balanced classes of size at least `512`). -/
theorem bri_of_balanced {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h512 : 512 ≤ m)
    (hbal : Fintype.card V ≤ 4 * m) : Nonempty (BRI lab 52000) := by
  have h3 : 3 ≤ m := by omega
  have hcls : ∀ k, 3 ≤ csz lab k := fun k => (hm k).trans' h3
  -- a bichromatic edge
  have hex : ∀ k : Fin 3, ∃ u, lab u = k := by
    intro k
    have := hm k
    unfold csz at this
    obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < #(univ.filter fun v => lab v = k))
    exact ⟨u, (mem_filter.mp hu).2⟩
  obtain ⟨u, hu⟩ := hex 0
  obtain ⟨v, hv⟩ := hex 1
  have huv : u ≠ v := fun h => by rw [h, hv] at hu; exact absurd hu (by decide)
  let e0 : E0 V := ⟨s(u, v), by simpa using huv⟩
  let δ0 : E0 V → ℝ := Pi.single e0 1
  have hδ : ell lab δ0 = 1 := by
    simp only [ell, LinearMap.coe_mk, AddHom.coe_mk, δ0]
    rw [Finset.sum_eq_single e0]
    · simp [e0, wl, hu, hv]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro h; exact absurd (mem_univ e0) h
  let W : Submodule ℝ (E0 V → ℝ) := LinearMap.ker (ell lab)
  let F : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) := Minc lab ∘ₗ Phi0 lab
  have hFW : ∀ x ∈ W, F x ∈ W := fun x _ => LinearMap.mem_ker.mpr (ell_M _)
  have hcontr : ∀ x ∈ W, ‖x‖ ≤ 2 * ‖F x‖ := by
    intro x hx
    have h1 := norm_err_le hcls hm h512 hbal x (LinearMap.mem_ker.mp hx)
    have h2 : ‖x‖ - ‖F x‖ ≤ ‖x - F x‖ := norm_sub_norm_le _ _
    have : ‖x - F x‖ = ‖x - Minc lab (Phi0 lab x)‖ := rfl
    linarith
  let f : W →ₗ[ℝ] W := F.restrict hFW
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : F x = 0 := congrArg Subtype.val hx
    have := hcontr x x.2
    rw [h0, norm_zero, mul_zero] at this
    exact Subtype.ext (norm_le_zero_iff.mp this)
  let eqv : W ≃ₗ[ℝ] W := LinearEquiv.ofBijective f ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let g : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) := LinearMap.id - (ell lab).smulRight δ0
  have hg : ∀ d, g d ∈ W := by
    intro d
    apply LinearMap.mem_ker.mpr
    simp only [g, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
      map_smul, hδ, smul_eq_mul, mul_one, sub_self]
  let proj : (E0 V → ℝ) →ₗ[ℝ] W := LinearMap.codRestrict W g hg
  have hproj : ∀ d, ell lab d = 0 → ((proj d : W) : E0 V → ℝ) = d := by
    intro d hd
    simp [proj, g, hd]
  have hFx : ∀ y : W, F ((eqv.symm y : W) : E0 V → ℝ) = (y : E0 V → ℝ) := by
    intro y
    have := congrArg Subtype.val (eqv.apply_symm_apply y)
    exact this
  refine ⟨⟨Phi0 lab ∘ₗ W.subtype ∘ₗ eqv.symm.toLinearMap ∘ₗ proj, fun d hd => ?_, fun d hd T => ?_⟩⟩
  · show F ((eqv.symm (proj d) : W) : E0 V → ℝ) = d
    rw [hFx, hproj d hd]
  · set x : E0 V → ℝ := ((eqv.symm (proj d) : W) : E0 V → ℝ)
    have hxW : x ∈ W := (eqv.symm (proj d)).2
    have hFd : F x = d := by simp only [x]; rw [hFx, hproj d hd]
    have hxn : ‖x‖ ≤ 2 * ‖d‖ := by rw [← hFd]; exact hcontr x hxW
    have hb := abs_Phi0_le hm h512 hbal x (LinearMap.mem_ker.mp hxW) T
    show |Phi0 lab x T| ≤ 52000 / Fintype.card V * ‖d‖
    calc |Phi0 lab x T| ≤ 26000 / Fintype.card V * ‖x‖ := hb
      _ ≤ 26000 / Fintype.card V * (2 * ‖d‖) := mul_le_mul_of_nonneg_left hxn (by positivity)
      _ = 52000 / Fintype.card V * ‖d‖ := by ring

end Final

end CDRBicolour.Absorption
