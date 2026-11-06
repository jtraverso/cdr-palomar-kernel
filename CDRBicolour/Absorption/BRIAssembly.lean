/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.BRIBound

/-!
# The approximate inverse `Φ₀`

`Φ₀ d = Φ₁ d + φ_U (G_c d)`, where `G_c d = Gfun d − λ(d) · Gfix` is the type-uniform part of
the averaging (`Gfun d X Y = ∑_e d e · ut e X Y`) corrected along the bichromatic indicator
`Gfix` so that `ℓ(G_c d) = 0`.  Then (`Minc_Phi0`)

  `M Φ₀ d f = d f − ∑_e d e (avgW e f − ut e (type f)) − λ(d) Gfix (type f)`,

i.e. the error of `Φ₀` is the local part of the averaging plus the `ℓ`-correction.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-! ### Linearity of the chain weights and of `ℓ` on type values -/

section ChainLinear

variable (a b c : ℝ)

theorem ellG_lin (G H : Fin 3 → Fin 3 → ℝ) (r : ℝ) :
    ellG a b c (fun X Y => G X Y - r * H X Y) = ellG a b c G - r * ellG a b c H := by
  unfold ellG; ring

end ChainLinear

section Assembly

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

theorem xU_add (G H : Fin 3 → Fin 3 → ℝ) (m : Multiset (Fin 3)) :
    xU lab (G + H) m = xU lab G m + xU lab H m := by
  unfold xU
  simp only [xAAB, xAAC, xBBC, xABB, xACC, xBCC, Pi.add_apply]
  split_ifs <;> ring

theorem xU_smul (r : ℝ) (G : Fin 3 → Fin 3 → ℝ) (m : Multiset (Fin 3)) :
    xU lab (r • G) m = r * xU lab G m := by
  unfold xU
  simp only [xAAB, xAAC, xBBC, xABB, xACC, xBCC, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

variable (lab) in
/-- The type-uniform part of the averaging. -/
def Gfun (d : E0 V → ℝ) : Fin 3 → Fin 3 → ℝ := fun X Y => ∑ e, d e * ut lab e X Y

/-- The bichromatic indicator on types. -/
def Gfix : Fin 3 → Fin 3 → ℝ := fun X Y => if X = Y then 0 else 1

variable (lab) in
/-- `ℓ` of the bichromatic indicator: `ab + ac + bc`. -/
def S0 : ℝ := ellG (csz lab 0) (csz lab 1) (csz lab 2) Gfix

theorem S0_eq : S0 lab = (csz lab 0 : ℝ) * csz lab 1 + csz lab 0 * csz lab 2 + csz lab 1 * csz lab 2 := by
  simp [S0, ellG, Gfix]

variable (lab) in
/-- The `ℓ`-correction coefficient. -/
def lam (d : E0 V → ℝ) : ℝ := ellG (csz lab 0) (csz lab 1) (csz lab 2) (Gfun lab d) / S0 lab

variable (lab) in
/-- The corrected type values. -/
def Gc (d : E0 V → ℝ) : Fin 3 → Fin 3 → ℝ := fun X Y => Gfun lab d X Y - lam lab d * Gfix X Y

theorem ut_symm (e : E0 V) (X Y : Fin 3) : ut lab e X Y = ut lab e Y X := by
  unfold ut; ring

theorem Gc_symm (d : E0 V → ℝ) (X Y : Fin 3) : Gc lab d X Y = Gc lab d Y X := by
  simp only [Gc, Gfun, Gfix, ut_symm (lab := lab) _ X Y, eq_comm (a := X)]

theorem ellG_Gc (hS : S0 lab ≠ 0) (d : E0 V → ℝ) :
    ellG (csz lab 0) (csz lab 1) (csz lab 2) (Gc lab d) = 0 := by
  unfold Gc
  rw [ellG_lin]
  unfold lam
  change _ - _ / S0 lab * S0 lab = 0
  field_simp
  ring

theorem Gfun_add (d d' : E0 V → ℝ) : Gfun lab (d + d') = Gfun lab d + Gfun lab d' := by
  funext X Y; simp [Gfun, add_mul, sum_add_distrib]

theorem Gfun_smul (r : ℝ) (d : E0 V → ℝ) : Gfun lab (r • d) = r • Gfun lab d := by
  funext X Y; simp [Gfun, mul_sum, mul_assoc]

theorem lam_add (d d' : E0 V → ℝ) : lam lab (d + d') = lam lab d + lam lab d' := by
  simp only [lam, Gfun_add]
  rw [← add_div]; congr 1; unfold ellG; simp only [Pi.add_apply]; ring

theorem lam_smul (r : ℝ) (d : E0 V → ℝ) : lam lab (r • d) = r * lam lab d := by
  simp only [lam, Gfun_smul]
  rw [mul_div_assoc']; congr 1; unfold ellG; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem Gc_add (d d' : E0 V → ℝ) : Gc lab (d + d') = Gc lab d + Gc lab d' := by
  funext X Y; simp only [Gc, Gfun_add, lam_add, Pi.add_apply]; ring

theorem Gc_smul (r : ℝ) (d : E0 V → ℝ) : Gc lab (r • d) = r • Gc lab d := by
  funext X Y; simp only [Gc, Gfun_smul, lam_smul, Pi.smul_apply, smul_eq_mul]; ring

variable (lab) in
/-- **The approximate inverse.** -/
def Phi0 : (E0 V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun d := Phi1 lab d + phiU lab (Gc lab d)
  map_add' d d' := by
    funext T
    simp only [map_add, Pi.add_apply, phiU, Gc_add, xU_add]
    ring
  map_smul' r d := by
    funext T
    simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, phiU, Gc_smul, xU_smul,
      RingHom.id_apply]
    ring

/-- **Coverage of the approximate inverse.** -/
theorem Minc_Phi0 (hcls : ∀ k, 3 ≤ csz lab k) (hS : S0 lab ≠ 0) (d : E0 V → ℝ) (f : E0 V) :
    Minc lab (Phi0 lab d) f = d f -
      ∑ e, d e * (avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2)) -
      lam lab d * Gfix (lab (rep f).1) (lab (rep f).2) := by
  have h1 := Minc_Phi1 hcls d f
  have h2 := Minc_uniform hcls (Gc lab d) (Gc_symm d) (ellG_Gc hS d) f
  have : Minc lab (Phi0 lab d) f = Minc lab (Phi1 lab d) f + Minc lab (phiU lab (Gc lab d)) f := by
    show Minc lab (Phi1 lab d + phiU lab (Gc lab d)) f = _
    rw [map_add, Pi.add_apply]
  rw [this, h1, h2]
  simp only [Gc, Gfun, mul_sub, sum_sub_distrib]
  ring

/-! ### The `ℓ`-correction is small -/

theorem card_pairsF_real (hcls : ∀ k, 3 ≤ csz lab k) (u v : V) :
    (#(pairsF lab u v) : ℝ) = if lab u = lab v then
      (csz lab (lab u + 1) : ℝ) * ((csz lab (lab u + 1) : ℝ) - 1)
    else ((csz lab (lab u) : ℝ) - 1) * ((csz lab (lab v) : ℝ) - 1) := by
  unfold pairsF
  split_ifs with hl
  · rw [offDiag_card]
    have h := hcls (lab u + 1)
    unfold csz at h ⊢
    have hle : #(univ.filter fun w => lab w = lab u + 1) ≤
        #(univ.filter fun w => lab w = lab u + 1) * #(univ.filter fun w => lab w = lab u + 1) :=
      Nat.le_mul_self _
    rw [Nat.cast_sub hle, Nat.cast_mul]; ring
  · rw [card_product, card_class_erase, card_class_erase, Nat.cast_mul,
      Nat.cast_sub (by have := hcls (lab u); omega), Nat.cast_sub (by have := hcls (lab v); omega),
      Nat.cast_one]

theorem wl_rep (e : E0 V) :
    wl lab e.1 = if lab (rep e).1 = lab (rep e).2 then -2 else 1 := by
  rw [← rep_spec e]; simp [wl]

theorem ellG_ut (hcls : ∀ k, 3 ≤ csz lab k) (e : E0 V) :
    ellG (csz lab 0) (csz lab 1) (csz lab 2) (ut lab e) =
      if lab (rep e).1 = lab (rep e).2 then -2 else
        (csz lab (lab (rep e).1) : ℝ) * csz lab (lab (rep e).2) /
          (((csz lab (lab (rep e).1) : ℝ) - 1) * ((csz lab (lab (rep e).2) : ℝ) - 1)) := by
  have h0 : (3 : ℝ) ≤ csz lab 0 := by exact_mod_cast hcls 0
  have h1 : (3 : ℝ) ≤ csz lab 1 := by exact_mod_cast hcls 1
  have h2 : (3 : ℝ) ≤ csz lab 2 := by exact_mod_cast hcls 2
  unfold ut
  rw [card_pairsF_real hcls]
  unfold matchQ
  have tri3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have a0 : (csz lab 0 : ℝ) - 1 ≠ 0 := by linarith
  have a1 : (csz lab 1 : ℝ) - 1 ≠ 0 := by linarith
  have a2 : (csz lab 2 : ℝ) - 1 ≠ 0 := by linarith
  have b0 : (csz lab 0 : ℝ) ≠ 0 := by linarith
  have b1 : (csz lab 1 : ℝ) ≠ 0 := by linarith
  have b2 : (csz lab 2 : ℝ) ≠ 0 := by linarith
  rcases tri3 (lab (rep e).1) with hi | hi | hi <;> rcases tri3 (lab (rep e).2) with hj | hj | hj <;>
    simp (config := { decide := true }) [hi, hj, ellG] <;> field_simp <;> ring

theorem ellG_ut_sub_wl (hcls : ∀ k, 3 ≤ csz lab k) {m : ℕ} (hm : ∀ k, m ≤ csz lab k)
    (h3 : 3 ≤ m) (e : E0 V) :
    |ellG (csz lab 0) (csz lab 1) (csz lab 2) (ut lab e) - wl lab e.1| ≤
      2 * Fintype.card V / (((m : ℝ) - 1) * ((m : ℝ) - 1)) := by
  rw [ellG_ut hcls, wl_rep]
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
  split_ifs with hl
  · simp; exact div_nonneg (by positivity) (mul_self_nonneg _)
  · set x : ℝ := (csz lab (lab (rep e).1) : ℝ)
    set y : ℝ := (csz lab (lab (rep e).2) : ℝ)
    have hcV : ∀ k, csz lab k ≤ Fintype.card V := fun k => by
      unfold csz; exact (card_filter_le _ _).trans_eq card_univ
    have hx : (m : ℝ) ≤ x := by simp only [x]; exact_mod_cast hm _
    have hy : (m : ℝ) ≤ y := by simp only [y]; exact_mod_cast hm _
    have hxn : x ≤ Fintype.card V := by simp only [x]; exact_mod_cast hcV _
    have hyn : y ≤ Fintype.card V := by simp only [y]; exact_mod_cast hcV _
    have hpos : 0 < (x - 1) * (y - 1) := by nlinarith
    have hx1 : x - 1 ≠ 0 := by intro h; linarith
    have hy1 : y - 1 ≠ 0 := by intro h; linarith
    have hP : ((m : ℝ) - 1) * ((m : ℝ) - 1) ≤ (x - 1) * (y - 1) := by nlinarith
    have hm1 : 0 < ((m : ℝ) - 1) * ((m : ℝ) - 1) := by nlinarith
    have : x * y / ((x - 1) * (y - 1)) - 1 = (x + y - 1) / ((x - 1) * (y - 1)) := by
      field_simp; ring
    rw [this, abs_of_nonneg (div_nonneg (by linarith) hpos.le)]
    calc (x + y - 1) / ((x - 1) * (y - 1)) ≤ (2 * Fintype.card V) / ((x - 1) * (y - 1)) :=
          div_le_div_of_nonneg_right (by linarith) hpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hm1 hP

theorem ellG_Gfun (d : E0 V → ℝ) :
    ellG (csz lab 0) (csz lab 1) (csz lab 2) (Gfun lab d) =
      ∑ e, d e * ellG (csz lab 0) (csz lab 1) (csz lab 2) (ut lab e) := by
  simp only [ellG, Gfun, mul_sum, ← sum_add_distrib, mul_add, ← sum_neg_distrib]
  refine sum_congr rfl fun e _ => by ring

theorem card_E0_le : (Fintype.card (E0 V) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have : Fintype.card (E0 V) ≤ Fintype.card (V × V) := by
    exact Fintype.card_le_of_injective rep rep_injective
  rw [Fintype.card_prod] at this
  have : ((Fintype.card (E0 V) : ℕ) : ℝ) ≤ ((Fintype.card V * Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast this
  rw [Nat.cast_mul] at this
  nlinarith

/-- **The `ℓ`-correction is small on `ker ℓ`.** -/
theorem abs_lam_le (hcls : ∀ k, 3 ≤ csz lab k) {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m)
    (d : E0 V → ℝ) (hd : ell lab d = 0) :
    |lam lab d| ≤ ‖d‖ * (Fintype.card V : ℝ) ^ 2 *
      (2 * Fintype.card V / (((m : ℝ) - 1) * ((m : ℝ) - 1))) / (3 * (m : ℝ) ^ 2) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
  have hx : ∀ k, (m : ℝ) ≤ csz lab k := fun k => by exact_mod_cast hm k
  have hS : 3 * (m : ℝ) ^ 2 ≤ S0 lab := by
    rw [S0_eq]; nlinarith [hx 0, hx 1, hx 2]
  have hSpos : 0 < S0 lab := lt_of_lt_of_le (by positivity) hS
  set r : ℝ := 2 * Fintype.card V / (((m : ℝ) - 1) * ((m : ℝ) - 1))
  have hr : 0 ≤ r := div_nonneg (by positivity) (mul_self_nonneg _)
  have hnum : |ellG (csz lab 0) (csz lab 1) (csz lab 2) (Gfun lab d)| ≤
      ‖d‖ * (Fintype.card V : ℝ) ^ 2 * r := by
    rw [ellG_Gfun]
    have hzero : ∑ e, d e * wl lab e.1 = 0 := by
      have := hd; simp only [ell, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [← this]; exact sum_congr rfl fun e _ => mul_comm _ _
    have : ∑ e, d e * ellG (csz lab 0) (csz lab 1) (csz lab 2) (ut lab e) =
        ∑ e, d e * (ellG (csz lab 0) (csz lab 1) (csz lab 2) (ut lab e) - wl lab e.1) := by
      simp only [mul_sub, sum_sub_distrib, hzero, sub_zero]
    rw [this]
    calc _ ≤ ∑ e : E0 V, |d e * (ellG (csz lab 0) (csz lab 1) (csz lab 2) (ut lab e) - wl lab e.1)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e : E0 V, ‖d‖ * r := by
          refine sum_le_sum fun e _ => ?_
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d e)
            (ellG_ut_sub_wl hcls hm h3 e) (abs_nonneg _) (norm_nonneg _)
      _ = Fintype.card (E0 V) * (‖d‖ * r) := by rw [sum_const, nsmul_eq_mul, card_univ]
      _ ≤ (Fintype.card V : ℝ) ^ 2 * (‖d‖ * r) :=
          mul_le_mul_of_nonneg_right card_E0_le (mul_nonneg (norm_nonneg _) hr)
      _ = _ := by ring
  unfold lam
  rw [abs_div, abs_of_pos hSpos, div_le_div_iff₀ hSpos (by positivity)]
  have hpos : 0 ≤ ‖d‖ * (Fintype.card V : ℝ) ^ 2 * r := mul_nonneg (by positivity) hr
  nlinarith [mul_le_mul hnum hS (by positivity) hpos]

/-! ### The local part and the error bound -/

theorem sum_mem_le (x : V) :
    ∑ e : E0 V, (if x ∈ e.1 then (1 : ℝ) else 0) ≤ 2 * Fintype.card V := by
  have hle : ∀ e : E0 V, (if x ∈ e.1 then (1 : ℝ) else 0) ≤
      (if (rep e).1 = x then 1 else 0) + (if (rep e).2 = x then 1 else 0) := by
    intro e
    rw [← rep_spec e]
    by_cases hm : x ∈ s((rep e).1, (rep e).2)
    · rw [if_pos hm]
      rcases Sym2.mem_iff.mp hm with h | h
      · rw [if_pos h.symm]; split_ifs <;> norm_num
      · rw [if_pos h.symm]; split_ifs <;> norm_num
    · rw [if_neg hm]; split_ifs <;> norm_num
  have hinj : ∑ e : E0 V, ((if (rep e).1 = x then (1 : ℝ) else 0) + (if (rep e).2 = x then 1 else 0)) ≤
      ∑ q : V × V, ((if q.1 = x then (1 : ℝ) else 0) + (if q.2 = x then 1 else 0)) := by
    rw [← sum_image (s := univ) (g := rep)
      (f := fun q : V × V => (if q.1 = x then (1 : ℝ) else 0) + (if q.2 = x then 1 else 0))
      (fun e _ e' _ h => rep_injective h)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun q _ _ => by split_ifs <;> norm_num
  have hcount : ∑ q : V × V, ((if q.1 = x then (1 : ℝ) else 0) + (if q.2 = x then 1 else 0)) =
      2 * Fintype.card V := by
    rw [Fintype.sum_prod_type]
    have h1 : ∀ u : V, ∑ v : V, ((if u = x then (1 : ℝ) else 0) + (if v = x then 1 else 0)) =
        (if u = x then (Fintype.card V : ℝ) else 0) + 1 := by
      intro u
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq']
      simp only [mem_univ, if_true]
      split_ifs <;> simp
    rw [sum_congr rfl (fun u _ => h1 u), sum_add_distrib, sum_ite_eq']
    simp only [mem_univ, if_true, sum_const, card_univ, nsmul_eq_mul, mul_one]
    ring
  calc _ ≤ _ := sum_le_sum fun e _ => hle e
    _ ≤ _ := hinj
    _ = _ := hcount

/-- **Local part of the error.** -/
theorem abs_local_le (hcls : ∀ k, 3 ≤ csz lab k) {m : ℕ} (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m)
    (d : E0 V → ℝ) (f : E0 V) :
    |∑ e, d e * (avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2))| ≤
      ‖d‖ * (8 * Fintype.card V / (((m : ℝ) - 1) * ((m : ℝ) - 1))) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
  have hP0 : 0 < ((m : ℝ) - 1) * ((m : ℝ) - 1) := by nlinarith
  have hPe : ∀ e : E0 V, ((m : ℝ) - 1) * ((m : ℝ) - 1) ≤ #(pairsF lab (rep e).1 (rep e).2) := by
    intro e
    have := card_pairsF_ge hm (rep e).1 (rep e).2
    have h1 : 1 ≤ m := by omega
    have : ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) ≤ #(pairsF lab (rep e).1 (rep e).2) := by
      exact_mod_cast this
    rwa [Nat.cast_sub h1, Nat.cast_one] at this
  set P : ℝ := ((m : ℝ) - 1) * ((m : ℝ) - 1)
  have hterm : ∀ e : E0 V, |d e * (avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2))| ≤
      ‖d‖ * ((2 / P) * ((if (rep f).1 ∈ e.1 then 1 else 0) + (if (rep f).2 ∈ e.1 then 1 else 0))) := by
    intro e
    rw [abs_mul]
    refine mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d e) ?_ (abs_nonneg _)
      (norm_nonneg _)
    refine (avgW_sub_ut hcls e f).trans ?_
    have hPpos : (0 : ℝ) < #(pairsF lab (rep e).1 (rep e).2) := lt_of_lt_of_le hP0 (hPe e)
    apply mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hP0 (hPe e)) _ (by split_ifs <;> norm_num)
      (by positivity)
    split_ifs <;> simp_all
  calc _ ≤ ∑ e, |d e * (avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : E0 V, ‖d‖ * ((2 / P) * ((if (rep f).1 ∈ e.1 then 1 else 0) +
          (if (rep f).2 ∈ e.1 then 1 else 0))) := sum_le_sum fun e _ => hterm e
    _ = ‖d‖ * (2 / P) * (∑ e : E0 V, (if (rep f).1 ∈ e.1 then (1 : ℝ) else 0) +
          ∑ e : E0 V, (if (rep f).2 ∈ e.1 then (1 : ℝ) else 0)) := by
        rw [← sum_add_distrib, mul_sum]; refine sum_congr rfl fun e _ => by ring
    _ ≤ ‖d‖ * (2 / P) * (2 * Fintype.card V + 2 * Fintype.card V) :=
        mul_le_mul_of_nonneg_left (add_le_add (sum_mem_le _) (sum_mem_le _)) (by positivity)
    _ = _ := by field_simp; ring

/-- The error operator `E = I - M Φ₀`. -/
theorem err_eq (hcls : ∀ k, 3 ≤ csz lab k) (hS : S0 lab ≠ 0) (d : E0 V → ℝ) (f : E0 V) :
    d f - Minc lab (Phi0 lab d) f =
      ∑ e, d e * (avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2)) +
        lam lab d * Gfix (lab (rep f).1) (lab (rep f).2) := by
  rw [Minc_Phi0 hcls hS]; ring

/-- **The error of `Φ₀` halves norms on `ker ℓ`** (balanced classes, `m ≥ 512`). -/
theorem norm_err_le (hcls : ∀ k, 3 ≤ csz lab k) {m : ℕ} (hm : ∀ k, m ≤ csz lab k)
    (h512 : 512 ≤ m) (hbal : Fintype.card V ≤ 4 * m) (d : E0 V → ℝ) (hd : ell lab d = 0) :
    ‖d - Minc lab (Phi0 lab d)‖ ≤ ‖d‖ / 2 := by
  have h3 : 3 ≤ m := by omega
  have hmR : (512 : ℝ) ≤ m := by exact_mod_cast h512
  have hnR : (Fintype.card V : ℝ) ≤ 4 * m := by exact_mod_cast hbal
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hx : ∀ k, (m : ℝ) ≤ csz lab k := fun k => by exact_mod_cast hm k
  have hS : S0 lab ≠ 0 := by
    have : 3 * (m : ℝ) ^ 2 ≤ S0 lab := by rw [S0_eq]; nlinarith [hx 0, hx 1, hx 2]
    have : (0 : ℝ) < S0 lab := lt_of_lt_of_le (by positivity) this
    exact this.ne'
  set n : ℝ := (Fintype.card V : ℝ)
  set P : ℝ := ((m : ℝ) - 1) * ((m : ℝ) - 1)
  have hP : (m : ℝ) ^ 2 / 2 ≤ P := by simp only [P]; nlinarith
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) hP
  -- the two coefficients
  have c1 : 8 * n / P ≤ 1 / 4 := by
    rw [div_le_iff₀ hPpos]; nlinarith
  have c2 : n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity), show n ^ 2 * (2 * n / P) = 2 * n ^ 3 / P by ring,
      div_le_iff₀ hPpos]
    have hn3 : n ^ 3 ≤ 64 * (m : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hn0 hnR 3; nlinarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
    have h4 : (512 : ℝ) * (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := by
      have := mul_le_mul_of_nonneg_left hmR hm0; nlinarith
    have hPm : 1 / 4 * (3 * (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 / 2) ≤ 1 / 4 * (3 * (m : ℝ) ^ 2) * P :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  have hlam := abs_lam_le hcls hm h3 d hd
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun f => ?_
  rw [Real.norm_eq_abs]
  show |d f - Minc lab (Phi0 lab d) f| ≤ _
  rw [err_eq hcls hS]
  have hloc := abs_local_le hcls hm h3 d f
  have hfix : |Gfix (lab (rep f).1) (lab (rep f).2)| ≤ 1 := by unfold Gfix; split_ifs <;> norm_num
  have hl2 : |lam lab d * Gfix (lab (rep f).1) (lab (rep f).2)| ≤ ‖d‖ * (1 / 4) := by
    rw [abs_mul]
    calc |lam lab d| * |Gfix _ _| ≤ |lam lab d| * 1 :=
          mul_le_mul_of_nonneg_left hfix (abs_nonneg _)
      _ ≤ ‖d‖ * n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) := by rw [mul_one]; exact hlam
      _ = ‖d‖ * (n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2)) := by ring
      _ ≤ ‖d‖ * (1 / 4) := mul_le_mul_of_nonneg_left c2 (norm_nonneg _)
  have hl1 : ‖d‖ * (8 * n / P) ≤ ‖d‖ * (1 / 4) := mul_le_mul_of_nonneg_left c1 (norm_nonneg _)
  calc _ ≤ |∑ e, d e * (avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2))| +
        |lam lab d * Gfix (lab (rep f).1) (lab (rep f).2)| := abs_add_le _ _
    _ ≤ ‖d‖ * (1 / 4) + ‖d‖ * (1 / 4) := add_le_add (hloc.trans hl1) hl2
    _ = ‖d‖ / 2 := by ring

end Assembly



end CDRBicolour.Absorption
