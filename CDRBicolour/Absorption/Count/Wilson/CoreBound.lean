/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.Core

/-!
# Optimal counting constant, part 10: the core bound (item 4)

`wilson_core`: for an admissible profile `(a, b, c)`, an admissible `g ≥ 15`,
`t = ⌊2 min(a, b, c)/(2g + 1)⌋`, the conclusion of Theorem T for `α = 1/(16(2g+1))²`,
`C = 6g(2g+1) + 8`, and explicit largeness conditions,

    (3/2) g (g − 1) t² (log t − 2) ≤ log realCount(a, b, c).

The proof is split: arithmetic of `t` (`t_bounds`, `wc_cond`, `wc_rlo`, `wc_rhi`, `wc_h4t`,
`wc_hN4`), the local seed (`wc_local`), the global seed (`wc_seed`), H3 (`wc_H3`), and the count
(`wc_log`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Count

/-- Hinge constant. -/
def Mg (g : ℕ) : ℕ := 16 * (2 * g + 1)
/-- Density constant of Theorem T. -/
def alphaG (g : ℕ) : ℝ := 1 / ((Mg g ^ 2 : ℕ) : ℝ)
/-- Seed constant of Theorem T. -/
def CG (g : ℕ) : ℝ := 6 * g * (2 * g + 1) + 8

section

variable {a b c g t : ℕ}

theorem card_resK (h : WCond a b c g t) (P : Fin 3) :
    #(resK (col3 a b c) (univ.filter fun v : Fin (a + b + c) => InR g t v) P) =
      csize a b c P - g * t := by
  rw [← card_off_range (a := a) (b := b) (c := c) P (gt_le_csize h P) le_rfl]
  congr 1
  ext v
  simp only [resK, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1, off_lt v⟩
  · rintro ⟨rfl, h1, -⟩; exact ⟨h1, rfl⟩

/-- `t (2g+1) ≤ 2 m₀ < t (2g+1) + (2g+1)`. -/
theorem t_bounds (hg : 1 ≤ g) (htdef : t = 2 * min a (min b c) / (2 * g + 1)) :
    t * (2 * g + 1) ≤ 2 * min a (min b c) ∧
      2 * min a (min b c) < t * (2 * g + 1) + (2 * g + 1) := by
  constructor
  · rw [htdef]; exact Nat.div_mul_le_self _ _
  · have := Nat.lt_div_mul_add (a := 2 * min a (min b c)) (show 0 < 2 * g + 1 by omega)
    rw [← htdef] at this
    exact this

theorem wc_cond (hg : 1 ≤ g) (ht0 : 0 < t) (htdef : t = 2 * min a (min b c) / (2 * g + 1)) :
    WCond a b c g t := by
  obtain ⟨h1, -⟩ := t_bounds hg htdef
  have e1 : t * (2 * g + 1) = 2 * (g * t) + t := by ring
  exact ⟨by omega, by omega, by omega, ht0⟩

theorem wc_rlo (hg : 1 ≤ g) (htdef : t = 2 * min a (min b c) / (2 * g + 1)) (P : Fin 3) :
    t ≤ 2 * (csize a b c P - g * t) := by
  obtain ⟨h1, -⟩ := t_bounds hg htdef
  have e1 : t * (2 * g + 1) = 2 * (g * t) + t := by ring
  have := csize_ge_min (a := a) (b := b) (c := c) P
  omega

theorem wc_rhi (hadm : AdmissibleProfile a b c) (hg : 1 ≤ g)
    (htdef : t = 2 * min a (min b c) / (2 * g + 1)) (hW : WCond a b c g t)
    (ht1 : 2 * (Real.sqrt (2 * ((a + b + c : ℕ) : ℝ)) + g + 2) ≤ (t : ℝ)) (P : Fin 3) :
    csize a b c P - g * t + 1 ≤ t := by
  obtain ⟨-, h2⟩ := t_bounds hg htdef
  have h1 := csize_le_min_add hadm P
  have h3 : ((2 * min a (min b c) : ℕ) : ℝ) < ((t * (2 * g + 1) + (2 * g + 1) : ℕ) : ℝ) := by
    exact_mod_cast h2
  have hg2 := gt_le_csize hW P
  have : ((csize a b c P - g * t + 1 : ℕ) : ℝ) ≤ t := by
    push_cast [Nat.cast_sub hg2] at h1 h3 ht1 ⊢
    nlinarith
  exact_mod_cast this

theorem wc_h4t (hadm : AdmissibleProfile a b c) (hg : 1 ≤ g)
    (htdef : t = 2 * min a (min b c) / (2 * g + 1)) (hn400 : 400 ≤ a + b + c) (ht0 : 0 < t) :
    a + b + c ≤ 4 * (t * (2 * g + 1)) := by
  obtain ⟨-, h2⟩ := t_bounds hg htdef
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all hadm hn400
  have hm4 : a + b + c + 8 ≤ 4 * min a (min b c) := by omega
  have hgt : g ≤ g * t := Nat.le_mul_of_pos_right g ht0
  have e1 : t * (2 * g + 1) = 2 * (g * t) + t := by ring
  omega

theorem wc_hN4 (h4t : a + b + c ≤ 4 * (t * (2 * g + 1))) (ht : 512 ≤ t) :
    a + b + c ≤ Mg g * (t / 2 - 5) := by
  set u := t / 2 - 5 with hu
  have htu : t ≤ 2 * u + 11 := by omega
  have hu8 : 8 * u + 44 ≤ 16 * u := by omega
  have h8 := Nat.mul_le_mul_left (2 * g + 1) hu8
  calc a + b + c ≤ 4 * (t * (2 * g + 1)) := h4t
    _ ≤ 4 * ((2 * u + 11) * (2 * g + 1)) := by gcongr
    _ = (2 * g + 1) * (8 * u + 44) := by ring
    _ ≤ (2 * g + 1) * (16 * u) := h8
    _ = Mg g * u := by unfold Mg; ring

set_option maxHeartbeats 1000000 in
/-- The local seed for the Wilson parameters. -/
theorem wc_local (hadm : AdmissibleProfile a b c) (hg1 : 1 ≤ g) (h : WCond a b c g t)
    (ht512 : 512 ≤ t)
    (hrlo : ∀ P : Fin 3, t ≤ 2 * (csize a b c P - g * t))
    (hrhi : ∀ P : Fin 3, csize a b c P - g * t + 1 ≤ t)
    (ht3 : 8 * 52000 * (g : ℝ) * (4 + Real.sqrt (2 * ((a + b + c : ℕ) : ℝ))) ≤ 3 * (t : ℝ)) :
    ∃ φ : Finset (Fin (mloc a b c g t)) → ℝ,
      (∀ T ∈ tri (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)),
        1 / (4 * g * xx t) ≤ φ T ∧ φ T ≤ 3 / xx t) ∧
      ∀ e : E0 (Fin (mloc a b c g t)),
        Minc (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)) φ e = tau' g t e.1 := by
  set D := Real.sqrt (2 * ((a + b + c : ℕ) : ℝ)) with hDdef
  have ht0 : 0 < t := by omega
  have hla : la a b c g t = t + (a - g * t) := rfl
  have hlb : lb a b c g t = t + (b - g * t) := rfl
  have hlc : lc a b c g t = t + (c - g * t) := rfl
  have hcl : ∀ P : Fin 3, csize (la a b c g t) (lb a b c g t) (lc a b c g t) P =
      t + (csize a b c P - g * t) := fun P => csize_loc P
  have hr0 := hrlo 0; have hr1 := hrlo 1; have hr2 := hrlo 2
  have hR0 := hrhi 0; have hR1 := hrhi 1; have hR2 := hrhi 2
  simp only [csize, Fin.isValue, Fin.reduceEq, ite_true, ite_false] at hr0 hr1 hr2 hR0 hR1 hR2
  have hagt : g * t ≤ a := h.hA
  have hbgt : g * t ≤ b := h.hB
  have hcgt : g * t ≤ c := h.hC
  have rr_eq : ∀ k, rr (la a b c g t) (lb a b c g t) (lc a b c g t) t k =
      (csize a b c k : ℝ) - g * t := by
    intro k
    unfold rr
    rw [hcl k]
    push_cast [Nat.cast_sub (gt_le_csize h k)]
    ring
  have hy1 : xx t / 4 ≤ yy (la a b c g t) (lb a b c g t) (lc a b c g t) t := by
    unfold yy xx
    rw [rr_eq, rr_eq, rr_eq]
    have q : ∀ P : Fin 3, (t : ℝ) ≤ 2 * ((csize a b c P : ℝ) - g * t) := by
      intro P
      have := hrlo P
      have h2 := gt_le_csize h P
      have : ((t : ℕ) : ℝ) ≤ ((2 * (csize a b c P - g * t) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast [Nat.cast_sub h2] at this; linarith
    have := q 0; have := q 1; have := q 2
    linarith
  have hy2 : yy (la a b c g t) (lb a b c g t) (lc a b c g t) t ≤ xx t := by
    unfold yy xx
    rw [rr_eq, rr_eq, rr_eq]
    have q : ∀ P : Fin 3, (csize a b c P : ℝ) - g * t + 1 ≤ t := by
      intro P
      have := hrhi P
      have h2 := gt_le_csize h P
      have : ((csize a b c P - g * t + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast this
      push_cast [Nat.cast_sub h2] at this; linarith
    have := q 0; have := q 1; have := q 2
    linarith
  have hDd : ∀ k l, |rr (la a b c g t) (lb a b c g t) (lc a b c g t) t k -
      rr (la a b c g t) (lb a b c g t) (lc a b c g t) t l| ≤ D := by
    intro k l
    rw [rr_eq, rr_eq, show (csize a b c k : ℝ) - g * t - (csize a b c l - g * t) =
      csize a b c k - csize a b c l by ring]
    exact csize_diff hadm k l
  have hid : ((la a b c g t : ℕ) - (t : ℝ)) ^ 2 + ((lb a b c g t : ℕ) - (t : ℝ)) ^ 2 +
      ((lc a b c g t : ℕ) - (t : ℝ)) ^ 2 -
      ((la a b c g t : ℕ) - (t : ℝ)) * ((lb a b c g t : ℕ) - (t : ℝ)) -
      ((la a b c g t : ℕ) - (t : ℝ)) * ((lc a b c g t : ℕ) - (t : ℝ)) -
      ((lb a b c g t : ℕ) - (t : ℝ)) * ((lc a b c g t : ℕ) - (t : ℝ)) =
      3 * g * t + ((la a b c g t : ℕ) - (t : ℝ)) + ((lb a b c g t : ℕ) - (t : ℝ)) +
        ((lc a b c g t : ℕ) - (t : ℝ)) := by
    rw [hla, hlb, hlc]
    push_cast [Nat.cast_sub hagt, Nat.cast_sub hbgt, Nat.cast_sub hcgt]
    have e := hadm.2.2.2.2.1
    have e' : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 - a * b - a * c - b * c = a + b + c := by
      exact_mod_cast e
    linear_combination e'
  have hm0 : ∀ k, t + t / 2 ≤ csz (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)) k := by
    intro k
    rw [csz_col3]
    fin_cases k <;> simp [hla, hlb, hlc] <;> omega
  have hbal : la a b c g t + lb a b c g t + lc a b c g t ≤ 4 * (t + t / 2) := by
    rw [hla, hlb, hlc]; omega
  have hsmall : 8 * 52000 * (g : ℝ) * (4 + D) ≤
      ((la a b c g t + lb a b c g t + lc a b c g t : ℕ) : ℝ) := by
    have : 3 * t ≤ la a b c g t + lb a b c g t + lc a b c g t := by rw [hla, hlb, hlc]; omega
    have : (3 * t : ℝ) ≤ ((la a b c g t + lb a b c g t + lc a b c g t : ℕ) : ℝ) := by
      exact_mod_cast this
    linarith
  exact local_seed (g := g) hg1 ht0 (by simp [hla, hlb, hlc]) hy1 hy2 hDd hid hm0
    (by omega) hbal hsmall

variable {S : Finset (Finset (Fin g))}

/-- The global diffuse seed (H1). -/
theorem wc_seed (hS : _root_.STS.IsSTS S) (hW : WCond a b c g t) (Λ : LFam S t) (hg1 : 1 ≤ g)
    (h4t : a + b + c ≤ 4 * (t * (2 * g + 1)))
    {φ : Finset (Fin (mloc a b c g t)) → ℝ}
    (hφ : ∀ T ∈ tri (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)),
      1 / (4 * g * xx t) ≤ φ T ∧ φ T ≤ 3 / xx t)
    (hM : ∀ e : E0 (Fin (mloc a b c g t)),
      Minc (col3 (la a b c g t) (lb a b c g t) (lc a b c g t)) φ e = tau' g t e.1) :
    ∃ μ, IsDiffuseSeed (rHost (col3 a b c) (LX hW Λ)) cdrF (CG g) μ := by
  have ht0 := hW.ht
  have hgt0 : 0 < g * t := Nat.mul_pos (by omega) ht0
  have hgta : g * t ≤ a := hW.hA
  have hn0 : (0 : ℝ) < ((a + b + c : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < a + b + c by omega)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hgtn : (g : ℝ) * t ≤ ((a + b + c : ℕ) : ℝ) := by
    have : g * t ≤ a + b + c := by omega
    exact_mod_cast this
  have h4tR : ((a + b + c : ℕ) : ℝ) ≤ 4 * ((t : ℝ) * (2 * g + 1)) := by exact_mod_cast h4t
  have hC1 : 1 / (CG g * ((a + b + c : ℕ) : ℝ)) ≤ 1 / (4 * g * xx t) := by
    unfold CG xx
    apply one_div_le_one_div_of_le
      (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith))
    have e0 : (0 : ℝ) ≤ 6 * g * (2 * g + 1) := by positivity
    calc (4 : ℝ) * g * (2 * t) = 8 * (g * t) := by ring
      _ ≤ 8 * ((a + b + c : ℕ) : ℝ) := by linarith
      _ ≤ (6 * g * (2 * g + 1) + 8) * ((a + b + c : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hn0.le
  have hC2 : (g : ℝ) * max (3 / xx t) 0 ≤ CG g / ((a + b + c : ℕ) : ℝ) := by
    rw [max_eq_left (by unfold xx; positivity)]
    unfold CG xx
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) hn0]
    nlinarith [mul_le_mul_of_nonneg_left h4tR (by linarith : (0 : ℝ) ≤ 3 * g)]
  exact ⟨_, global_seed hW hS Λ (by omega) (lo := 1 / (4 * g * xx t)) (hi := 3 / xx t)
    (by unfold xx; positivity) hφ hM hC1 hC2⟩

/-- H3 for the residual host. -/
theorem wc_H3 (hW : WCond a b c g t) (Λ : LFam S t)
    (hU : Univ (LX hW Λ) (univ.filter fun v : Fin (a + b + c) => InR g t v))
    (hres : ∀ P : Fin 3, t / 2 ≤ #(resK (col3 a b c)
      (univ.filter fun v : Fin (a + b + c) => InR g t v) P))
    (hN4 : a + b + c ≤ Mg g * (t / 2 - 5)) (ht : 14 ≤ t) :
    CommonNbrCond (rHost (col3 a b c) (LX hW Λ)) cdrF (alphaG g) := by
  have hMg : 0 < Mg g := by unfold Mg; omega
  refine H3_of_reserve hU fun k => ?_
  have hk := hres k
  have hM2 : (Mg g : ℝ) ≤ (((Mg g) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have hMR : (0 : ℝ) < Mg g := by exact_mod_cast hMg
  have h1 : alphaG g * ((a + b + c : ℕ) : ℝ) ≤ ((a + b + c : ℕ) : ℝ) / Mg g := by
    unfold alphaG
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (by positivity) hMR hM2
  have h2 : ((a + b + c : ℕ) : ℝ) ≤ Mg g * ((t / 2 - 5 : ℕ) : ℝ) := by exact_mod_cast hN4
  have h3 : ((a + b + c : ℕ) : ℝ) / Mg g ≤ ((t / 2 - 5 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hMR, mul_comm]; exact h2
  have h4 : ((t / 2 - 5 : ℕ) : ℝ) + 2 ≤ ((t / 2 : ℕ) : ℝ) := by
    have : t / 2 - 5 + 2 ≤ t / 2 := by omega
    exact_mod_cast this
  have h5 : ((t / 2 : ℕ) : ℝ) ≤ #(resK (col3 a b c)
      (univ.filter fun v : Fin (a + b + c) => InR g t v) k) := by exact_mod_cast hk
  rw [Fintype.card_fin]
  linarith

theorem wc_nodd (hadm : AdmissibleProfile a b c) :
    Even (Fintype.card (Fin (a + b + c)) - 1) := by
  rw [Fintype.card_fin, Nat.even_iff]
  have := hadm.2.2.2.1
  omega

open Classical in
/-- The count. -/
theorem wc_log (hS : _root_.STS.IsSTS S) (hW : WCond a b c g t) (Λ₀ : LFam S t) (hg1 : 1 ≤ g)
    (ht512 : 512 ≤ t) {Dd : Finset (Finset (Fin (a + b + c)))}
    (hDd : IsDecomposition (rHost (col3 a b c) (LX hW Λ₀)) cdrF
      (edges (rHost (col3 a b c) (LX hW Λ₀))) Dd) :
    3 / 2 * (g : ℝ) * (g - 1) * (t : ℝ) ^ 2 * (Real.log t - 2) ≤
      Real.log (realCount a b c) := by
  have ht0 : 0 < t := by omega
  have hcnt : _root_.STS.L t ^ (9 * #(OT S)) ≤ realCount a b c :=
    le_trans (le_of_eq (card_LFam t).symm) (card_LFam_le hW hS Λ₀ hDd)
  have hL1 : 1 ≤ _root_.STS.L t := by
    unfold _root_.STS.L
    exact Nat.card_pos_iff.2 ⟨⟨⟨_, cyc_latin ht0⟩⟩, inferInstance⟩
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hlogL := _root_.STS.hL_one _root_.STS.van_der_waerden t (by omega)
  have hlogt : 2 ≤ Real.log t := by
    have h82 : Real.exp 2 < 512 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ < 2.7182818286 * 2.7182818286 := by gcongr
        _ < 512 := by norm_num
    have : (512 : ℝ) ≤ t := by exact_mod_cast ht512
    exact (Real.le_log_iff_exp_le htR).mpr (by linarith)
  have hpow : 1 ≤ _root_.STS.L t ^ (9 * #(OT S)) := Nat.one_le_pow _ _ (by omega)
  have hlog1 : (9 * #(OT S) : ℝ) * Real.log (_root_.STS.L t) ≤ Real.log (realCount a b c) := by
    have h1 : ((_root_.STS.L t ^ (9 * #(OT S)) : ℕ) : ℝ) ≤ realCount a b c := by
      exact_mod_cast hcnt
    have hp : (0 : ℝ) < ((_root_.STS.L t ^ (9 * #(OT S)) : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < _root_.STS.L t ^ (9 * #(OT S)) by omega)
    have h2 := Real.log_le_log hp h1
    rw [Nat.cast_pow, Real.log_pow] at h2
    push_cast at h2
    exact h2
  have hOT : (3 / 2 : ℝ) * g * (g - 1) ≤ 9 * #(OT S) := by
    have h1 := card_S_ge hS
    have h2 := card_S_le_OT hS
    have h3 : ((g * (g - 1) : ℕ) : ℝ) ≤ 6 * #(OT S) := by
      have : g * (g - 1) ≤ 6 * #(OT S) := h1.trans (by omega)
      exact_mod_cast this
    push_cast [Nat.cast_sub hg1] at h3
    linarith
  have hpos : 0 ≤ (t : ℝ) ^ 2 * (Real.log t - 2) := mul_nonneg (by positivity) (by linarith)
  calc 3 / 2 * (g : ℝ) * (g - 1) * (t : ℝ) ^ 2 * (Real.log t - 2)
      = (3 / 2 * (g : ℝ) * (g - 1)) * ((t : ℝ) ^ 2 * (Real.log t - 2)) := by ring
    _ ≤ (9 * #(OT S) : ℝ) * ((t : ℝ) ^ 2 * (Real.log t - 2)) :=
        mul_le_mul_of_nonneg_right hOT hpos
    _ ≤ (9 * #(OT S) : ℝ) * Real.log (_root_.STS.L t) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ ≤ Real.log (realCount a b c) := hlog1

end

/-- **The core bound.** -/
theorem wilson_core {a b c g t : ℕ} (hadm : AdmissibleProfile a b c) (hg15 : 15 ≤ g)
    (hga : _root_.STS.Admissible g) (htdef : t = 2 * min a (min b c) / (2 * g + 1))
    (hT : ∀ H : Host (Fin (a + b + c)) (Fin 3), (∃ μ, IsDiffuseSeed H cdrF (CG g) μ) →
      IsPhysical H cdrF (edges H) → CommonNbrCond H cdrF (alphaG g) →
      HingeCond H cdrF (alphaG g) 6 → ∃ D, IsDecomposition H cdrF (edges H) D)
    (hn400 : 400 ≤ a + b + c) (ht512 : 512 ≤ t)
    (ht1 : 2 * (Real.sqrt (2 * ((a + b + c : ℕ) : ℝ)) + g + 2) ≤ (t : ℝ))
    (ht3 : 8 * 52000 * (g : ℝ) * (4 + Real.sqrt (2 * ((a + b + c : ℕ) : ℝ))) ≤ 3 * (t : ℝ)) :
    3 / 2 * (g : ℝ) * (g - 1) * (t : ℝ) ^ 2 * (Real.log t - 2) ≤ Real.log (realCount a b c) := by
  have hg1 : 1 ≤ g := by omega
  have ht0 : 0 < t := by omega
  have h : WCond a b c g t := wc_cond hg1 ht0 htdef
  obtain ⟨S, hS⟩ := exists_sts hg15 hga
  let Λ₀ : LFam S t := fun _ =>
    ⟨fun i j => ⟨(i.val + j.val) % t, Nat.mod_lt _ ht0⟩, cyc_latin ht0⟩
  have hrlo := wc_rlo (a := a) (b := b) (c := c) hg1 htdef
  have hrhi := wc_rhi hadm hg1 htdef h ht1
  have h4t := wc_h4t hadm hg1 htdef hn400 ht0
  -- H1
  obtain ⟨φ, hφ, hM⟩ := wc_local hadm hg1 h ht512 hrlo hrhi ht3
  have hseed := wc_seed hS h Λ₀ hg1 h4t hφ hM
  -- H2
  have hres : ∀ P : Fin 3, t / 2 ≤ #(resK (col3 a b c)
      (univ.filter fun v : Fin (a + b + c) => InR g t v) P) := by
    intro P; rw [card_resK h P]; have := hrlo P; omega
  have hU := univ_reserve h hS Λ₀
  have hbig : BigR (col3 a b c) (LX h Λ₀) :=
    bigR_of_reserve hU fun k => (by omega : 5 ≤ t / 2).trans (hres k)
  obtain ⟨o, ho, hoadj⟩ := exists_base hbig (⟨0, by omega⟩ : Fin (a + b + c))
  have hs0 := csz_col3 a b c 0
  have hs1 := csz_col3 a b c 1
  have hs2 := csz_col3 a b c 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hs0 hs1 hs2
  obtain ⟨h01, h02, h12⟩ := adm_even_mul hadm
  have hH2 : IsPhysical (rHost (col3 a b c) (LX h Λ₀)) cdrF
      (edges (rHost (col3 a b c) (LX h Λ₀))) :=
    residual_physical hbig ho hoadj (crossP h Λ₀) (crossP_allowed h Λ₀) (crossP_disj h hS Λ₀) rfl
      (wc_nodd hadm) (by rw [hs0, hs1]; exact h01) (by rw [hs0, hs2]; exact h02)
      (by rw [hs1, hs2]; exact h12) (by rw [hs0, hs1, hs2]; exact hadm.2.2.2.2.1)
  -- H3, H4
  have hN4 := wc_hN4 h4t ht512
  have hMg : 0 < Mg g := by unfold Mg; omega
  have hH4 : HingeCond (rHost (col3 a b c) (LX h Λ₀)) cdrF (alphaG g) 6 :=
    H4_of_reserve hU hMg hres (by rw [Fintype.card_fin]; exact hN4)
  have hH3 := wc_H3 h Λ₀ hU hres hN4 (by omega)
  -- Theorem T and the count
  obtain ⟨Dd, hDd⟩ := hT (rHost (col3 a b c) (LX h Λ₀)) hseed hH2 hH3 hH4
  exact wc_log hS h Λ₀ hg1 ht512 hDd

end CDRBicolour.Absorption.Count.Wilson
