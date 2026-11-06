/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.ResidualHinge
public import CDRBicolour.Absorption.ResidualLattice

/-!
# Optimal counting constant, part 2: hosts with a universal reserve (item 4)

A *universal reserve* of the residual graph `rG L` is a set `R` of points adjacent to every other
point.  With enough reserve points of every class:

* `bigR_of_reserve`: the density condition `BigR` used by `residual_physical` (H2);
* `H3_of_reserve`: common neighbours (H3);
* `H4_of_reserve`: hinges of order `6` (H4), with the two new points `x, y` in the reserve.

Here `L` may be dense: only the reserve has to be large.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Absorption

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3} {L : Finset (Sym2 V)}

/-- `R` is a universal reserve of `rG L`. -/
def Univ (L : Finset (Sym2 V)) (R : Finset V) : Prop := ∀ w ∈ R, ∀ p, p ≠ w → (rG L).Adj w p

/-- Reserve points of class `k`. -/
def resK (lab : V → Fin 3) (R : Finset V) (k : Fin 3) : Finset V := R.filter fun w => lab w = k

theorem bigR_of_reserve {R : Finset V} (hU : Univ L R) (hR : ∀ k, 5 ≤ #(resK lab R k)) :
    BigR lab L := by
  intro k p q r s
  have hns : ¬ resK lab R k ⊆ {p, q, r, s} := fun hsub => by
    have h1 := card_le_card hsub
    have h2 : #({p, q, r, s} : Finset V) ≤ 4 := card_le_four
    have := hR k
    omega
  obtain ⟨w, hw, hwB⟩ := not_subset.1 hns
  simp only [resK, mem_filter] at hw
  simp only [mem_insert, mem_singleton, not_or] at hwB
  obtain ⟨h1, h2, h3, h4⟩ := hwB
  exact ⟨w, hw.2, hU w hw.1 p (Ne.symm h1), hU w hw.1 q (Ne.symm h2), hU w hw.1 r (Ne.symm h3),
    hU w hw.1 s (Ne.symm h4)⟩

theorem H3_of_reserve {R : Finset V} (hU : Univ L R) {α : ℝ}
    (hR : ∀ k, α * Fintype.card V + 2 ≤ #(resK lab R k)) :
    CommonNbrCond (rHost lab L) cdrF α := by
  intro u v _ k _
  have hsub : resK lab R k \ {u, v} ⊆ commonNbrs (rHost lab L) k u v := by
    intro w hw
    simp only [resK, mem_sdiff, mem_filter, mem_insert, mem_singleton, not_or] at hw
    simp only [commonNbrs, mem_filter, mem_univ, true_and]
    exact ⟨(hU w hw.1.1 u fun e => hw.2.1 e.symm).symm,
      (hU w hw.1.1 v fun e => hw.2.2 e.symm).symm, hw.1.2⟩
  have h1 := card_le_card hsub
  have h2 := le_card_sdiff ({u, v} : Finset V) (resK lab R k)
  have h3 : #({u, v} : Finset V) ≤ 2 := card_le_two
  have h4 : (#(resK lab R k) : ℝ) ≤ #(commonNbrs (rHost lab L) k u v) + 2 := by
    have : #(resK lab R k) ≤ #(commonNbrs (rHost lab L) k u v) + 2 := by omega
    exact_mod_cast this
  linarith [hR k]

theorem H4_of_reserve {R : Finset V} (hU : Univ L R) {m M : ℕ} (hM : 0 < M)
    (hR : ∀ k, m ≤ #(resK lab R k)) (hN : Fintype.card V ≤ M * (m - 5)) :
    HingeCond (rHost lab L) cdrF (1 / (M ^ 2 : ℕ)) 6 := by
  intro u v a b hab hTa0 hTb0
  refine ⟨6, le_rfl, le_rfl, ?_⟩
  have hTa : IsAllowed (rHost lab L) cdrF ({u, v, a} : Finset V) := by convert hTa0
  have hTb : IsAllowed (rHost lab L) cdrF ({u, v, b} : Finset V) := by convert hTb0
  obtain ⟨huv, hua, hva⟩ := ne_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := ne_of_card_three hTb.1
  have adjA : ∀ p ∈ ({u, v, a} : Finset V), ∀ q ∈ ({u, v, a} : Finset V), p ≠ q →
      (rG L).Adj p q := hTa.2.1
  have adjB : ∀ p ∈ ({u, v, b} : Finset V), ∀ q ∈ ({u, v, b} : Finset V), p ≠ q →
      (rG L).Adj p q := hTb.2.1
  have Aua : (rG L).Adj u a := adjA u (by simp) a (by simp) hua
  have Ava : (rG L).Adj v a := adjA v (by simp) a (by simp) hva
  have Aub : (rG L).Adj u b := adjB u (by simp) b (by simp) hub
  have Avb : (rG L).Adj v b := adjB v (by simp) b (by simp) hvb
  have hFa : ({lab u, lab v, lab a} : Multiset (Fin 3)) ∈ cdrF := by
    have : ({u, v, a} : Finset V).val.map lab ∈ cdrF := hTa.2.2
    rwa [val_map_triple lab huv (Ne.symm hua) (Ne.symm hva)] at this
  have hFb : ({lab u, lab v, lab b} : Multiset (Fin 3)) ∈ cdrF := by
    have : ({u, v, b} : Finset V).val.map lab ∈ cdrF := hTb.2.2
    rwa [val_map_triple lab huv (Ne.symm hub) (Ne.symm hvb)] at this
  set B : Finset V := {u, v, a, b} with hBdef
  have hB : #B ≤ 4 := card_le_four
  set X := resK lab R (lab u) \ B with hX
  set Y := resK lab R (lab v) \ B with hY
  have memX : ∀ x ∈ X, x ∈ R ∧ lab x = lab u ∧ x ∉ B := by
    intro x hx; simp only [hX, resK, mem_sdiff, mem_filter] at hx; exact ⟨hx.1.1, hx.1.2, hx.2⟩
  have memY : ∀ y ∈ Y, y ∈ R ∧ lab y = lab v ∧ y ∉ B := by
    intro y hy; simp only [hY, resK, mem_sdiff, mem_filter] at hy; exact ⟨hy.1.1, hy.1.2, hy.2⟩
  set P := (X ×ˢ Y).filter fun p : V × V => p.1 ≠ p.2 with hP
  have hgood : ∀ p ∈ P, Six u v a b p.1 p.2 ∧ lab p.1 = lab u ∧ lab p.2 = lab v ∧
      (rG L).Adj u p.2 ∧ (rG L).Adj p.1 v ∧ (rG L).Adj p.1 p.2 ∧ (rG L).Adj p.1 a ∧
      (rG L).Adj p.1 b ∧ (rG L).Adj p.2 a ∧ (rG L).Adj p.2 b := by
    rintro ⟨x, y⟩ hp
    simp only [hP, mem_filter, mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hp
    obtain ⟨xR, lx, xB⟩ := memX x hx
    obtain ⟨yR, ly, yB⟩ := memY y hy
    simp only [hBdef, mem_insert, mem_singleton, not_or] at xB yB
    obtain ⟨xu, xv, xa, xb⟩ := xB
    obtain ⟨yu, yv, ya, yb⟩ := yB
    have Ax : ∀ p, p ≠ x → (rG L).Adj x p := hU x xR
    have Ay : ∀ p, p ≠ y → (rG L).Adj y p := hU y yR
    exact ⟨⟨huv, hua, hub, Ne.symm xu, Ne.symm yu, hva, hvb, Ne.symm xv, Ne.symm yv, hab,
      Ne.symm xa, Ne.symm ya, Ne.symm xb, Ne.symm yb, hxy⟩, lx, ly,
      (Ay u (Ne.symm yu)).symm, Ax v (Ne.symm xv), Ax y (Ne.symm hxy), Ax a (Ne.symm xa),
      Ax b (Ne.symm xb), Ay a (Ne.symm ya), Ay b (Ne.symm yb)⟩
  have hsub : P.image (fun p => hcore u v a b p.1 p.2) ⊆ hinges (rHost lab L) cdrF u v a b 6 := by
    intro J hJ
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hJ
    obtain ⟨h6, lx, ly, A1, A2, A3, A4, A5, A6, A7⟩ := hgood p hp
    simp only [hinges, mem_filter, mem_univ, true_and]
    exact ⟨hcore_isHingeR h6 lx ly hFa hFb Aua Ava Aub Avb A1 A2 A3 A4 A5 A6 A7, support_hcore h6⟩
  have hinj : Set.InjOn (fun p : V × V => hcore u v a b p.1 p.2) P := by
    intro p hp q hq he
    obtain ⟨h1, h2⟩ := hcore_inj (hgood p hp).1 (hgood q hq).1 he
    exact Prod.ext h1 h2
  -- counting
  have hfib : ∀ x ∈ X, #Y - 1 ≤ #(Y.filter fun y => x ≠ y) := by
    intro x _
    have h1 := le_card_sdiff ({x} : Finset V) Y
    have h3 : Y \ {x} = Y.filter fun y => x ≠ y := by
      ext y; simp [eq_comm]
    rw [h3, card_singleton] at h1
    exact h1
  have hPcard : #X * (#Y - 1) ≤ #P := by
    have : #P = ∑ x ∈ X, #(Y.filter fun y => x ≠ y) := by
      rw [hP, card_eq_sum_ones, sum_filter, sum_product]
      refine sum_congr rfl fun x _ => ?_
      rw [card_eq_sum_ones, sum_filter]
    rw [this, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum hfib
  have hXc := le_card_sdiff B (resK lab R (lab u))
  have hYc := le_card_sdiff B (resK lab R (lab v))
  rw [← hX] at hXc
  rw [← hY] at hYc
  have h1 := hR (lab u)
  have h2 := hR (lab v)
  set N := Fintype.card V
  have hXl : m - 5 ≤ #X := by omega
  have hYl : m - 5 ≤ #Y - 1 := by omega
  have hNat : N * N ≤ M ^ 2 * #(hinges (rHost lab L) cdrF u v a b 6) := by
    have hcard := (card_image_of_injOn hinj).symm.le.trans (card_le_card hsub)
    have e1 : N * N ≤ (M * (m - 5)) * (M * (m - 5)) := Nat.mul_le_mul hN hN
    have e2 : (m - 5) * (m - 5) ≤ #X * (#Y - 1) := Nat.mul_le_mul hXl hYl
    calc N * N ≤ (M * (m - 5)) * (M * (m - 5)) := e1
      _ = M ^ 2 * ((m - 5) * (m - 5)) := by ring
      _ ≤ M ^ 2 * #(hinges (rHost lab L) cdrF u v a b 6) := by
          gcongr; exact e2.trans (hPcard.trans hcard)
  have hMpos : (0 : ℝ) < ((M ^ 2 : ℕ) : ℝ) := by positivity
  have : ((N : ℝ) * N) ≤ ((M ^ 2 : ℕ) : ℝ) * #(hinges (rHost lab L) cdrF u v a b 6) := by
    exact_mod_cast hNat
  rw [show (6 - 4 : ℕ) = 2 from rfl, one_div, inv_mul_le_iff₀ hMpos, pow_two]
  exact this

end CDRBicolour.Absorption.Count.Wilson
