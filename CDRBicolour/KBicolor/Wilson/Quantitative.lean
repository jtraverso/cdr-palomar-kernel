/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.Assembly
public import CDRBicolour.KBicolor.Wilson.NearFull

/-!
# The sharp coefficient from Wilson coverage and a residual decomposition

The algebraic loss is at most four factors `1-ρ`: one from the number of group
pairs, two from the covered points, and one from the logarithm of the free Latin
order. No additional loss arises from the number or size of the pattern slots.
The endpoint explicitly retains the residual decomposition as a hypothesis.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle
open CDRBicolour.Absorption.Count.Wilson (OT tri3 mem_OT exists_sorted)

variable {g : ℕ} {S : Finset (Finset (Fin g))}

theorem card_blocks_le_OT (hS : _root_.STS.IsSTS S) : #S ≤ #(OT S) := by
  refine le_trans (card_le_card ?_) (card_image_le (s := OT S) (f := tri3))
  intro B hB
  obtain ⟨x, y, z, h1, h2, h3, rfl⟩ := card_eq_three.mp (hS.1 B hB)
  obtain ⟨o, ho1, ho2, hoB⟩ := exists_sorted h1 h2 h3
  exact mem_image.mpr ⟨o, mem_OT.mpr ⟨ho1, ho2, hoB ▸ hB⟩, hoB⟩

theorem group_pairs_le_OT (hS : _root_.STS.IsSTS S) :
    g * (g - 1) ≤ 6 * #(OT S) := by
  classical
  have hsub : (univ : Finset (Fin g)).offDiag ⊆ S.biUnion (fun B => B.offDiag) := by
    intro p hp
    rw [mem_offDiag] at hp
    obtain ⟨B, ⟨hB, h1, h2⟩, -⟩ := hS.2 _ _ hp.2.2
    exact mem_biUnion.mpr ⟨B, hB, mem_offDiag.mpr ⟨h1, h2, hp.2.2⟩⟩
  have h1 := card_le_card hsub
  rw [offDiag_card, card_univ, Fintype.card_fin] at h1
  have h2 : #(S.biUnion fun B => B.offDiag) ≤ ∑ B ∈ S, #B.offDiag := card_biUnion_le
  have h3 : ∑ B ∈ S, #B.offDiag = 6 * #S := by
    rw [sum_congr rfl (fun B hB => by rw [offDiag_card, hS.1 B hB]),
      sum_const, smul_eq_mul]
    ring
  have h4 := card_blocks_le_OT hS
  rw [← Nat.mul_sub_one] at h1
  omega

/-- Quantitative entropy calculation, independent of the pattern construction. -/
theorem entropy_ineq {ε ρ G B N T O L : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρε : ρ ≤ ε)
    (hG : 0 ≤ G) (_hB : 0 ≤ B) (hN : 0 ≤ N) (_hT : 0 ≤ T) (hO : 0 ≤ O)
    (hL : 0 ≤ L) (hρG : 1 ≤ ρ * G) (hpairs : G * (G - 1) ≤ 6 * O)
    (hcover : (1 - ρ) * N ≤ G * B * T)
    (hlog : (1 - ρ) * L ≤ Real.log T - 2) :
    (1 / 6 - ε) * N ^ 2 * L ≤ O * B ^ 2 * T ^ 2 * (Real.log T - 2) := by
  have h1ρ : 0 ≤ 1 - ρ := by linarith
  have hgroup : (1 - ρ) * G ^ 2 ≤ G * (G - 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hρG hG]
  have hpoint : ((1 - ρ) * N) ^ 2 ≤ (G * B * T) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h1ρ hN) hcover 2
  have hcoef : (1 - ρ) ^ 3 * N ^ 2 ≤ 6 * (O * B ^ 2 * T ^ 2) := calc
    _ = (1 - ρ) * ((1 - ρ) * N) ^ 2 := by ring
    _ ≤ (1 - ρ) * (G * B * T) ^ 2 := mul_le_mul_of_nonneg_left hpoint h1ρ
    _ = ((1 - ρ) * G ^ 2) * (B ^ 2 * T ^ 2) := by ring
    _ ≤ (G * (G - 1)) * (B ^ 2 * T ^ 2) :=
      mul_le_mul_of_nonneg_right hgroup (by positivity)
    _ ≤ (6 * O) * (B ^ 2 * T ^ 2) :=
      mul_le_mul_of_nonneg_right hpairs (by positivity)
    _ = _ := by ring
  have hBern : 1 / 6 - ε ≤ 1 / 6 * (1 - ρ) ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg ρ) (sq_nonneg (ρ - 2))]
  have hcoef' : 1 / 6 * (1 - ρ) ^ 3 * N ^ 2 ≤ O * B ^ 2 * T ^ 2 := by linarith
  calc
    _ ≤ (1 / 6 * (1 - ρ) ^ 4) * N ^ 2 * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBern (sq_nonneg N)) hL
    _ = (1 / 6 * (1 - ρ) ^ 3 * N ^ 2) * ((1 - ρ) * L) := by ring
    _ ≤ (O * B ^ 2 * T ^ 2) * (Real.log T - 2) :=
      mul_le_mul hcoef' hlog (mul_nonneg h1ρ hL) (by positivity)
    _ = _ := by ring

/-- A uniform linear lower bound on the Latin order gives the logarithmic estimate. -/
theorem log_order_control {ρ C n t : ℝ} (hρ : 0 < ρ) (hC : 0 < C) (hn : 0 < n)
    (ht : n / C ≤ t) (hlarge : Real.exp ((Real.log C + 2) / ρ) ≤ n) :
    (1 - ρ) * Real.log n ≤ Real.log t - 2 := by
  have hlog := Real.log_le_log (div_pos hn hC) ht
  rw [Real.log_div hn.ne' hC.ne'] at hlog
  have hthreshold : (Real.log C + 2) / ρ ≤ Real.log n :=
    (Real.le_log_iff_exp_le hn).mpr hlarge
  have hscaled := (div_le_iff₀ hρ).mp hthreshold
  nlinarith

variable {A : Type*} [Fintype A] [DecidableEq A] {k n t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

/-- Sharp counting from the coverage estimates and a decomposition of the common residual. -/
theorem sharp_lower_of_residual (h : Setup lab κ g t) (hS : _root_.STS.IsSTS S)
    (Λ₀ : LFam A S t) {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρε : ρ ≤ ε)
    (hg : 1 ≤ g) (hρg : 1 ≤ ρ * g) (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hcover : (1 - ρ) * n ≤ (g : ℝ) * Fintype.card A * t)
    (hlog : (1 - ρ) * Real.log n ≤ Real.log t - 2)
    {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (rHostK lab ((crossP h Λ₀).biUnion triEdges)) (bicF k)
      (edges (rHostK lab ((crossP h Λ₀).biUnion triEdges))) D) :
    (1 / 6 - ε) * (n : ℝ) ^ 2 * Real.log n ≤ Real.log (kCount lab) := by
  have hpairN := group_pairs_le_OT hS
  have hpair : (g : ℝ) * (g - 1) ≤ 6 * #(OT S) := by
    have hcast : (g : ℝ) * ((g - 1 : ℕ) : ℝ) ≤ 6 * #(OT S) := by exact_mod_cast hpairN
    simpa only [Nat.cast_sub hg, Nat.cast_one] using hcast
  have hcalc := entropy_ineq hρ hρ1 hρε (Nat.cast_nonneg g)
    (Nat.cast_nonneg (Fintype.card A)) (Nat.cast_nonneg n) (Nat.cast_nonneg t)
    (Nat.cast_nonneg #(OT S)) (Real.log_nonneg (by exact_mod_cast hn)) hρg hpair hcover hlog
  have hcount := log_kCount_ge h hS Λ₀ ht hD
  have hrewrite :
      ((Fintype.card A ^ 2 * #(OT S) : ℕ) : ℝ) * (t : ℝ) ^ 2 * (Real.log t - 2) =
        (#(OT S) : ℝ) * (Fintype.card A : ℝ) ^ 2 * t ^ 2 * (Real.log t - 2) := by
    push_cast
    ring
  rw [hrewrite] at hcount
  exact hcalc.trans hcount

end CDRBicolour.KBicolor.Wilson
