/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.AssemblyBounds

/-!
# Explicit accuracy and order parameters for residual H1
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset
open scoped Classical

theorem trip_card_pos {k : ℕ} (hk : 3 ≤ k) (o : Fin k) : 0 < #(Trip o) := by
  obtain ⟨τ,hsub,-,hc⟩ := exists_subsuperset_card_eq (n := 3) (subset_univ ({o} : Finset (Fin k)))
    (by simp) (by rw [card_univ,Fintype.card_fin]; exact hk)
  exact card_pos.mpr ⟨τ,mem_filter.mpr ⟨mem_univ _,hc,hsub (mem_singleton_self _)⟩⟩

theorem localInverseConstant_pos {k : ℕ} (hk : 3 ≤ k) (o : Fin k) {δ : ℝ} (hδ : 0 < δ) :
    0 < localInverseConstant o (8/δ) := by
  have ht : (0 : ℝ) < #(Trip o) := by exact_mod_cast trip_card_pos hk o
  unfold localInverseConstant
  positivity

def seedAccuracy {k : ℕ} (g : ℕ) (o : Fin k) (δ η : ℝ) : ℝ :=
  min (δ/2) (η*δ/(8*(g : ℝ)*localInverseConstant o (8/δ)*k*((g : ℝ)+1)))

def seedThreshold {k : ℕ} (g : ℕ) (o : Fin k) (δ η : ℝ) : ℕ :=
  ⌈max (2/δ) (max (4*(g : ℝ)*((inverseFloorMinimum δ : ℝ)+1)/δ)
    (64*(g : ℝ)^2*localInverseConstant o (8/δ)/(η*δ)))⌉₊

theorem seedAccuracy_spec {k g : ℕ} (hk : 3 ≤ k) (hg : 1 ≤ g) (o : Fin k)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    0 < seedAccuracy g o δ η ∧ seedAccuracy g o δ η ≤ δ/2 ∧
      8*(g : ℝ)*localInverseConstant o (8/δ)*k*((g : ℝ)+1)*seedAccuracy g o δ η ≤ η*δ := by
  have hG : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hK := localInverseConstant_pos hk o hδ
  have hden : 0 < 8*(g : ℝ)*localInverseConstant o (8/δ)*k*((g : ℝ)+1) := by positivity
  refine ⟨lt_min (by positivity) (by positivity),min_le_left _ _,?_⟩
  have hh := (le_div_iff₀ hden).mp (min_le_right (δ/2)
    (η*δ/(8*(g : ℝ)*localInverseConstant o (8/δ)*k*((g : ℝ)+1))))
  simpa only [seedAccuracy,mul_comm] using hh

theorem seedThreshold_budgets {k g n : ℕ} (hg : 1 ≤ g) (o : Fin k)
    {δ η B : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hn : seedThreshold g o δ η ≤ n) (hB : (n : ℝ) ≤ 2*(g : ℝ)*B) :
    2 ≤ δ*n ∧ 2*((inverseFloorMinimum δ : ℝ)+1) ≤ δ*B ∧
      32*(g : ℝ)*localInverseConstant o (8/δ) ≤ η*δ*B := by
  have hG : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hcast : (seedThreshold g o δ η : ℝ) ≤ n := by exact_mod_cast hn
  have hh : max (2/δ) (max (4*(g : ℝ)*((inverseFloorMinimum δ : ℝ)+1)/δ)
      (64*(g : ℝ)^2*localInverseConstant o (8/δ)/(η*δ))) ≤ n :=
    (Nat.le_ceil _).trans hcast
  have h2 := (div_le_iff₀ hδ).mp ((le_max_left _ _).trans hh)
  have hs := (div_le_iff₀ hδ).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hh))
  have ho := (div_le_iff₀ (mul_pos hη hδ)).mp
    ((le_max_right _ _).trans ((le_max_right _ _).trans hh))
  refine ⟨by nlinarith [h2],?_,?_⟩
  · apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2*g)).mp
    nlinarith [mul_le_mul_of_nonneg_left hB hδ.le,hs]
  · apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2*g)).mp
    nlinarith [mul_le_mul_of_nonneg_left hB (mul_pos hη hδ).le,ho]

theorem reserve_le_group_of_mass {G B r n ρ : ℝ} (hG : 0 < G) (hn : 0 ≤ n)
    (hmass : r+G*B=n) (hcover : (1-ρ)*n ≤ G*B) (hρ : ρ ≤ 1/(G+1)) : r ≤ B := by
  have hρbound : ρ*(G+1) ≤ 1 := (le_div_iff₀ (by linarith : 0 < G+1)).mp hρ
  have hr : r ≤ ρ*n := by nlinarith [hmass,hcover]
  have hbound : (G+1)*r ≤ n := by
    nlinarith [mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ G+1),
      mul_le_mul_of_nonneg_right hρbound hn]
  apply (mul_le_mul_iff_right₀ hG).mp
  nlinarith [hmass,hbound]

end CDRBicolour.KBicolor.Wilson
