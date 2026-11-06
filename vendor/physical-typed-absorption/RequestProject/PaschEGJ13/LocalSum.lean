/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Pseudorandom.Cylinder
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Concentration of weighted sums of local `[0,1]`-valued functions

If `f(τ) = ∑_{s ∈ S} w s · g s τ` where each `g s` takes values in `[0,1]` and only depends on
the coordinates in `B s`, then coordinate `v` changes `f` by at most
`cylGap S w B v = ∑_{s : v ∈ B s} w s`, and the Bernstein-type inequality applies.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {ι σ α : Type*} [Fintype ι] [DecidableEq ι]

theorem local_gap (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s) (B : σ → Finset ι)
    (g : σ → (ι → α) → ℝ) (hg : ∀ s τ, 0 ≤ g s τ ∧ g s τ ≤ 1)
    (hloc : ∀ s τ τ', (∀ v ∈ B s, τ v = τ' v) → g s τ = g s τ') :
    CoordGap (fun τ => ∑ s ∈ S, w s * g s τ) (cylGap S w B) := by
  classical
  intro v τ b b'
  unfold cylGap
  simp only
  rw [← sum_sub_distrib, sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s hs => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw s hs)]
  by_cases hv : v ∈ B s
  · rw [if_pos hv]
    have h1 := hg s (Function.update τ v b)
    have h2 := hg s (Function.update τ v b')
    have : |g s (Function.update τ v b) - g s (Function.update τ v b')| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    exact mul_le_of_le_one_right (hw s hs) this
  · rw [if_neg hv]
    have : g s (Function.update τ v b) = g s (Function.update τ v b') := by
      apply hloc
      intro u hu
      have huv : u ≠ v := fun h => hv (h ▸ hu)
      simp [Function.update_of_ne huv]
    rw [this, sub_self, abs_zero, mul_zero]

variable [Fintype α]

/-- Upper and lower tails for local sums under any product measure. -/
theorem local_tail (P : ι → α → ℝ) (hP : IsPMF P) (S : Finset σ) (w : σ → ℝ)
    (hw : ∀ s ∈ S, 0 ≤ w s) (B : σ → Finset ι)
    (g : σ → (ι → α) → ℝ) (hg : ∀ s τ, 0 ≤ g s τ ∧ g s τ ≤ 1)
    (hloc : ∀ s τ τ', (∀ v ∈ B s, τ v = τ' v) → g s τ = g s τ')
    (L Wt : ℝ) (hL0 : 0 < L) (hL : ∀ v, cylGap S w B v ≤ L)
    (hWt : ∑ s ∈ S, w s * (B s).card ≤ Wt) (t : ℝ) (ht : 0 < t) :
    pProb P (fun τ => t ≤ (∑ s ∈ S, w s * g s τ) - pE P (fun τ => ∑ s ∈ S, w s * g s τ)) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt + L * t)))) ∧
    pProb P (fun τ => t ≤ pE P (fun τ => ∑ s ∈ S, w s * g s τ) - ∑ s ∈ S, w s * g s τ) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt + L * t)))) := by
  classical
  have hgap := local_gap S w hw B g hg hloc
  have hrare : CoordRare (fun τ => ∑ s ∈ S, w s * g s τ) (fun _ => (univ : Finset α)) := by
    intro v τ a b ha
    exact absurd (mem_univ a) ha
  have hq : ∀ v, ∑ a ∈ (univ : Finset α), P v a ≤ 1 := fun v => (hP.2 v).le
  have hc : ∀ v, 0 ≤ cylGap S w B v ∧ cylGap S w B v ≤ L :=
    fun v => ⟨cylGap_nonneg S w hw B v, hL v⟩
  have hvar : ∑ v, (1 : ℝ) * cylGap S w B v ^ 2 ≤ L * Wt := by
    have h1 : ∀ v, (1 : ℝ) * cylGap S w B v ^ 2 ≤ L * cylGap S w B v := by
      intro v
      rw [one_mul, sq]
      exact mul_le_mul_of_nonneg_right (hL v) (cylGap_nonneg S w hw B v)
    calc _ ≤ ∑ v, L * cylGap S w B v := sum_le_sum fun v _ => h1 v
      _ = L * ∑ s ∈ S, w s * (B s).card := by rw [← mul_sum, sum_cylGap]
      _ ≤ L * Wt := mul_le_mul_of_nonneg_left hWt hL0.le
  have hvar0 : 0 ≤ ∑ v, (1 : ℝ) * cylGap S w B v ^ 2 := sum_nonneg fun v _ => by positivity
  have hmono : Real.exp (-(t ^ 2 / (2 * ((∑ v, (1 : ℝ) * cylGap S w B v ^ 2) + L * t)))) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt + L * t)))) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  constructor
  · exact (pE_upper_tail P hP _ _ (fun _ => 1) _ L hL0 hc hgap hrare hq t ht).trans hmono
  · exact (pE_lower_tail P hP _ _ (fun _ => 1) _ L hL0 hc hgap hrare hq t ht).trans hmono

end Pseudorandom
