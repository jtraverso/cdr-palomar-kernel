/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.KernelSeed
public import CDRBicolour.KBicolor.Wilson.FiniteLoads

/-!
# Uniform defect of the actual approximate Wilson seed

The bound uses class discrepancies and the two exact root exclusions. All
weights and constants come from the original reference SeedData.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

theorem classKernel_bounds (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {η δ n : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hs : SeedData c η a)
    (hcls : ∀ i, δ * n ≤ c i) (hsize : ∀ i, (c i : ℝ) ≤ n) (h2 : 2 ≤ δ * n)
    (i j l : Fin k) :
    0 ≤ classKernel c a i j l ∧ |classKernel c a i j l| ≤ 2 / (δ * n) := by
  rw [← classKernel_eq]
  split_ifs with hf
  · obtain ⟨hl, hu⟩ := seedW_sharp_bounds c a hη hδ hn hs hcls hsize h2 hf
    have hp := (div_nonneg hη.le hn.le).trans hl
    exact ⟨hp, by rwa [abs_of_nonneg hp]⟩
  · exact ⟨le_rfl, by simpa only [abs_zero] using (show (0 : ℝ) ≤ 2/(δ*n) by positivity)⟩

def localDefectBound (k : ℕ) (C EG ER x : ℝ) : ℝ :=
  ((k : ℝ) * (EG + ER) * C + 4 * C) / x

def reserveTarget (R : Finset V) (g : ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun u v => if u ∈ R ∧ v ∈ R then 1 / g else 1,
    fun u v => by simp only [and_comm]⟩ e

theorem reserveTarget_eq (R : Finset V) (g : ℝ) (u v : V) :
    reserveTarget R g s(u,v) =
      targetLoad g ((if u ∈ R then 1 else 0) + (if v ∈ R then 1 else 0)) := by
  by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;>
    simp [reserveTarget, targetLoad, hu, hv]

theorem approximateLocalSeed_defect (lab : V → Fin k) (R : Finset V)
    (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {g x y η δ n EG ER : ℝ}
    (hg : 1 ≤ g) (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hs : SeedData c η a)
    (hcls : ∀ i, δ * n ≤ c i) (hsize : ∀ i, (c i : ℝ) ≤ n) (h2 : 2 ≤ δ * n)
    (hEG : 0 ≤ EG) (hER : 0 ≤ ER)
    (hG : ∀ l, |(#((univ \ R).filter fun z => lab z = l) : ℝ) - x * c l| ≤ EG)
    (hR : ∀ l, |(#(R.filter fun z => lab z = l) : ℝ) - y * c l| ≤ ER) :
    ‖(fun e : E0 V => reserveTarget R g e.1) -
      MincG lab (bicF k) (approximateLocalSeed lab R c a g x y)‖ ≤
        localDefectBound k (2 / (δ * n)) EG ER x := by
  have hC : 0 ≤ 2 / (δ * n) := by positivity
  have hb : 0 ≤ localDefectBound k (2 / (δ * n)) EG ER x := by
    unfold localDefectBound
    positivity
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro e
  obtain ⟨u,v,he⟩ : ∃ u v, s(u,v) = e.1 := by
    induction e.1 using Sym2.ind with
    | _ u v => exact ⟨u,v,rfl⟩
  have huv : u ≠ v := by
    intro h
    exact e.2 (by rw [← he, h]; exact Sym2.mk_isDiag_iff.mpr rfl)
  let w : Fin k → ℝ := classKernel c a (lab u) (lab v)
  have href := classKernel_mass c a hs (fun i => by linarith [hcls i]) (lab u) (lab v)
  have hw : ∀ l, |w l| ≤ 2 / (δ * n) := fun l =>
    (classKernel_bounds c a hη hδ hn hs hcls hsize h2 (lab u) (lab v) l).2
  have hG' := finite_rooted_mass_error lab (univ \ R) (fun i => (c i : ℝ)) w huv
    hx.le hx1 hEG hC hG hw href
  have hR' := finite_rooted_mass_error lab R (fun i => (c i : ℝ)) w huv
    hy (hyx.trans hx1) hER hC hR hw href
  let j : ℕ := (if u ∈ R then 1 else 0) + (if v ∈ R then 1 else 0)
  have hj : j ≤ 2 := by unfold j; split_ifs <;> omega
  have herr := optimal_load_error hg hx hy hyx
    (by positivity : 0 ≤ (k : ℝ) * EG * (2 / (δ * n)) + 2 * (2 / (δ * n)))
    (by positivity : 0 ≤ (k : ℝ) * ER * (2 / (δ * n)) + 2 * (2 / (δ * n)))
    hG' hR' j hj
  rw [Real.norm_eq_abs, Pi.sub_apply]
  change |reserveTarget R g e.1 - MincG lab (bicF k) _ e| ≤ _
  change |reserveTarget R g e.1 -
    (∑ T ∈ (triG lab (bicF k)).filter (fun T => e.1 ∈ triEdges T),
      approximateLocalSeed lab R c a g x y T)| ≤ _
  rw [← he, reserveTarget_eq, approximateLocalSeed_edge_sum lab R c a g x y huv, abs_sub_comm]
  have hid : ((k : ℝ) * EG * (2 / (δ * n)) + 2 * (2 / (δ * n)) +
      ((k : ℝ) * ER * (2 / (δ * n)) + 2 * (2 / (δ * n)))) / x =
      localDefectBound k (2 / (δ * n)) EG ER x := by unfold localDefectBound; ring
  rw [mul_comm (optimalWeight g x y j), mul_comm (optimalWeight g x y (j+1))]
  exact herr.trans_eq hid

end CDRBicolour.KBicolor.Wilson
