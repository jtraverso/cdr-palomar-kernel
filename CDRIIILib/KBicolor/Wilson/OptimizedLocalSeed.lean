/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.LocalCompatibility

/-!
# Exact local Wilson seed using the optimized weights

The reference seed, class discrepancies and exact pair balance give a diffuse
seed for the target loads 1 and 1/g. The bounded inverse is the existing k-colour
inverse. This is local exactification; global transport and assembly are separate.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

theorem approximateLocalSeed_local_bounds (lab : V → Fin k) (R : Finset V)
    (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {g x y η δ n : ℝ}
    (hg : 1 ≤ g) (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hs : SeedData c η a)
    (hcls : ∀ i, δ * n ≤ c i) (hsize : ∀ i, (c i : ℝ) ≤ n) (h2 : 2 ≤ δ * n)
    (hN : (Fintype.card V : ℝ) = (x+y)*n)
    {T : Finset V} (hT : T ∈ triG lab (bicF k)) :
    (η/g) / Fintype.card V ≤ approximateLocalSeed lab R c a g x y T ∧
      approximateLocalSeed lab R c a g x y T ≤ (4/δ) / Fintype.card V := by
  obtain ⟨hl, hu⟩ := approximateLocalSeed_bounds lab R c a hg hx hy hyx hη hδ hn hs hcls hsize h2 hT
  have hg0 : 0 < g := by linarith
  have hxy : 0 < x+y := by linarith
  have hNV : (0 : ℝ) < Fintype.card V := by rw [hN]; positivity
  constructor
  · have hid : (η/g) / Fintype.card V = optimalFloor g x y * η / n := by
      rw [hN]
      unfold optimalFloor
      field_simp
      <;> ring
    rwa [hid]
  · refine hu.trans ?_
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < δ*n*x) (by positivity : 0 < δ*(Fintype.card V : ℝ))).mpr
    rw [hN]
    nlinarith [mul_nonneg (mul_pos hδ hn).le (sub_nonneg.mpr hyx)]

theorem optimized_local_seed (lab : V → Fin k) (R : Finset V)
    (c : Fin k → ℕ) (a : Fin k → Fin k → ℝ) {g x y η δ n EG ER K : ℝ}
    (hg : 1 ≤ g) (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hs : SeedData c η a)
    (hcls : ∀ i, δ*n ≤ c i) (hsize : ∀ i, (c i : ℝ) ≤ n) (h2 : 2 ≤ δ*n)
    (hEG : 0 ≤ EG) (hER : 0 ≤ ER)
    (hG : ∀ l, |(#((univ \ R).filter fun z => lab z = l) : ℝ) - x*c l| ≤ EG)
    (hR : ∀ l, |(#(R.filter fun z => lab z = l) : ℝ) - y*c l| ≤ ER)
    (hN : (Fintype.card V : ℝ) = (x+y)*n)
    (hbalance : g * profileDefect
      ((fun i => (#((univ \ R).filter fun v => lab v = i) : ℝ)) +
       (fun i => (#(R.filter fun v => lab v = i) : ℝ))) =
      (g-1) * profileDefect (fun i => (#(R.filter fun v => lab v = i) : ℝ)))
    (B : BRIG lab (bicF k) (wlk lab) K) (hK : 0 ≤ K)
    (hsmall : K * localDefectBound k (2/(δ*n)) EG ER x ≤ η/(2*g)) :
    ∃ φ : Finset V → ℝ,
      MincG lab (bicF k) φ = (fun e : E0 V => reserveTarget R g e.1) ∧
      ∀ T ∈ triG lab (bicF k), η/(2*g*Fintype.card V) ≤ φ T ∧
        φ T ≤ (4/δ + η/(2*g)) / Fintype.card V := by
  have hg0 : 0 < g := by linarith
  have hNV : (0 : ℝ) < Fintype.card V := by rw [hN]; positivity
  have hNVnat : 0 < Fintype.card V := by exact_mod_cast hNV
  have hε : 0 ≤ localDefectBound k (2/(δ*n)) EG ER x := by
    unfold localDefectBound
    positivity
  have hsmall' : K * localDefectBound k (2/(δ*n)) EG ER x ≤ (η/g)/2 := by
    simpa only [div_div, mul_comm g 2] using hsmall
  obtain ⟨φ, heq, hb⟩ := exactify_local_seed lab B hNVnat hK hε hsmall'
    (approximateLocalSeed lab R c a g x y) (fun e : E0 V => reserveTarget R g e.1)
    (local_target_compatible lab R hg0 hbalance)
    (fun T hT => approximateLocalSeed_local_bounds lab R c a hg hx hy hyx hη hδ hn hs hcls hsize h2 hN hT)
    (approximateLocalSeed_defect lab R c a hg hx hx1 hy hyx hη hδ hn hs hcls hsize h2 hEG hER hG hR)
  refine ⟨φ, heq, fun T hT => ?_⟩
  obtain ⟨hl, hu⟩ := hb T hT
  constructor
  · convert hl using 1 <;> ring
  · convert hu using 1 <;> ring

def normalizedDefectBudget (k : ℕ) (g δ ξ n x : ℝ) : ℝ :=
  2 * k * (g+1) * ξ / δ + 8 / (δ*n*x)

theorem localDefectBound_scaled (k : ℕ) {g δ ξ n x : ℝ}
    (hδ : 0 < δ) (hn : 0 < n) (hx : 0 < x) :
    localDefectBound k (2/(δ*n)) (x*n*ξ) (g*x*n*ξ) x =
      normalizedDefectBudget k g δ ξ n x := by
  unfold localDefectBound normalizedDefectBudget
  field_simp
  <;> ring

/-- Explicit sufficient input budgets for the local correction. -/
theorem explicit_local_correction_budget {k : ℕ} {g δ η ξ n x K : ℝ}
    (hg : 0 < g) (hδ : 0 < δ) (hn : 0 < n) (hx : 0 < x)
    (hξ : 8*g*K*k*(g+1)*ξ ≤ η*δ)
    (horder : 32*g*K ≤ η*δ*n*x) :
    K * normalizedDefectBudget k g δ ξ n x ≤ η/(2*g) := by
  have h1 : K * (2*k*(g+1)*ξ/δ) ≤ η/(4*g) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hδ (by positivity : 0 < 4*g)).mpr
    nlinarith [hξ]
  have h2 : K * (8/(δ*n*x)) ≤ η/(4*g) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < δ*n*x) (by positivity : 0 < 4*g)).mpr
    nlinarith [horder]
  unfold normalizedDefectBudget
  rw [mul_add]
  have hid : η/(4*g)+η/(4*g) = η/(2*g) := by ring
  linarith

end CDRBicolour.KBicolor.Wilson
