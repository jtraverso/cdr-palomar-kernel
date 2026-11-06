/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.BRIAverage

/-!
# The uniform solver

A type-uniform edge function is given by a symmetric `G : Fin 3 → Fin 3 → ℝ` (value on edges
whose ends have labels `X, Y`).  With class sizes `a, b, c` (all `≥ 2`), the type-uniform
triangle weights of the chain solution

  `x_AAB = G₀₀/b`, `x_AAC = 0`, `x_ACC = G₀₂/(c-1)`, `x_ABB = (G₀₁ - (a-1) x_AAB)/(b-1)`,
  `x_BCC = (G₂₂ - a x_ACC)/b`, `x_BBC = (G₁₁ - a x_ABB)/c`

satisfy five of the six edge equations identically and the sixth (`BC`) up to `-ℓ(G)/(bc)`,
where `ℓ(G) = -2 ∑_X C(|X|,2) G_XX + ∑_{X<Y} |X||Y| G_XY` (`chain_BC`).  Hence, when
`ℓ(G) = 0`, the uniform weights cover `G` exactly (`Minc_uniform`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Chain

variable (a b c : ℝ) (G : Fin 3 → Fin 3 → ℝ)

def xAAB : ℝ := G 0 0 / b
def xAAC : ℝ := 0
def xACC : ℝ := G 0 2 / (c - 1)
def xABB : ℝ := (G 0 1 - (a - 1) * xAAB b G) / (b - 1)
def xBCC : ℝ := (G 2 2 - a * xACC c G) / b
def xBBC : ℝ := (G 1 1 - a * xABB a b G) / c

/-- The functional `ℓ` on type values. -/
def ellG : ℝ := -2 * (a * (a - 1) / 2 * G 0 0 + b * (b - 1) / 2 * G 1 1 + c * (c - 1) / 2 * G 2 2) +
  a * b * G 0 1 + a * c * G 0 2 + b * c * G 1 2

variable {a b c} (hb : b ≠ 0) (hc : c ≠ 0) (hb1 : b - 1 ≠ 0) (hc1 : c - 1 ≠ 0)
include hb hc hb1 hc1

theorem chain_AA : b * xAAB b G + c * xAAC = G 0 0 := by
  simp only [xAAB, xAAC]; field_simp; ring
theorem chain_BB : a * xABB a b G + c * xBBC a b c G = G 1 1 := by
  simp only [xBBC]; field_simp; ring
theorem chain_CC : a * xACC c G + b * xBCC a b c G = G 2 2 := by
  simp only [xBCC]; field_simp; ring
theorem chain_AB : (a - 1) * xAAB b G + (b - 1) * xABB a b G = G 0 1 := by
  simp only [xABB]; field_simp; ring
theorem chain_AC : (a - 1) * xAAC + (c - 1) * xACC c G = G 0 2 := by
  simp only [xAAC, xACC]; field_simp; ring
theorem chain_BC (hℓ : ellG a b c G = 0) :
    (b - 1) * xBBC a b c G + (c - 1) * xBCC a b c G = G 1 2 := by
  have : (b - 1) * xBBC a b c G + (c - 1) * xBCC a b c G - G 1 2 = -ellG a b c G / (b * c) := by
    simp only [xBBC, xBCC, xABB, xACC, xAAB, ellG]; field_simp; ring
  rw [hℓ, neg_zero, zero_div, sub_eq_zero] at this
  exact this

end Chain

section Solver

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

variable (lab) in
/-- The uniform triangle weight of a type, with the class sizes of `lab`. -/
def xU (G : Fin 3 → Fin 3 → ℝ) (m : Multiset (Fin 3)) : ℝ :=
  let a : ℝ := csz lab 0
  let b : ℝ := csz lab 1
  let c : ℝ := csz lab 2
  if m.count 0 = 2 ∧ m.count 1 = 1 then xAAB b G
  else if m.count 0 = 2 ∧ m.count 2 = 1 then xAAC
  else if m.count 1 = 2 ∧ m.count 2 = 1 then xBBC a b c G
  else if m.count 1 = 2 ∧ m.count 0 = 1 then xABB a b G
  else if m.count 2 = 2 ∧ m.count 0 = 1 then xACC c G
  else if m.count 2 = 2 ∧ m.count 1 = 1 then xBCC a b c G
  else 0

variable (lab) in
/-- The uniform solver as a triangle weight. -/
def phiU (G : Fin 3 → Fin 3 → ℝ) : Finset V → ℝ := fun T => xU lab G (T.val.map lab)

/-- **The uniform solver covers a symmetric `G` with `ℓ(G) = 0`.** -/
theorem Minc_uniform (hcls : ∀ k, 3 ≤ csz lab k) (G : Fin 3 → Fin 3 → ℝ)
    (hsym : ∀ X Y, G X Y = G Y X)
    (hℓ : ellG (csz lab 0) (csz lab 1) (csz lab 2) G = 0) (f : E0 V) :
    Minc lab (phiU lab G) f = G (lab (rep f).1) (lab (rep f).2) := by
  classical
  have h0 : (3 : ℝ) ≤ csz lab 0 := by exact_mod_cast hcls 0
  have h1 : (3 : ℝ) ≤ csz lab 1 := by exact_mod_cast hcls 1
  have h2 : (3 : ℝ) ≤ csz lab 2 := by exact_mod_cast hcls 2
  have hb0 : (csz lab 1 : ℝ) ≠ 0 := by linarith
  have hc0 : (csz lab 2 : ℝ) ≠ 0 := by linarith
  have hb1 : (csz lab 1 : ℝ) - 1 ≠ 0 := by linarith
  have hc1 : (csz lab 2 : ℝ) - 1 ≠ 0 := by linarith
  have cAA := chain_AA G hb0 hc0 hb1 hc1
  have cBB := chain_BB (a := (csz lab 0 : ℝ)) G hb0 hc0 hb1 hc1
  have cCC := chain_CC (a := (csz lab 0 : ℝ)) G hb0 hc0 hb1 hc1
  have cAB := chain_AB (a := (csz lab 0 : ℝ)) G hb0 hc0 hb1 hc1
  have cAC := chain_AC (a := (csz lab 0 : ℝ)) G hb0 hc0 hb1 hc1
  have cBC := chain_BC G hb0 hc0 hb1 hc1 hℓ
  set u := (rep f).1 with hu
  set v := (rep f).2 with hv
  have huv : u ≠ v := rep_ne f
  have hf : f.1 = s(u, v) := (rep_spec f).symm
  simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk, phiU]
  rw [hf, edge_sum_top' lab cdrF (xU lab G) huv _ ?hS]
  case hS =>
    intro T
    convert (mem_filter (s := allowed (⟨⊤, lab⟩ : Host V (Fin 3)) cdrF)
      (p := fun T => s(u, v) ∈ triEdges T) (a := T))
  rw [sum_by_label lab (fun k => ({lab u, lab v, k} : Multiset (Fin 3)) ∈ cdrF)
    (fun k => xU lab G {lab u, lab v, k})]
  simp only [card_third lab huv, Fin.sum_univ_three]
  have hcz : ∀ k : Fin 3, ((univ.filter fun z => lab z = k).card : ℝ) = (csz lab k : ℝ) :=
    fun _ => rfl
  simp only [hcz]
  generalize lab u = i
  generalize lab v = j
  have s01 := hsym 0 1
  have s02 := hsym 0 2
  have s12 := hsym 1 2
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [cdrF, xU] <;> linarith

end Solver

end CDRBicolour.Absorption
