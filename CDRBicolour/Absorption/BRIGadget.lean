/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.ResidualSeed

/-!
# The K₄ gadget

For distinct `u, v, w, z` whose four triangles are allowed,
`gad u v w z = 1_{uvw} + 1_{uvz} - 1_{uwz} - 1_{vwz}` covers `2·1_{uv} - 2·1_{wz}`
(`Minc_gad`).  Averaging these gadgets is the first step of the bounded right inverse.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Gadget

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

/-- Indicator of one triangle. -/
def indT (S : Finset V) : Finset V → ℝ := fun T => if T = S then 1 else 0

theorem Minc_indT {S : Finset V} (hS : S ∈ tri lab) (e : E0 V) :
    Minc lab (indT S) e = if e.1 ∈ triEdges S then 1 else 0 := by
  simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk, indT]
  rw [sum_ite_eq' ((tri lab).filter fun T => e.1 ∈ triEdges T) S (fun _ => (1 : ℝ))]
  simp only [mem_filter, hS, true_and]

/-- The K₄ gadget. -/
def gad (u v w z : V) : Finset V → ℝ :=
  indT {u, v, w} + indT {u, v, z} - indT {u, w, z} - indT {v, w, z}

theorem Minc_gad {u v w z : V} (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w)
    (hvz : v ≠ z) (hwz : w ≠ z) (h1 : ({u, v, w} : Finset V) ∈ tri lab)
    (h2 : ({u, v, z} : Finset V) ∈ tri lab) (h3 : ({u, w, z} : Finset V) ∈ tri lab)
    (h4 : ({v, w, z} : Finset V) ∈ tri lab) (e : E0 V) :
    Minc lab (gad u v w z) e =
      2 * (if e.1 = s(u, v) then 1 else 0) - 2 * (if e.1 = s(w, z) then 1 else 0) := by
  simp only [gad, map_sub, map_add, Pi.sub_apply, Pi.add_apply]
  rw [Minc_indT h1, Minc_indT h2, Minc_indT h3, Minc_indT h4,
    triEdges_triple huv huw hvw, triEdges_triple huv huz hvz, triEdges_triple huw huz hwz,
    triEdges_triple hvw hvz hwz]
  obtain ⟨f, hf⟩ := e
  simp only [mem_insert, mem_singleton]
  have hvu := huv.symm; have hwu := huw.symm; have hzu := huz.symm
  have hwv := hvw.symm; have hzv := hvz.symm; have hzw := hwz.symm
  have n1 : s(u, v) ≠ s(u, w) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n2 : s(u, v) ≠ s(v, w) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n3 : s(u, v) ≠ s(u, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n4 : s(u, v) ≠ s(v, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n5 : s(u, v) ≠ s(w, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n6 : s(u, w) ≠ s(v, w) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n7 : s(u, w) ≠ s(u, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n8 : s(u, w) ≠ s(v, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n9 : s(u, w) ≠ s(w, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n10 : s(v, w) ≠ s(u, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n11 : s(v, w) ≠ s(v, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n12 : s(v, w) ≠ s(w, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n13 : s(u, z) ≠ s(v, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n14 : s(u, z) ≠ s(w, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  have n15 : s(v, z) ≠ s(w, z) := by simp only [ne_eq, Sym2.eq_iff]; tauto
  by_cases e1 : f = s(u, v)
  · subst e1; simp [n1, n2, n3, n4, n5]; norm_num
  by_cases e2 : f = s(u, w)
  · subst e2; simp [n1.symm, n6, n7, n8, n9]
  by_cases e3 : f = s(v, w)
  · subst e3; simp [n2.symm, n6.symm, n10, n11, n12]
  by_cases e4 : f = s(u, z)
  · subst e4; simp [n3.symm, n7.symm, n10.symm, n13, n14]
  by_cases e5 : f = s(v, z)
  · subst e5; simp [n4.symm, n8.symm, n11.symm, n13.symm, n15]
  by_cases e6 : f = s(w, z)
  · subst e6; simp [n5.symm, n9.symm, n12.symm, n14.symm, n15.symm]; norm_num
  simp [e1, e2, e3, e4, e5, e6]

end Gadget

end CDRBicolour.Absorption
