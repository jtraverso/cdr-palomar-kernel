/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.IncidenceImage
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

open Finset Classical

noncomputable section

namespace TypedTriangle.Incidence

variable {V : Type*} [Fintype V]

/-- An integral double delta obstructs a two-colouring on its closed component.
This keeps the integral obstruction; it does not pass to a rational saturation. -/
theorem double_delta_forbids_coloring (J : SimpleGraph V) (K : Finset V) (u : V)
    (hu : u ∈ K)
    (hclosed : ∀ a b, J.Adj a b → (a ∈ K ↔ b ∈ K))
    (hmem : (2 : ℤ) • dlt u ∈ incLattice J) :
    ¬ ∃ col : V → Bool, ∀ a ∈ K, ∀ b ∈ K, J.Adj a b → col a ≠ col b := by
  rintro ⟨col, hcol⟩
  let σ : V → ℤ := fun a => if a ∈ K then (if col a then 1 else -1) else 0
  have hadm : ∀ a b, J.Adj a b → σ a + σ b = 0 := by
    intro a b hab
    by_cases ha : a ∈ K
    · have hb : b ∈ K := (hclosed a b hab).mp ha
      have hne := hcol a ha b hb hab
      simp only [σ, if_pos ha, if_pos hb]
      cases hca : col a <;> cases hcb : col b <;> simp_all
    · have hb : b ∉ K := fun hb => ha ((hclosed a b hab).mpr hb)
      simp [σ, ha, hb]
  have hzero := (incLattice_necessary hmem).1 σ hadm
  have hsum : ∑ a, σ a * ((2 : ℤ) • dlt u) a = 2 * σ u := by
    rw [Finset.sum_eq_single u]
    · simp [dlt, mul_comm]
    · intro a _ hau
      simp [dlt, hau]
    · intro hn
      exact (hn (Finset.mem_univ u)).elim
  rw [hsum] at hzero
  have hsu : σ u = 1 ∨ σ u = -1 := by
    simp only [σ, if_pos hu]
    cases col u <;> simp
  rcases hsu with hsu | hsu <;> rw [hsu] at hzero <;> norm_num at hzero

end TypedTriangle.Incidence
