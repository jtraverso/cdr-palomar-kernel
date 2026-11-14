/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.RootedLoads

/-!
# From actual vertex sums to the class-kernel discrepancy bound

Both root contributions are removed exactly, including when the roots have
the same colour. No divisibility or decomposition hypothesis is used here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

theorem sum_erase_one (B : Finset V) (f : V → ℝ) (u : V) :
    (∑ z ∈ B.erase u, f z) = (∑ z ∈ B, f z) - if u ∈ B then f u else 0 := by
  by_cases hu : u ∈ B
  · rw [ite_eq_left hu, sum_erase_eq_sub hu]
  · simp [hu, erase_eq_of_notMem hu]

theorem sum_erase_two (B : Finset V) (f : V → ℝ) {u v : V} (huv : u ≠ v) :
    (∑ z ∈ (B.erase u).erase v, f z) = (∑ z ∈ B, f z) -
      (if u ∈ B then f u else 0) - (if v ∈ B then f v else 0) := by
  rw [sum_erase_one, sum_erase_one]
  simp [mem_erase, Ne.symm huv]

theorem sum_label_kernel (lab : V → Fin k) (B : Finset V) (w : Fin k → ℝ) :
    (∑ z ∈ B, w (lab z)) = ∑ l, (#(B.filter fun z => lab z = l) : ℝ) * w l := by
  classical
  rw [← sum_fiberwise_of_maps_to (t := univ) (g := lab) (fun _ _ => mem_univ _) (fun z => w (lab z))]
  apply sum_congr rfl
  intro l _
  calc
    (∑ z ∈ B.filter (fun z => lab z = l), w (lab z)) =
        ∑ _z ∈ B.filter (fun z => lab z = l), w l :=
      sum_congr rfl fun z hz => by rw [(mem_filter.mp hz).2]
    _ = _ := by simp

theorem sum_thirds_eq_rootedMass (lab : V → Fin k) (B : Finset V) (w : Fin k → ℝ)
    {u v : V} (huv : u ≠ v) :
    (∑ z ∈ (B.erase u).erase v, w (lab z)) =
      rootedMass (fun l => (#(B.filter fun z => lab z = l) : ℝ)) w (lab u) (lab v)
        (if u ∈ B then 1 else 0) (if v ∈ B then 1 else 0) := by
  rw [sum_erase_two B _ huv, sum_label_kernel]
  unfold rootedMass
  by_cases hu : u ∈ B <;> by_cases hv : v ∈ B <;> simp [hu, hv]

theorem finite_rooted_mass_error (lab : V → Fin k) (B : Finset V)
    (c w : Fin k → ℝ) {u v : V} (huv : u ≠ v) {s E C : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hz : ∀ l, |(#(B.filter fun z => lab z = l) : ℝ) - s * c l| ≤ E)
    (hw : ∀ l, |w l| ≤ C)
    (href : (∑ l, c l * w l) - w (lab u) - w (lab v) = 1) :
    |(∑ z ∈ (B.erase u).erase v, w (lab z)) - s| ≤ (k : ℝ) * E * C + 2 * C := by
  rw [sum_thirds_eq_rootedMass lab B w huv]
  apply rooted_mass_error _ c w (lab u) (lab v) hs0 hs1 hE hC _ _ hz hw href
  all_goals split_ifs <;> norm_num

end CDRBicolour.KBicolor.Wilson
