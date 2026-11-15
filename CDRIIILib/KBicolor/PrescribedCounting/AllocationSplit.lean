/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.Pattern.Split

/-! # Exact splitting preserves every zero of an allocation matrix -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.Hilton
open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

theorem decompose_with_support (h : ℕ) (M : I → J → ℕ) (a : I → ℕ) (b : J → ℕ)
    (hr : ∀ i, ∑ j, M i j = h*a i) (hc : ∀ j, ∑ i, M i j = h*b j) :
    ∃ F : Fin h → I → J → ℕ,
      (∀ t i, ∑ j, F t i j = a i) ∧ (∀ t j, ∑ i, F t i j = b j) ∧
      (∀ i j, ∑ t, F t i j = M i j) ∧
      (∀ t i j, F t i j ≤ M i j) ∧
      (∀ t i j, M i j = 0 → F t i j = 0) := by
  obtain ⟨F,hFr,hFc,hFs⟩ := decompose h M a b hr hc
  have hle : ∀ t i j, F t i j ≤ M i j := by
    intro t i j
    rw [← hFs i j]
    exact single_le_sum (f:=fun u => F u i j) (fun _ _ => Nat.zero_le _) (mem_univ t)
  exact ⟨F,hFr,hFc,hFs,hle,fun t i j hz => Nat.eq_zero_of_le_zero (hz ▸ hle t i j)⟩

end CDRBicolour.KBicolor.Hilton
