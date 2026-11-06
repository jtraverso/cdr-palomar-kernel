/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicPreparation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.Vortex

/-- The constructed preparation operation, retaining the same rank/torsion
constants when the required order is chosen later. -/
def IntrinsicPreparationKernel (α : ℝ) (h : ℕ) (ε : ℝ) (d T : ℕ) : Prop :=
  let D : ℝ := 2 ^ Nat.choose h 2
  ∀ N : ℕ, ∃ n₀ : ℕ,
  (∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        Module.finrank ℤ (physQuot H F) ≤ d ∧
          Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T) ∧
      let L := d + (d + 1) * Nat.log 2 T
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) → (∑ j ∈ range (L + 1), β j) ≤ ε →
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (γ : ℝ),
        n₀ ≤ Fintype.card V → 2 * α ≤ γ →
        CommonNbrCond H F γ → CleanHingeCond H F γ h →
        ∃ r ≤ L, ∃ A : Finset V,
          physicalPotential H F T ≤ r ∧ physicalPotential (restrictedHost H A) F T = r ∧
          let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
          (A.card : ℝ) ≤ Fintype.card V * debt ∧
          (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors A) ∧
          CommonNbrCond (restrictedHost H A) F (γ - D * debt) ∧
          CleanHingeCond (restrictedHost H A) F (γ - D * debt) h ∧
          Dispersal.PreparedCore (restrictedHost H A).G (restrictedHost H A).lab
            F (α / 2) h N (β r)

theorem IntrinsicPreparationKernel.mono {α : ℝ} {h d T : ℕ} {ε ε' : ℝ}
    (K : IntrinsicPreparationKernel α h ε d T) (hε : ε' ≤ ε) :
    IntrinsicPreparationKernel α h ε' d T := by
  dsimp only [IntrinsicPreparationKernel] at K ⊢
  intro N
  obtain ⟨n₀, hQuot, hPrepare⟩ := K N
  refine ⟨n₀, hQuot, ?_⟩
  intro β hβ hBudget
  exact hPrepare β hβ (hBudget.trans hε)

theorem intrinsic_preparation_kernel_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T : ℕ, 1 ≤ T ∧ IntrinsicPreparationKernel α h ε d T := by
  obtain ⟨ε, hε, d, T, hT, hBuild⟩ := intrinsic_preparation_with_clean_geometry α h hα
  exact ⟨ε, hε, d, T, hT, hBuild⟩

#print axioms intrinsic_preparation_kernel_of_H3H4
end TypedTriangle.Vortex
