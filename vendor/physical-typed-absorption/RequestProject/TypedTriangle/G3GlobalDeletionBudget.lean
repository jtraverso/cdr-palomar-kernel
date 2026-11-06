/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3ResourceUnionBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The reference-window budget also pays for deleting the entire lifted
sampled reference, provided its density scale is chosen below the global
complement threshold. This is an arithmetic interface, not a vortex step. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open SelSimul

theorem four_resource_global_deletion_budget {V : Type} [Fintype V]
    (W : Finset V) (A B C D : Finset (Sym2 V))
    (q γ δ ρ τ ηT ε : ℝ)
    (hq : 0 < q) (hγ : 0 < γ)
    (hWlo : q*Fintype.card V/2 ≤ W.card)
    (hWhi : (W.card:ℝ) < 2*q*Fintype.card V)
    (hSum : ρ+τ+ηT ≤ γ*q/8) (hε : ε ≤ γ/4)
    (hA : ∀ v, (degIn A v:ℝ) ≤ ρ*Fintype.card V)
    (hB : ∀ v, (degIn B v:ℝ) ≤ τ*Fintype.card V)
    (hC : ∀ v, (degIn C v:ℝ) ≤ ηT*Fintype.card V)
    (hD : ∀ v, (degIn D v:ℝ) ≤ ε*W.card)
    (hLarge : 2 ≤ γ*W.card)
    (hGlobal : 2*γ*q+2*q ≤ δ) :
    ∃ dU : ℕ,
      (∀ v, degIn (((A∪B)∪C)∪D) v ≤ dU) ∧
      ((dU+W.card:ℕ):ℝ) ≤ δ*Fintype.card V := by
  obtain ⟨dU,hDegree,hdU⟩ := four_resource_reference_window W A B C D
    q γ ρ τ ηT ε hq hγ hWlo hSum hε hA hB hC hD hLarge
  refine ⟨dU,hDegree,?_⟩
  have hW : (W.card:ℝ) ≤ 2*q*Fintype.card V := le_of_lt hWhi
  have hγW := mul_le_mul_of_nonneg_left hW hγ.le
  have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hcap := mul_le_mul_of_nonneg_right hGlobal hn
  rw [Nat.cast_add]
  nlinarith only [hdU,hW,hγW,hcap]

#print axioms four_resource_global_deletion_budget

end TypedTriangle.CatalogNative
