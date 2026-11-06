/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.PreparedDeletion
public import RequestProject.TypedTriangle.RoutingInputs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Local bridge candidate from the original H3--H4 to all routing inputs.
No prepared routing, component count or deletion provider is assumed.
Pending the rc3 audit; the positive G3 catalogue is a separate construction. -/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.RoutingConstants

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)}

theorem routing_deletion_of_H3H4 {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h)
    (hn : routeN0 α h ≤ Fintype.card V) (A : Finset V)
    (hA : (A.card : ℝ) ≤ routeδ α h * Fintype.card V) :
    DeletionHyp G lab F A := by
  obtain ⟨hw1, hw2⟩ := routeWindows hα h hn hA
  exact deletionHyp_of_H3H4 hα hH3 hH4 A hw1 hw2

/-- Constants are fixed before the finite host, with the original hypotheses. -/
theorem routing_geometry_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ C D : ℕ, ∃ δ : ℝ, ∃ n₀ : ℕ,
      1 ≤ C ∧ 0 < δ ∧ (C : ℝ) * δ ≤ 4 ∧ 1 ≤ D ∧ 12 * C ^ 2 ≤ D + 1 ∧
      ∀ {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)), n₀ ≤ Fintype.card V →
        CommonNbrCond (⟨G, lab⟩ : Host V I) F α →
        HingeCond (⟨G, lab⟩ : Host V I) F α h →
        0 < Fintype.card V ∧
          (∀ a, (univ.filter (fun j : Row V => j.1 = a ∧ IsActiveRow G lab F j)).card ≤ C) ∧
          (∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card) ∧
          ∀ A : Finset V, (A.card : ℝ) ≤ δ * Fintype.card V →
            DeletionHyp G lab F A := by
  refine ⟨compConst α, routeD α, routeδ α h, routeN0 α h,
    one_le_compConst α, routeδ_pos hα h, compConst_mul_routeδ_le α h,
    one_le_routeD α, routeD_spec α, ?_⟩
  intro V I _ G lab F hn hH3 hH4
  have hlow : ∀ j : Row V, IsActiveRow G lab F j →
      α * Fintype.card V ≤ j.2.card := by
    rintro ⟨a, K⟩ hK
    exact active_component_card_ge hH3 hK
  obtain ⟨hpos, hrows, hdeg, -⟩ :=
    RoutingInputs.routing_inputs_host hα h G lab F hlow hn
  exact ⟨hpos, hrows, hdeg, fun A hA => routing_deletion_of_H3H4 hα hH3 hH4 hn A hA⟩

/-- Actual cells, rather than a routing provider, from H3--H4. -/
theorem routing_cells_of_H3H4 {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h)
    (hn : routeN0 α h ≤ Fintype.card V)
    (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) (he : 0 < norm1 G x) :
    ∃ cells : List (Sym2 V → ℤ), (∀ b ∈ cells, IsLocalProfile G lab F b) ∧
      (∀ e, (cells.map (fun b => b e)).sum = x e) ∧
      (cells.length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cells, norm1 G b ≤ 3 * routeD α) ∧
      (cells.map (norm1 G)).sum ≤ 6 * routeD α * norm1 G x ∧
      ∀ v, (cells.countP (fun b => decide (InSupp G v b)) : ℤ) <
        3 * dabs G x v + ⌈32 * routeD α * (norm1 G x : ℝ) /
          (routeδ α h * Fintype.card V)⌉₊ + 2 * routeD α := by
  have hlow : ∀ j : Row V, IsActiveRow G lab F j →
      α * Fintype.card V ≤ j.2.card := by
    rintro ⟨a, K⟩ hK
    exact active_component_card_ge hH3 hK
  exact RoutingInputs.routing_budget_of_lower hα h G lab F hlow hn
    (fun A hA => routing_deletion_of_H3H4 hα hH3 hH4 hn A hA) x hx he

end TypedTriangle.ActiveCover
