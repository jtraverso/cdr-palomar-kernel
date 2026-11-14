/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.AbsorptionCore
public import RequestProject.TypedTriangle.MainPaperIIITower

/-!
# Complete absorption of the common Wilson residual

The host assumptions are the original robust SeedData, parity and pair identity.
H1-H4 are constructed before invoking T. No residual decomposition is an input.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle
open scoped Classical

/-- The full absorption threshold, before the host is chosen. -/
def coreTowerThreshold {k : ℕ} (hk : 4 ≤ k) (g : ℕ) (δ η ρ : ℝ) : ℕ :=
  let o : Fin k := ⟨0,by omega⟩
  let ξ := seedAccuracy g o δ η
  let C := max 1 (globalSeedConstant (g : ℝ) η δ)
  max 1 (max (Vortex.Explicit.paperIIITowerThreshold (reserveAlpha (ρ*δ/4)) C 6)
    (max (wilsonGeometricThreshold k g δ η ρ ξ) (seedThreshold g o δ η)))

theorem absorption_core_at_tower_order {k g : ℕ} (hk : 4 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ρ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hρgroup : ρ ≤ 1/((g : ℝ)+1)) :
    let o : Fin k := ⟨0,by omega⟩
    let ξ := seedAccuracy g o δ η
    ∀ (n : ℕ) (lab : Fin n → Fin k), coreTowerThreshold hk g δ η ρ ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X, ksz lab X*(ksz lab X-1) = n*(n-1) →
      (∀ X, δ*n ≤ ksz lab X) → (∃ a, SeedData (ksz lab) η a) →
      ∃ (m : Fin k → ℕ) (t : ℕ), (∀ X, 1 ≤ m X) ∧
        ∑ X, m X ≤ wilsonPatternBound k δ η ρ ξ ∧
        3*∑ X, m X^2 = (∑ X, m X)^2 ∧
        (∀ X, |(m X : ℝ)/(∑ Y, m Y : ℕ) - ksz lab X/n| ≤ ξ) ∧
        (1-ρ)*n ≤ ((g*(∑ X,m X)*t : ℕ) : ℝ) ∧
        (n : ℝ)/(4*g*wilsonPatternBound k δ η ρ ξ) ≤ t ∧
        ∃ (h : Setup lab (fun x : (Σ X,Fin (m X)) => x.1) g t)
          (S : Finset (Finset (Fin g))), _root_.STS.IsSTS S ∧
          ∀ Λ : LFam (Σ X,Fin (m X)) S t,
            ∃ D, IsDecomposition (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
              (edges (rHostK lab ((crossP h Λ).biUnion triEdges))) D := by
  intro o ξ
  have hξ : 0 < ξ := (seedAccuracy_spec (by omega) (by omega) o hδ hη).1
  let C₀ := globalSeedConstant (g : ℝ) η δ
  let C := max 1 C₀
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀ : 0 < C₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  let nT := Vortex.Explicit.paperIIITowerThreshold (reserveAlpha (ρ*δ/4)) C 6
  intro n lab hn hodd heven hdiv hcls hseed
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnrest := (le_max_right _ _).trans hn
  have hnT : nT ≤ n := (le_max_left _ _).trans hnrest
  have hnprep := (le_max_right _ _).trans hnrest
  have hnG : wilsonGeometricThreshold k g δ η ρ ξ ≤ n := (le_max_left _ _).trans hnprep
  have hnS : seedThreshold g o δ η ≤ n := (le_max_right _ _).trans hnprep
  obtain ⟨m,t,hm,hB,hcone,hclose,hcover,htlin,h,S,hS,h234⟩ :=
    exists_geometric_core hk hg hga hδ hη hρ hρhalf hξ n lab hnG hodd heven hdiv hcls hseed
  have hcard : Fintype.card (Σ X,Fin (m X)) = ∑ X,m X := by
    simp only [Fintype.card_sigma,Fintype.card_fin]
  have hsum : ∑ X,ksz lab X=n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _),card_univ,Fintype.card_fin]
  have hglobal := profile_square_of_div (ksz lab) hsum hdiv
  obtain ⟨a,ha⟩ := hseed
  refine ⟨m,t,hm,hB,hcone,hclose,hcover,htlin,h,S,hS,fun Λ => ?_⟩
  obtain ⟨μ,hμ⟩ := residual_H1_at_threshold h (by omega) o hS Λ (by omega)
    hδ hη hρhalf hρgroup hnS (by rwa [hcard]) ha hcls
    (by simpa only [Pattern.csize_sigma,hcard] using hclose)
    hglobal (by simpa only [Pattern.csize_sigma] using hcone)
  have hμ' : IsDiffuseSeed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) C μ :=
    diffuse_seed_enlarge (by rw [Fintype.card_fin]; omega) hC₀ (le_max_right _ _) hμ
  obtain ⟨H2,H3,H4⟩ := h234 Λ
  exact Vortex.Explicit.main_theorem_T_at_tower_order (bicF k) (reserveAlpha (ρ*δ/4)) C 6
    (reserveAlpha_pos (by positivity)) hC le_rfl
    (rHostK lab ((crossP h Λ).biUnion triEdges))
    (by rw [Fintype.card_fin]; exact hnT) ⟨μ,hμ'⟩ H2 H3 H4

end CDRBicolour.KBicolor.Wilson
