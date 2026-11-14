/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.PrescribedCounting.SparseHostCompletion
public import CDRBicolour.KBicolor.Wilson.PreparedSeed
public import CDRBicolour.KBicolor.Wilson.PreparedGeometry
public import CDRBicolour.KBicolor.Wilson.BalancedThreePattern

/-!
# Absorption of the Wilson residual with a sparse prescription

The host assumptions are the original robust SeedData, parity and pair identity.
H1-H4 are constructed on the actual host before sparse seed persistence and T.
No residual decomposition or deleted-host seed is an input.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CDRBicolour.KBicolor.PrescribedCounting
open CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle
open scoped Classical

def prescribedPatternBound (k : ℕ) (δ η ρ ξ : ℝ) : ℕ :=
  if k = 3 then 3 else wilsonPatternBound k δ η ρ ξ

theorem prescribedPatternBound_pos (k : ℕ) (δ η ρ ξ : ℝ) :
    0 < prescribedPatternBound k δ η ρ ξ := by
  unfold prescribedPatternBound
  split_ifs
  · decide
  · exact Nat.zero_lt_one.trans_le (le_max_right _ _)

/-- Both placement constructions supply the same Wilson geometry and reserve. -/
private theorem prescribedPlacement {k g : ℕ} (hk : 3 ≤ k) (hg : 1 ≤ g)
    {δ η ρ ξ : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hξ : 0 < ξ) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      3*∑ X, (ksz lab X : ℝ)^2 = (n : ℝ)^2+2*n →
      (∀ X, δ*n ≤ ksz lab X) → (∃ a, SeedData (ksz lab) η a) →
      ∃ (m : Fin k → ℕ) (t : ℕ), (∀ X, 1 ≤ m X) ∧
        ∑ X, m X ≤ prescribedPatternBound k δ η ρ ξ ∧
        3*∑ X, m X^2 = (∑ X, m X)^2 ∧
        (∀ X, |(m X : ℝ)/(∑ Y, m Y : ℕ) - ksz lab X/n| ≤ ξ) ∧
        (1-ρ)*n ≤ ((g*(∑ X,m X)*t : ℕ) : ℝ) ∧
        (n : ℝ)/(4*g*prescribedPatternBound k δ η ρ ξ) ≤ t ∧
        ∃ h : Setup lab (fun x : (Σ X,Fin (m X)) => x.1) g t,
          ∀ X, ρ*δ/4*n ≤ #((reserve h).filter fun v => lab v=X) := by
  by_cases h : k = 3
  · subst k
    obtain ⟨N, hN⟩ := exists_near_full_setup_reserve_three hg hδ hρ hρhalf hξ
    exact ⟨N, fun n lab hn hbalance hcls _ => by
      simpa only [prescribedPatternBound, eq_self, ite_true, Nat.cast_ofNat] using
        hN n lab hn hbalance hcls⟩
  · refine ⟨wilsonPlacementThreshold k g δ η ρ ξ, fun n lab hn hbalance hcls hseed => ?_⟩
    simpa only [prescribedPatternBound, ite_eq_right h] using
      exists_near_full_setup_reserve_explicit (by omega) hg hδ hη hρ hρhalf hξ
        n lab hn hbalance hcls hseed

theorem exists_reserved_absorption_core_of_three_le {k g : ℕ} (hk : 3 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ρ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hρgroup : ρ ≤ 1/((g : ℝ)+1)) :
    let o : Fin k := ⟨0,by omega⟩
    let ξ := seedAccuracy g o δ η
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X, ksz lab X*(ksz lab X-1) = n*(n-1) →
      (∀ X, δ*n ≤ ksz lab X) → (∃ a, SeedData (ksz lab) η a) →
      ∃ (m : Fin k → ℕ) (t : ℕ), (∀ X, 1 ≤ m X) ∧
        ∑ X, m X ≤ prescribedPatternBound k δ η ρ ξ ∧
        3*∑ X, m X^2 = (∑ X, m X)^2 ∧
        (∀ X, |(m X : ℝ)/(∑ Y, m Y : ℕ) - ksz lab X/n| ≤ ξ) ∧
        (1-ρ)*n ≤ ((g*(∑ X,m X)*t : ℕ) : ℝ) ∧
        (n : ℝ)/(4*g*prescribedPatternBound k δ η ρ ξ) ≤ t ∧
        ∃ (h : Setup lab (fun x : (Σ X,Fin (m X)) => x.1) g t)
          (S : Finset (Finset (Fin g))), _root_.STS.IsSTS S ∧
          (∀ X, ρ*δ/4*n ≤ #((reserve h).filter fun v => lab v=X)) ∧
          ∀ Λ : LFam (Σ X,Fin (m X)) S t,
            ∀ (Q : Finset (Finset (Fin n))) (d : ℕ),
            IsPacking (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) Q →
            (∀ v, SparseEdge.degIn (Q.biUnion triEdges) v ≤ d) → (d : ℝ) ≤ γ*n →
            ∃ D, IsDecomposition
              (residual (rHostK lab ((crossP h Λ).biUnion triEdges)) (Q.biUnion triEdges))
              (bicF k) (edges (residual (rHostK lab ((crossP h Λ).biUnion triEdges))
                (Q.biUnion triEdges))) D := by
  intro o ξ
  have hξ : 0 < ξ := (seedAccuracy_spec (by omega) (by omega) o hδ hη).1
  obtain ⟨nP, hP⟩ := prescribedPlacement hk (by omega : 1 ≤ g) hδ hη hρ hρhalf hξ
  let C₀ := globalSeedConstant (g : ℝ) η δ
  let C := max 1 C₀
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀ : 0 < C₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  obtain ⟨γ,hγ,nT,hT⟩ := sparse_host_completion (bicF k) C (reserveAlpha (ρ*δ/4)) 6
    hC (reserveAlpha_pos (by positivity)) le_rfl
  refine ⟨γ,hγ,max 1 (max nT (max (max nP (reserveThreshold k (ρ*δ/4)))
    (seedThreshold g o δ η))),fun n lab hn hodd heven hdiv hcls hseed => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnrest := (le_max_right _ _).trans hn
  have hnT : nT ≤ n := (le_max_left _ _).trans hnrest
  have hnprep := (le_max_right _ _).trans hnrest
  have hnG : max nP (reserveThreshold k (ρ*δ/4)) ≤ n := (le_max_left _ _).trans hnprep
  have hnS : seedThreshold g o δ η ≤ n := (le_max_right _ _).trans hnprep
  have hsum0 : ∑ X,ksz lab X=n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _),card_univ,Fintype.card_fin]
  obtain ⟨m,t,hm,hB,hcone,hclose,hcover,htlin,h,hreserve⟩ :=
    hP n lab ((le_max_left _ _).trans hnG) (profile_square_of_div (ksz lab) hsum0 hdiv) hcls hseed
  have h1 := _root_.STS.lemma4 g hg hga
  unfold _root_.STS.D7 at h1
  obtain ⟨⟨S,hS,-⟩⟩ := (Nat.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one h1)).1
  have hcard : Fintype.card (Σ X,Fin (m X)) = ∑ X,m X := by
    simp only [Fintype.card_sigma,Fintype.card_fin]
  have hglobal := profile_square_of_div (ksz lab) hsum0 hdiv
  obtain ⟨a,ha⟩ := hseed
  refine ⟨m,t,hm,hB,hcone,hclose,hcover,htlin,h,S,hS,hreserve,fun Λ Q d hQ hdeg hd => ?_⟩
  obtain ⟨μ,hμ⟩ := residual_H1_at_threshold h (by omega) o hS Λ (by omega)
    hδ hη hρhalf hρgroup hnS (by rwa [hcard]) ha hcls
    (by simpa only [Pattern.csize_sigma,hcard] using hclose)
    hglobal (by simpa only [Pattern.csize_sigma] using hcone)
  have hμ' : IsDiffuseSeed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) C μ :=
    diffuse_seed_enlarge (by rw [Fintype.card_fin]; omega) hC₀ (le_max_right _ _) hμ
  obtain ⟨H2,H3,H4⟩ := residual_H234 h (by omega) hS Λ (by positivity)
    ((le_max_right _ _).trans hnG) hreserve hodd heven hdiv
  have hBsub : Q.biUnion triEdges ⊆ edges (rHostK lab ((crossP h Λ).biUnion triEdges)) := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hQ.1 T hT) heT
  exact hT _ (by rw [Fintype.card_fin]; exact hnT) ⟨μ,hμ'⟩ H2 H3 H4
    (Q.biUnion triEdges) Q d hBsub ⟨hQ.1,hQ.2,by ext e; simp only [mem_biUnion]⟩ hdeg
    (by simpa only [Fintype.card_fin] using hd)

theorem exists_reserved_absorption_core {k g : ℕ} (hk : 4 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ρ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hρgroup : ρ ≤ 1/((g : ℝ)+1)) :
    let o : Fin k := ⟨0,by omega⟩
    let ξ := seedAccuracy g o δ η
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
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
          (∀ X, ρ*δ/4*n ≤ #((reserve h).filter fun v => lab v=X)) ∧
          ∀ Λ : LFam (Σ X,Fin (m X)) S t,
            ∀ (Q : Finset (Finset (Fin n))) (d : ℕ),
            IsPacking (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) Q →
            (∀ v, SparseEdge.degIn (Q.biUnion triEdges) v ≤ d) → (d : ℝ) ≤ γ*n →
            ∃ D, IsDecomposition
              (residual (rHostK lab ((crossP h Λ).biUnion triEdges)) (Q.biUnion triEdges))
              (bicF k) (edges (residual (rHostK lab ((crossP h Λ).biUnion triEdges))
                (Q.biUnion triEdges))) D := by
  have hk3 : k ≠ 3 := by omega
  simpa only [prescribedPatternBound, ite_eq_right hk3] using
    exists_reserved_absorption_core_of_three_le (k := k) (by omega) hg hga hδ hη hρ hρhalf hρgroup

end CDRBicolour.KBicolor.PrescribedCounting
