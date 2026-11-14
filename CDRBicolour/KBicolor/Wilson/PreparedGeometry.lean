/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.Geometry
public import CountingCone.Construction

/-!
# Geometrically prepared Wilson cores at an explicit threshold

Starting with the original robust-profile assumptions, this constructs the
bounded pattern, the near-full placement, an STS on the group indices, and H2,
H3 and H4 for the residual of every Latin family. The remaining seed H1 is not
an assumption of this theorem and is not asserted in its conclusion.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle

theorem profile_square_of_div {k n : ℕ} (c : Fin k → ℕ) (hsum : ∑ X, c X = n)
    (hdiv : 3 * ∑ X, c X * (c X - 1) = n * (n - 1)) :
    3 * ∑ X, (c X : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n := by
  have hprod : ∀ a : ℕ, ((a * (a - 1) : ℕ) : ℝ) = (a : ℝ) ^ 2 - a := by
    intro a
    simp only [Nat.mul_sub, Nat.mul_one]
    rw [Nat.cast_sub (Nat.le_mul_self a), Nat.cast_mul]
    ring
  have hsumR : ∑ X, (c X : ℝ) = n := by exact_mod_cast hsum
  have hsumP : ∑ X, ((c X * (c X - 1) : ℕ) : ℝ) = ∑ X, (c X : ℝ) ^ 2 - n := by
    simp_rw [hprod]
    rw [sum_sub_distrib, hsumR]
  have hdivR : (3 : ℝ) * ∑ X, ((c X * (c X - 1) : ℕ) : ℝ) =
      ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hdiv
  rw [hprod n, hsumP] at hdivR
  linarith

def wilsonGeometricThreshold (k g : ℕ) (δ η ρ ξ : ℝ) : ℕ :=
  max (wilsonPlacementThreshold k g δ η ρ ξ) (reserveThreshold k (ρ * δ / 4))

theorem exists_geometric_core {k g : ℕ} (hk : 4 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ρ ξ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hξ : 0 < ξ) :
    ∀ (n : ℕ) (lab : Fin n → Fin k), wilsonGeometricThreshold k g δ η ρ ξ ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      (∀ X, δ * n ≤ ksz lab X) → (∃ a, SeedData (ksz lab) η a) →
      ∃ (m : Fin k → ℕ) (t : ℕ), (∀ X, 1 ≤ m X) ∧
        ∑ X, m X ≤ wilsonPatternBound k δ η ρ ξ ∧
        3 * ∑ X, m X ^ 2 = (∑ X, m X) ^ 2 ∧
        (∀ X, |(m X : ℝ) / (∑ Y, m Y : ℕ) - ksz lab X / n| ≤ ξ) ∧
        (1 - ρ) * n ≤ ((g * (∑ X, m X) * t : ℕ) : ℝ) ∧
        (n : ℝ) / (4 * g * wilsonPatternBound k δ η ρ ξ) ≤ t ∧
        ∃ (h : Setup lab (fun x : (Σ X, Fin (m X)) => x.1) g t)
          (S : Finset (Finset (Fin g))), _root_.STS.IsSTS S ∧
          ∀ Λ : LFam (Σ X, Fin (m X)) S t,
          IsPhysical (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
            (edges (rHostK lab ((crossP h Λ).biUnion triEdges))) ∧
          CommonNbrCond (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
            (reserveAlpha (ρ * δ / 4)) ∧
          HingeCond (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
            (reserveAlpha (ρ * δ / 4)) 6 := by
  intro n lab hn hodd heven hdiv hcls hseed
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  obtain ⟨m, t, hm, hB, hcone, hclose, hcover, htlin, h, hreserve⟩ :=
    exists_near_full_setup_reserve_explicit hk (by omega) hδ hη hρ hρ1 hξ n lab
      (le_of_max_le_left hn) (profile_square_of_div (ksz lab) hsum hdiv) hcls hseed
  have h1 := _root_.STS.lemma4 g hg hga
  unfold _root_.STS.D7 at h1
  obtain ⟨⟨S, hS, -⟩⟩ := (Nat.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one h1)).1
  refine ⟨m, t, hm, hB, hcone, hclose, hcover, htlin, h, S, hS, fun Λ => ?_⟩
  exact residual_H234 h (by omega) hS Λ (by positivity) (le_of_max_le_right hn)
    hreserve hodd heven hdiv

end CDRBicolour.KBicolor.Wilson
