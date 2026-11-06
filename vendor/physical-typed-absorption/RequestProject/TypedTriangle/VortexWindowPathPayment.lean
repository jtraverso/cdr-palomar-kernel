/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexWindowPathEdgeLoss
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

/-- Both later vertex and edge losses are paid on the actual window. -/
theorem pay_deterministic_on_window {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V)
    (W : Finset V) {K : ℝ} (hK : K ≤ (pathsIn G m x y W).card)
    (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ)
    (hB : ∀ v, B.degree v ≤ d)
    (hwin : ((Z.card*m*W.card^(m-1) + (m+1)*d*(W.card+2)^(m-1) : ℕ) : ℝ) < K) :
    ∃ p ∈ pathsLen G (m+1) x y, intlSet m p ⊆ W ∧
      (∀ i : Fin m, intl m p i ∉ Z) ∧
      ∀ k < m+1, ¬ B.Adj (p.getVert k) (p.getVert (k+1)) := by
  let A := pathsIn G m x y W
  have hLength : ∀ p ∈ A, p.length = m+1 := by
    intro p hp
    exact SimpleGraph.mem_finsetWalkLength_iff.mp (mem_filter.mp (mem_filter.mp hp).1).1
  have hInternal : ∀ p ∈ A, intlSet m p ⊆ W := fun p hp => (mem_filter.mp hp).2
  have h1 := card_through_window_le m x y A W Z hLength hInternal
  have h2 := card_edge_window_le m x y A W hLength hInternal B d hB
  by_contra hNo
  push_neg at hNo
  have hCover : A ⊆ (A.filter fun p => ∃ i : Fin m, intl m p i ∈ Z) ∪
      (A.filter fun p => ∃ k ∈ Finset.range (m+1),
        B.Adj (p.getVert k) (p.getVert (k+1))) := by
    intro p hp
    by_cases hz : ∃ i : Fin m, intl m p i ∈ Z
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,hz⟩)
    · push_neg at hz
      obtain ⟨k,hk,hAdj⟩ := hNo p (mem_filter.mp hp).1 (mem_filter.mp hp).2 hz
      exact mem_union_right _ (mem_filter.mpr ⟨hp,k,mem_range.mpr hk,hAdj⟩)
  have hCount : A.card ≤ Z.card*m*W.card^(m-1) + (m+1)*d*(W.card+2)^(m-1) := by
    apply (card_le_card hCover).trans
    apply (card_union_le _ _).trans
    apply Nat.add_le_add h1
    convert h2 using 1 <;> congr 1 <;> ext p <;> simp only [Finset.mem_filter]
  have hCountR : (A.card:ℝ) ≤
      ((Z.card*m*W.card^(m-1) + (m+1)*d*(W.card+2)^(m-1) : ℕ) : ℝ) := by
    exact_mod_cast hCount
  exact (not_lt_of_ge (hK.trans hCountR)) hwin

/-- An admissible relative trim chosen before q retains a quarter of the
original native path scale. -/
theorem path_count_after_relative_trim {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hm : 0 < m)
    (x y : V) (W Z : Finset V) (a q β : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hWindow : (W.card:ℝ) ≤ 2*q*Fintype.card V)
    (hTrim : (Z.card:ℝ) ≤ β*W.card) (hBudget : β*(m:ℝ)*2^m ≤ a/4)
    (hCount : a*(Fintype.card V:ℝ)^m*q^m/2 ≤ (pathsIn G m x y W).card) :
    a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (pathsIn G m x y (W \ Z)).card := by
  have hLoss := relative_window_path_loss m hm ha hq hβ
    (Nat.cast_nonneg (Fintype.card V)) (Nat.cast_nonneg W.card) hTrim hWindow hBudget
  have hNat := paths_in_trim_count G m x y W Z
  have hNatR : ((pathsIn G m x y W).card:ℝ) ≤
      (pathsIn G m x y (W \ Z)).card + (Z.card:ℝ)*(m:ℝ)*(W.card:ℝ)^(m-1) := by
    exact_mod_cast hNat
  nlinarith only [hLoss,hNatR,hCount]

#print axioms pay_deterministic_on_window
#print axioms path_count_after_relative_trim

end TypedTriangle.Vortex
