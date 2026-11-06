/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.NestedVertexQuotients

@[expose] public section

/-! Common windows and concrete strict-step bounds. Local candidate; NOT kernel-checked. -/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

theorem uniform_nested_vertex_windows (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (A B : Finset V), n₀ ≤ Fintype.card V →
        (A.card : ℝ) ≤ ε*Fintype.card V → (B.card : ℝ) ≤ ε*Fintype.card V →
        (A.card : ℝ) ≤ α*Fintype.card V/2 ∧
        (A.card : ℝ)*2 ^ Nat.choose (h+1) 2 ≤ α/2*Fintype.card V ∧
        (B.card : ℝ)+2 < (α/2)*Fintype.card (Survivors A) ∧
        ((B.card : ℝ)+h)*2 ^ Nat.choose h 2 ≤ α/4*Fintype.card (Survivors A) := by
  obtain ⟨δ,hδ,hδhalf,hδbudget⟩ := original_geometry_vertex_budget hα h
  let P : ℝ := 2 ^ Nat.choose h 2
  let Q : ℝ := 2 ^ Nat.choose (h+1) 2
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hQ : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have hPQ : P ≤ Q := pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 (by omega))
  let ε : ℝ := min δ (α/(128*Q))
  have hε : 0 < ε := lt_min hδ (by positivity)
  let n₀ : ℕ := ⌈(16+16*h*P)/α⌉₊+1
  refine ⟨ε,hε,n₀,fun {V} _ A B hn hA hB => ?_⟩
  let n : ℝ := Fintype.card V
  have hn0 : 0 ≤ n := by positivity
  have hAδ : (A.card : ℝ) ≤ δ*n :=
    hA.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  obtain ⟨hA3,hA4⟩ := hδbudget hn0 hAδ
  have hhalf : (A.card : ℝ) ≤ n/2 := by
    have := mul_le_mul_of_nonneg_right hδhalf hn0
    linarith
  have hcard : (Fintype.card (Survivors A) : ℝ)+(A.card : ℝ)=n := by
    dsimp [n]
    exact_mod_cast card_survivors_add_card A
  have hN : n/2 ≤ (Fintype.card (Survivors A) : ℝ) := by linarith
  have hnlarge : 16+16*h*P < α*n := by
    have hc : (16+16*h*P)/α ≤ (⌈(16+16*h*P)/α⌉₊ : ℝ) := Nat.le_ceil _
    have hcn : ((n₀ : ℕ) : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast hn
    dsimp [n₀] at hcn
    push_cast at hcn
    have hd : (16+16*h*P)/α < n := by linarith
    have := (div_lt_iff₀ hα).1 hd
    linarith
  have hn16 : 16 ≤ α*n := by
    have : 0 ≤ (h : ℝ)*P := by positivity
    nlinarith
  have hhP : (h : ℝ)*P ≤ α*n/16 := by linarith
  have hzQ : (B.card : ℝ)*Q ≤ α*n/128 := by
    have hεQ : ε ≤ α/(128*Q) := min_le_right _ _
    have h1 := hB.trans (mul_le_mul_of_nonneg_right hεQ hn0)
    calc (B.card : ℝ)*Q ≤ (α/(128*Q)*n)*Q :=
           mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = α*n/128 := by field_simp
  have hzP : (B.card : ℝ)*P ≤ α*n/64 := by
    have h1 := mul_le_mul_of_nonneg_left hPQ (show (0 : ℝ) ≤ B.card by positivity)
    have h2 : 0 ≤ α*n := mul_nonneg hα.le hn0
    linarith
  obtain ⟨hw1,hw2⟩ := vertex_deletion_windows hα
    (show (0 : ℝ) ≤ B.card by positivity) hP hN hn16 hzP hhP
  exact ⟨hA3,hA4,hw1,hw2⟩

/-- All maps and bounds in the chain are built from original-host H3--H4. -/
theorem physical_vertex_chain_control (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        (∀ A B : Finset V, (A.card : ℝ) ≤ ε*Fintype.card V →
          (B.card : ℝ) ≤ ε*Fintype.card V →
          Function.Surjective (nestedVertexQuotMap H F A B)) ∧
        (∀ (Z : ℕ → Finset V) (hz : ∀ k, Z k ⊆ Z (k+1)) (m : ℕ),
          (∀ k ≤ m, ((Z k).card : ℝ) ≤ ε*Fintype.card V) →
          ((Finset.range m).filter (fun k => ¬ Function.Injective
            (quotMap (F := F) (vertexDeleted_antitone H (hz k)) rfl))).card ≤
            d+(d+1)*Nat.log 2 T) := by
  obtain ⟨ε₁,hε₁,N₁,hwin⟩ := uniform_nested_vertex_windows α h hα
  obtain ⟨δ,hδ,d,T,N₂,hT,hbounds⟩ := physQuot_vertexDeleted_bounds_of_original_geometry α h hα
  let ε : ℝ := min ε₁ δ
  have hε : 0 < ε := lt_min hε₁ hδ
  refine ⟨ε,hε,d,T,max N₁ N₂,hT,fun {V I} _ H F hn hH3 hH4 => ?_⟩
  have hn1 : N₁ ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hn2 : N₂ ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hsmall₁ : ∀ A : Finset V, (A.card : ℝ) ≤ ε*Fintype.card V →
      (A.card : ℝ) ≤ ε₁*Fintype.card V := by
    intro A hA
    exact hA.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hsmall₂ : ∀ A : Finset V, (A.card : ℝ) ≤ ε*Fintype.card V →
      (A.card : ℝ) ≤ δ*Fintype.card V := by
    intro A hA
    exact hA.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hs : ∀ A B : Finset V, (A.card : ℝ) ≤ ε*Fintype.card V →
      (B.card : ℝ) ≤ ε*Fintype.card V → Function.Surjective (nestedVertexQuotMap H F A B) := by
    intro A B hA hB
    obtain ⟨hA3,hA4,hB1,hB2⟩ := hwin A B hn1 (hsmall₁ A hA) (hsmall₁ B hB)
    exact nestedVertexQuotMap_surjective hα hH3 hH4 A B hA3 hA4 hB1 hB2
  refine ⟨hs,fun Z hz m hZ => ?_⟩
  apply physical_chain_strict_count (fun k => vertexDeleted H (Z k)) F
    (fun k => vertexDeleted_antitone H (hz k)) (fun _ => rfl) m d T
  · intro k hk
    have hks := hs (Z k) (Z (k+1)) (hZ k (by omega)) (hZ (k+1) (by omega))
    exact (quotMap_surjective_congr_source
      (congrArg (vertexDeleted H) (Finset.union_eq_right.2 (hz k))) _ _ _ _).1 hks
  · intro k hk
    exact (hbounds H F (Z k) hn2 hH3 hH4 (hsmall₂ (Z k) (hZ k hk))).1
  · intro k hk
    exact (hbounds H F (Z k) hn2 hH3 hH4 (hsmall₂ (Z k) (hZ k hk))).2

end TypedTriangle
