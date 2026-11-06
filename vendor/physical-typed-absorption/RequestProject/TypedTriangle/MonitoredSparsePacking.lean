/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.WeightedStars
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedStar

/-- ONE actual packing controls the requested weights and every leftover degree.
Star tests are added to the SAME EGJ application. Their mass is derived from H3;
no independent packing is substituted after the monitored one is chosen. -/
theorem monitored_sparse_packing (C α c η : ℝ) (q : ℕ)
    (hC : 0 < C) (hα : 0 < α) (hc : 0 < c) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      CommonNbrCond H F α → ∀ (κ : Type) [Fintype κ] (W : κ → Finset V → ℝ),
      (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
      (∀ k T, IsAllowed H F T → 0 ≤ W k T ∧ W k T ≤ 1) →
      (∀ k, c*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*W k T) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        (∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
        ∀ k, |(∑ T ∈ P, W k T)-(∑ T ∈ allowed H F, φ T*W k T)| ≤
          η*(∑ T ∈ allowed H F, φ T*W k T) := by
  let c' := min c (α/2)
  have hc' : 0 < c' := lt_min hc (by positivity)
  obtain ⟨nP,hPack⟩ := NativeNibble.weighted_packing_of_diffuse_seed C c' η (q+2) hC hc' hη
  refine ⟨max 2 nP,?_⟩
  intro V I _ H F φ hn hφ h3 κ _ W hκ hW hmass
  classical
  let AV := {v : V // ActiveRoot H F v}
  let W' : (κ ⊕ AV) → Finset V → ℝ := fun k => match k with
    | Sum.inl j => W j
    | Sum.inr v => starWeight v.1
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast (le_max_left _ _).trans hn
  have hn1 : (1:ℝ) ≤ Fintype.card V := by linarith
  have hn0 : (0:ℝ) ≤ Fintype.card V := by positivity
  have hav : (Fintype.card AV:ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_subtype_le (ActiveRoot H F)
  have hpow1 : (1:ℝ) ≤ (Fintype.card V:ℝ)^q := one_le_pow₀ hn1
  have hpow : (Fintype.card V:ℝ)^q+Fintype.card V ≤ (Fintype.card V:ℝ)^(q+2) := by
    let n := (Fintype.card V:ℝ)
    have hp : 0 ≤ n^q := by positivity
    calc n^q+n ≤ n^q+n^q*n := add_le_add le_rfl (le_mul_of_one_le_left hn0 hpow1)
      _ = n^q*(1+n) := by ring
      _ ≤ n^q*n^2 := mul_le_mul_of_nonneg_left (by dsimp [n]; nlinarith) hp
      _ = n^(q+2) := by rw [pow_add]
  have hcount : (Fintype.card (κ ⊕ AV):ℝ) ≤ (Fintype.card V:ℝ)^(q+2) := by
    rw [Fintype.card_sum,Nat.cast_add]
    exact (add_le_add hκ hav).trans hpow
  have hW' : ∀ k T, IsAllowed H F T → 0 ≤ W' k T ∧ W' k T ≤ 1 := by
    intro k T hT
    cases k with
    | inl j => exact hW j T hT
    | inr v => dsimp [W',starWeight]; split_ifs <;> norm_num
  have hmass' : ∀ k, c'*Fintype.card V ≤ ∑ T ∈ allowed H F, φ T*W' k T := by
    intro k
    cases k with
    | inl j => exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0).trans (hmass j)
    | inr v => exact (mul_le_mul_of_nonneg_right (min_le_right c (α/2)) hn0).trans (seed_star_mass_bounds H F φ hφ h3 v.2).1
  obtain ⟨P,hPsub,hP,hWeights⟩ := hPack H F φ ((le_max_right _ _).trans hn) hφ
    (κ ⊕ AV) W' hcount hW' hmass'
  refine ⟨P,hPsub,hP,sparse_leftover_of_star_tests H F φ hφ hη.le P hP ?_,?_⟩
  · intro v
    by_cases hv : ActiveRoot H F v
    · exact hWeights (Sum.inr ⟨v,hv⟩)
    · have hsel : ∑ T ∈ P, starWeight v T=0 := by
        apply sum_eq_zero
        intro T hT
        apply if_neg
        exact fun hvT => hv ⟨T,hP.1 T hT,hvT⟩
      have hseed : ∑ T ∈ allowed H F, φ T*starWeight v T=0 := by
        apply sum_eq_zero
        intro T hT
        have hh : v ∉ T := fun hvT => hv ⟨T,isAllowed_of_mem_allowed hT,hvT⟩
        simp only [starWeight,if_neg hh,mul_zero]
      rw [hsel,hseed]
      norm_num
  · intro k
    exact hWeights (Sum.inl k)
end TypedTriangle.WeightedStar
