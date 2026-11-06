/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRestrictedRawProfile
public import RequestProject.TypedTriangle.CorePoolGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V48
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference
variable {V I : Type*} [Fintype V]

/-- Literal raw weights on the exact survivor type used by the vortex. -/
def survivorSampledWeights (μ : Finset V → ℝ) (W : Finset V) (q : ℝ)
    (T : Finset (Survivors (univ \ W))) : ℝ :=
  restrictedWeights μ (univ \ W) T / q

theorem survivor_sampled_boundary (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (W : Finset V) (q : ℝ)
    (u v : Survivors (univ \ W)) (huv : u ≠ v) :
    bdry (restrictedHost H (univ \ W)) F (survivorSampledWeights μ W q) s(u,v) =
      sampW H.G H.lab F μ W u.1 v.1 / q := by
  have hDouble : (univ : Finset V) \ (univ \ W) = W := by ext x; simp
  rw [bdry_eq_sum_triOn]
  change (∑ T ∈ triOn (restrictedHost H (univ \ W)) F s(u,v),
    restrictedWeights μ (univ \ W) T / q) = _
  rw [← sum_div, ← bdry_eq_sum_triOn]
  rw [restricted_raw_boundary H F μ (univ \ W) u v huv, hDouble]

/-- Raw sampling on Survivors (univ \ W), with no exact-seed premise. -/
theorem survivor_sampled_raw_profile_from_coefficient_window
    (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (a b q loScale σ ξ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 < q) (hloScale : 0 < loScale) (hn : 0 < (Fintype.card V : ℝ))
    (hWeights : ∀ T, IsAllowed H F T →
      a / Fintype.card V ≤ μ T ∧ μ T ≤ b / Fintype.card V)
    (W : Finset V) (hWlo : loScale * q * Fintype.card V ≤ W.card)
    (hWhi : (W.card : ℝ) ≤ σ * q * Fintype.card V)
    (hProfile : ∀ u v, H.G.Adj u v →
      |sampW H.G H.lab F μ W u v / q - 1| ≤ ξ) :
    (∀ T, IsAllowed (restrictedHost H (univ \ W)) F T →
      (loScale * a) / Fintype.card (Survivors (univ \ W)) ≤
        survivorSampledWeights μ W q T ∧
      survivorSampledWeights μ W q T ≤
        (σ * b) / Fintype.card (Survivors (univ \ W))) ∧
    ∀ e ∈ edges (restrictedHost H (univ \ W)),
      |bdry (restrictedHost H (univ \ W)) F (survivorSampledWeights μ W q) e - 1| ≤ ξ := by
  have hWpos : (0 : ℝ) < W.card :=
    lt_of_lt_of_le (mul_pos (mul_pos hloScale hq) hn) hWlo
  constructor
  · intro T hT
    have hDeleted := (isAllowed_liftVertexSet_iff H F (univ \ W) T).mp hT
    have hAmbient := ((isAllowed_vertexDeleted_iff H F (univ \ W)
      (liftVertexSet (univ \ W) T)).mp hDeleted).1
    have hCoeff := hWeights _ hAmbient
    change a / Fintype.card V ≤ μ (T.map (Function.Embedding.subtype _)) ∧
      μ (T.map (Function.Embedding.subtype _)) ≤ b / Fintype.card V at hCoeff
    simp only [survivorSampledWeights, restrictedWeights, CorePaid.card_survivors_compl]
    constructor
    · apply le_trans ?_ (div_le_div_of_nonneg_right hCoeff.1 hq.le)
      rw [div_div]
      apply (div_le_div_iff₀ hWpos (mul_pos hn hq)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hWlo ha]
    · apply le_trans (div_le_div_of_nonneg_right hCoeff.2 hq.le) ?_
      rw [div_div]
      apply (div_le_div_iff₀ (mul_pos hn hq) hWpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hWhi hb]
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : (restrictedHost H (univ \ W)).G.Adj u v := by
        simpa only [edges,mem_filter,mem_univ,true_and,SimpleGraph.mem_edgeSet] using he
      rw [survivor_sampled_boundary H F μ W q u v huv.ne]
      exact hProfile u.1 v.1 huv

/-- Relative raw coefficient error grows by at most twice the relative
sample-size error on the exact survivor type of the recursive child. -/
theorem survivor_sampled_raw_profile_with_additive_error
    (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (C q ρ η ξ : ℝ) (hC : 0 < C) (hq : 0 < q)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hη : 0 ≤ η) (hη1 : η < 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hWeights : ∀ T, IsAllowed H F T →
      ((1 - ρ) / C) / Fintype.card V ≤ μ T ∧
        μ T ≤ ((1 + ρ) * C) / Fintype.card V)
    (W : Finset V) (hWlo : (1 - η) * q * Fintype.card V ≤ W.card)
    (hWhi : (W.card : ℝ) ≤ (1 + η) * q * Fintype.card V)
    (hProfile : ∀ u v, H.G.Adj u v →
      |sampW H.G H.lab F μ W u v / q - 1| ≤ ξ) :
    (∀ T, IsAllowed (restrictedHost H (univ \ W)) F T →
      ((1 - (ρ + 2 * η)) / C) / Fintype.card (Survivors (univ \ W)) ≤
        survivorSampledWeights μ W q T ∧
      survivorSampledWeights μ W q T ≤
        ((1 + (ρ + 2 * η)) * C) / Fintype.card (Survivors (univ \ W))) ∧
    ∀ e ∈ edges (restrictedHost H (univ \ W)),
      |bdry (restrictedHost H (univ \ W)) F (survivorSampledWeights μ W q) e - 1| ≤ ξ := by
  have hRaw := survivor_sampled_raw_profile_from_coefficient_window H F μ
    ((1 - ρ) / C) ((1 + ρ) * C) q (1 - η) (1 + η) ξ
    (by positivity) (by positivity) hq (by linarith) hn hWeights W hWlo hWhi hProfile
  refine ⟨?_, hRaw.2⟩
  intro T hT
  have hCoeff := hRaw.1 T hT
  have hLower : (1 - (ρ + 2 * η)) / C ≤ (1 - η) * ((1 - ρ) / C) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right ?_ hC.le
    nlinarith [mul_nonneg hρ hη]
  have hUpper : (1 + η) * ((1 + ρ) * C) ≤ (1 + (ρ + 2 * η)) * C := by
    have hScaled := mul_le_mul_of_nonneg_right hρ1 hη
    have hCoeffUpper : (1 + η) * (1 + ρ) ≤ 1 + (ρ + 2 * η) := by nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCoeffUpper hC.le
  exact ⟨(div_le_div_of_nonneg_right hLower (by positivity)).trans hCoeff.1,
    hCoeff.2.trans (div_le_div_of_nonneg_right hUpper (by positivity))⟩

#print axioms survivor_sampled_boundary
#print axioms survivor_sampled_raw_profile_from_coefficient_window
#print axioms survivor_sampled_raw_profile_with_additive_error
end TypedTriangle.RawReference
