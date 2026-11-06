/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RawProfileDeletion
public import RequestProject.TypedTriangle.RestrictedHingeTransport
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

/-- Literal restriction of the raw profile: no size renormalization. -/
def restrictedWeights (μ : Finset V → ℝ) (A : Finset V)
    (T : Finset (Survivors A)) : ℝ :=
  μ (T.map (Function.Embedding.subtype _))

theorem raw_boundary_eq_samp_univ (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (u v : V) (huv : u ≠ v) :
    bdry H F μ s(u,v) = sampW H.G H.lab F μ univ u v := by
  have hs := sum_compW_eq_load H.G H.lab F μ huv
  have hsets : univ.filter (fun T => SparseEdge.IsAllowed H.G H.lab F T ∧
      s(u,v) ∈ SparseEdge.triEdges T) = triOn H F s(u,v) := by
    ext T
    simp only [triOn,allowed,mem_filter,mem_univ,true_and]
    rfl
  rw [hsets] at hs
  rw [bdry_eq_sum_triOn, ← hs]
  rfl

private theorem compW_change_decEq {X J : Type*} (d₁ d₂ : DecidableEq X)
    (G : SimpleGraph X) (lab : X → J) (F : Set (Multiset J))
    (μ : Finset X → ℝ) (u v a : X) :
    @compW X J d₁ G lab F μ u v a = @compW X J d₂ G lab F μ u v a := by
  cases Subsingleton.elim d₁ d₂
  rfl

theorem restricted_raw_boundary (H : Host V I) (F : Set (Multiset I))
    (μ : Finset V → ℝ) (A : Finset V) (u v : Survivors A) (huv : u ≠ v) :
    bdry (restrictedHost H A) F (restrictedWeights μ A) s(u,v) =
      sampW H.G H.lab F μ (univ \ A) u.1 v.1 := by
  rw [raw_boundary_eq_samp_univ (restrictedHost H A) F (restrictedWeights μ A) u v huv]
  have hc (a : Survivors A) :
      compW (restrictedHost H A).G (restrictedHost H A).lab F
        (restrictedWeights μ A) u v a = compW H.G H.lab F μ u.1 v.1 a.1 := by
    unfold compW
    have hAllow := isAllowed_restricted_triple H F A u v a
    change IsAllowed (restrictedHost H A) F {u,v,a} ↔
      IsAllowed H F {u.1,v.1,a.1} at hAllow
    split_ifs with hLeft hRight hRight
    · simp [restrictedWeights]
    · exact False.elim (hRight (hAllow.mp hLeft))
    · exact False.elim (hLeft (hAllow.mpr hRight))
    · rfl
  change (∑ a : Survivors A, _) = ∑ a ∈ univ \ A, _
  refine Finset.sum_bij (fun a _ => a.1) ?_ ?_ ?_ ?_
  · intro a _
    exact mem_sdiff.mpr ⟨mem_univ _, a.2⟩
  · intro a _ a' _ ha
    exact Subtype.ext ha
  · intro a ha
    exact ⟨⟨a, (mem_sdiff.mp ha).2⟩, mem_univ _, rfl⟩
  · intro a _
    exact (compW_change_decEq (Classical.decEq (Survivors A))
      (fun x y : Survivors A => x.instDecidableEq y)
      (restrictedHost H A).G (restrictedHost H A).lab F (restrictedWeights μ A) u v a).trans
      (hc a)

/-- Coefficient and load transport on the exact surviving vertex type. -/
theorem restricted_raw_profile_from_coefficient_window
    (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (a b ξ δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hWeights : ∀ T, IsAllowed H F T →
      a / Fintype.card V ≤ μ T ∧ μ T ≤ b / Fintype.card V)
    (hLoad : ∀ e ∈ edges H, |bdry H F μ e - 1| ≤ ξ)
    (A : Finset V) (hA : (A.card : ℝ) ≤ δ * Fintype.card V) :
    (∀ T, IsAllowed (restrictedHost H A) F T →
      ((1 - δ) * a) / Fintype.card (Survivors A) ≤ restrictedWeights μ A T ∧
        restrictedWeights μ A T ≤ b / Fintype.card (Survivors A)) ∧
    ∀ e ∈ edges (restrictedHost H A),
      |bdry (restrictedHost H A) F (restrictedWeights μ A) e - 1| ≤ ξ + b * δ := by
  have hCard : (Fintype.card (Survivors A) : ℝ) + A.card = Fintype.card V := by
    exact_mod_cast card_survivors_add_card A
  have hSize : (1 - δ) * Fintype.card V ≤ Fintype.card (Survivors A) := by
    nlinarith
  have hnA : (0 : ℝ) < Fintype.card (Survivors A) :=
    lt_of_lt_of_le (mul_pos (by linarith) hn) hSize
  have hUpperSize : (Fintype.card (Survivors A) : ℝ) ≤ Fintype.card V := by
    have hA0 : (0 : ℝ) ≤ A.card := by positivity
    linarith
  have hNonneg : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b / Fintype.card V := by
    intro T hT
    exact ⟨(div_nonneg ha hn.le).trans (hWeights T hT).1, (hWeights T hT).2⟩
  constructor
  · intro T hT
    have hDeleted := (isAllowed_liftVertexSet_iff H F A T).mp hT
    have hAmbient := ((isAllowed_vertexDeleted_iff H F A (liftVertexSet A T)).mp hDeleted).1
    have hCoeff := hWeights _ hAmbient
    change _ ≤ μ (T.map (Function.Embedding.subtype _)) ∧
      μ (T.map (Function.Embedding.subtype _)) ≤ _
    change a / Fintype.card V ≤ μ (T.map (Function.Embedding.subtype _)) ∧
      μ (T.map (Function.Embedding.subtype _)) ≤ b / Fintype.card V at hCoeff
    constructor
    · apply le_trans ?_ hCoeff.1
      apply (div_le_div_iff₀ hnA hn).mpr
      have hScaled := mul_le_mul_of_nonneg_left hSize ha
      nlinarith
    · exact hCoeff.2.trans (div_le_div_of_nonneg_left hb hnA hUpperSize)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : (restrictedHost H A).G.Adj u v := by
        simpa only [edges,mem_filter,mem_univ,true_and,SimpleGraph.mem_edgeSet] using he
      have huvAmbient : H.G.Adj u.1 v.1 := huv
      have heAmbient : s(u.1,v.1) ∈ edges H :=
        mem_filter.mpr ⟨mem_univ _, (SimpleGraph.mem_edgeSet H.G).mpr huvAmbient⟩
      have hRaw : |sampW H.G H.lab F μ univ u.1 v.1 / 1 - 1| ≤ ξ := by
        simpa only [div_one, ← raw_boundary_eq_samp_univ H F μ u.1 v.1 huvAmbient.ne]
          using hLoad _ heAmbient
      have hBudget : (A.card : ℝ) * (b / Fintype.card V) ≤ 1 * (b * δ) := by
        have hScaled := mul_le_mul_of_nonneg_left hA hb
        rw [show (A.card : ℝ) * (b / Fintype.card V) =
          b * A.card / Fintype.card V by ring]
        apply (div_le_iff₀ hn).mpr
        nlinarith
      have hProfile := sampled_profile_after_vertex_deletion H F μ univ A u.1 v.1
        b 1 ξ (b * δ) hb (by norm_num) hn hNonneg hRaw hBudget
      rw [restricted_raw_boundary H F μ A u v huv.ne]
      simpa only [div_one] using hProfile

/-- Relative error grows by the removed vertex proportion while literal
triangle weights are preserved. -/
theorem restricted_raw_profile_with_additive_error
    (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (C ρ ξ δ : ℝ) (hC : 0 < C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hn : 0 < (Fintype.card V : ℝ))
    (hWeights : ∀ T, IsAllowed H F T →
      ((1 - ρ) / C) / Fintype.card V ≤ μ T ∧
        μ T ≤ ((1 + ρ) * C) / Fintype.card V)
    (hLoad : ∀ e ∈ edges H, |bdry H F μ e - 1| ≤ ξ)
    (A : Finset V) (hA : (A.card : ℝ) ≤ δ * Fintype.card V) :
    (∀ T, IsAllowed (restrictedHost H A) F T →
      ((1 - (ρ + δ)) / C) / Fintype.card (Survivors A) ≤ restrictedWeights μ A T ∧
        restrictedWeights μ A T ≤ ((1 + (ρ + δ)) * C) / Fintype.card (Survivors A)) ∧
    ∀ e ∈ edges (restrictedHost H A),
      |bdry (restrictedHost H A) F (restrictedWeights μ A) e - 1| ≤
        ξ + ((1 + ρ) * C) * δ := by
  have hRaw := restricted_raw_profile_from_coefficient_window H F μ
    ((1 - ρ) / C) ((1 + ρ) * C) ξ δ (by positivity) (by positivity) hδ hδ1 hn
    hWeights hLoad A hA
  refine ⟨?_, hRaw.2⟩
  intro T hT
  have hCoeff := hRaw.1 T hT
  have hLower : (1 - (ρ + δ)) / C ≤ (1 - δ) * ((1 - ρ) / C) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right ?_ hC.le
    nlinarith [mul_nonneg hρ hδ]
  have hUpper : (1 + ρ) * C ≤ (1 + (ρ + δ)) * C := by
    apply mul_le_mul_of_nonneg_right ?_ hC.le
    linarith
  exact ⟨(div_le_div_of_nonneg_right hLower (by positivity)).trans hCoeff.1,
    hCoeff.2.trans (div_le_div_of_nonneg_right hUpper (by positivity))⟩

#print axioms restricted_raw_boundary
#print axioms restricted_raw_profile_from_coefficient_window
#print axioms restricted_raw_profile_with_additive_error
end TypedTriangle.RawReference
