/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRawPathsWindowEquiv
public import RequestProject.TypedTriangle.VortexRelativeRawPathsPreparedVortex
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

/-- The actual prepared image is the raw window minus its actual lifted
trim. Both natural and real cardinality identities are retained. -/
theorem next_prepared_window_card_data {X : Type} [Fintype X]
    (W : Finset X) (B : Finset (Survivors (univ \ W))) :
    embeddingWindow (nextPreparedEmbedding W B) = W \ liftVertexSet (univ \ W) B ∧
    liftVertexSet (univ \ W) B ⊆ W ∧
    (liftVertexSet (univ \ W) B).card = B.card ∧
    (embeddingWindow (nextPreparedEmbedding W B)).card = W.card - B.card ∧
    ((embeddingWindow (nextPreparedEmbedding W B)).card : ℝ) = (W.card : ℝ) - B.card := by
  have hSub : liftVertexSet (univ \ W) B ⊆ W := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    change x.val ∈ W
    simpa using x.property
  have hCardB : B.card ≤ W.card := by
    simpa only [card_liftVertexSet] using Finset.card_le_card hSub
  have hCard : (embeddingWindow (nextPreparedEmbedding W B)).card = W.card - B.card := by
    rw [next_prepared_window_eq, Finset.card_sdiff_of_subset hSub, card_liftVertexSet]
  refine ⟨next_prepared_window_eq W B,hSub,card_liftVertexSet _ _,hCard,?_⟩
  rw [hCard,Nat.cast_sub hCardB]

/-- Any actual preparation trim is charged to the finite global prefix,
independently of the depth and of the rate of the preceding sample. -/
theorem raw_prepared_trim_le_total {X I : Type} [Fintype X]
    {H : Host X I} {F : Set (Multiset I)} {α C : ℝ} {β : ℕ → ℝ}
    {h N M d T : ℕ} {μ : Finset X → ℝ}
    (node : IntrinsicRawPreparedLayer H F α C β h N M d T μ)
    (Btotal : ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hTotal : (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j) ≤ Btotal) :
    (node.trim.card : ℝ) ≤ Btotal * Fintype.card X := by
  have hPrefix : (∑ j ∈ range node.index, β j) ≤
      ∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by have hs := node.index_le; omega))
      (by intro j _ _; exact hβ j)
  have hPrior : 0 ≤ ∑ j ∈ range (physicalPotential H F T), β j :=
    sum_nonneg (by intro j _; exact hβ j)
  have hBound := mul_le_mul_of_nonneg_left (hPrefix.trans hTotal)
    (by positivity : (0:ℝ) ≤ Fintype.card X)
  have hPriorMul := mul_nonneg (by positivity : (0:ℝ) ≤ Fintype.card X) hPrior
  nlinarith [node.cost]

theorem next_prepared_trim_le_total {X I : Type} [Fintype X]
    {H : Host X I} {F : Set (Multiset I)} {α q C : ℝ} {β : ℕ → ℝ}
    {h N M d T m : ℕ} {a εRoute t : ℝ}
    (W : Finset X) {μ : Finset (Survivors (univ \ W)) → ℝ}
    (tail : IntrinsicRawPathsPreparedVortex F α q C β h N M d T m a εRoute t
      (restrictedHost H (univ \ W)) μ)
    (Btotal : ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hTotal : (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j) ≤ Btotal) :
    ((liftVertexSet (univ \ W) tail.head.trim).card : ℝ) ≤ Btotal * W.card := by
  rw [card_liftVertexSet]
  simpa only [CorePaid.card_survivors_compl] using
    raw_prepared_trim_le_total tail.head Btotal hβ hTotal

/-- The fine raw cap supplies a uniform margin for the subsequent cut. -/
theorem raw_prepared_relative_error_le_sixteenth {X I : Type} [Fintype X]
    {H : Host X I} {F : Set (Multiset I)} {α C : ℝ} {β : ℕ → ℝ}
    {h N M d T : ℕ} {μ : Finset X → ℝ}
    (node : IntrinsicRawPreparedLayer H F α C β h N M d T μ)
    (hβ : ∀ j, 0 ≤ β j) :
    automaticRelativeError (Fintype.card (Survivors node.trim)) ≤ 1/16 := by
  have hPrefix : 0 ≤ ∑ j ∈ range node.index, β j := sum_nonneg (by intro j _; exact hβ j)
  have hE : (0:ℝ) ≤ max 1 (2*C) := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  have hDebt := mul_nonneg hE hPrefix
  have hc := node.raw_cap
  dsimp only [globalRawProfileError] at hc
  linarith

/-- The exact size tests for this very sample imply the margins used by
the real window budget. No new sample is selected. -/
theorem raw_sample_metadata_quarter_sizes {X I : Type} [Fintype X]
    {H : Host X I} {F : Set (Multiset I)} {α q C : ℝ} {β : ℕ → ℝ}
    {h N M d T : ℕ} {μ : Finset X → ℝ}
    (node : IntrinsicRawPreparedLayer H F α C β h N M d T μ)
    (W : Finset (Survivors node.trim))
    (metadata : RawSampleMetadata (restrictedHost H node.trim) F α q W)
    (hβ : ∀ j, 0 ≤ β j) (hq : 0 ≤ q) :
    (3/4:ℝ)*q*Fintype.card (Survivors node.trim) ≤ W.card ∧
    (W.card:ℝ) ≤ (5/4:ℝ)*q*Fintype.card (Survivors node.trim) := by
  have hη := raw_prepared_relative_error_le_sixteenth node hβ
  have hqn : 0 ≤ q * Fintype.card (Survivors node.trim) := mul_nonneg hq (by positivity)
  have hLo := mul_le_mul_of_nonneg_right (show (3/4:ℝ) ≤
    1-automaticRelativeError (Fintype.card (Survivors node.trim)) by linarith) hqn
  have hHi := mul_le_mul_of_nonneg_right (show
    1+automaticRelativeError (Fintype.card (Survivors node.trim)) ≤ (5/4:ℝ) by linarith) hqn
  constructor
  · nlinarith [metadata.size_relative_lower]
  · nlinarith [metadata.size_relative_upper]

/-- For the outer sample, the same margin is measured against the original
parent order, including vertices removed by its own preparation. -/
theorem raw_prepared_outer_sample_quarter_sizes {X I : Type} [Fintype X]
    {H : Host X I} {F : Set (Multiset I)} {α C : ℝ} {β : ℕ → ℝ}
    {h N M d T : ℕ} {μ : Finset X → ℝ}
    (node : IntrinsicRawPreparedLayer H F α C β h N M d T μ)
    (W : Finset (Survivors node.trim)) (q : ℝ)
    (hβ : ∀ j, 0 ≤ β j) (hq : 0 ≤ q)
    (hTotal : (∑ j ∈ range (d+(d+1)*Nat.log 2 T+1), β j) ≤ 1/8)
    (hLow : (1-automaticRelativeError (Fintype.card (Survivors node.trim)))*q*
      Fintype.card (Survivors node.trim) ≤ (W.card:ℝ))
    (hUp : (W.card:ℝ) < (1+automaticRelativeError (Fintype.card (Survivors node.trim)))*q*
      Fintype.card (Survivors node.trim)) :
    (3/4:ℝ)*q*Fintype.card X ≤ W.card ∧ (W.card:ℝ) ≤ (5/4:ℝ)*q*Fintype.card X := by
  have hη := raw_prepared_relative_error_le_sixteenth node hβ
  have hCut := raw_prepared_trim_le_total node (1/8) hβ hTotal
  have hCard : (Fintype.card (Survivors node.trim):ℝ) + node.trim.card = Fintype.card X := by
    exact_mod_cast card_survivors_add_card node.trim
  have hNlow : (7/8:ℝ)*Fintype.card X ≤ Fintype.card (Survivors node.trim) := by linarith
  have hNup : (Fintype.card (Survivors node.trim):ℝ) ≤ Fintype.card X := by
    linarith [show (0:ℝ) ≤ node.trim.card from Nat.cast_nonneg _]
  have hNlowQ := mul_le_mul_of_nonneg_left hNlow hq
  have hNupQ := mul_le_mul_of_nonneg_left hNup hq
  have hqn : 0 ≤ q * Fintype.card (Survivors node.trim) := mul_nonneg hq (by positivity)
  have hOrigQ : 0 ≤ q * Fintype.card X := mul_nonneg hq (by positivity)
  have hLo := mul_le_mul_of_nonneg_right (show (15/16:ℝ) ≤
    1-automaticRelativeError (Fintype.card (Survivors node.trim)) by linarith) hqn
  have hHi := mul_le_mul_of_nonneg_right (show
    1+automaticRelativeError (Fintype.card (Survivors node.trim)) ≤ (17/16:ℝ) by linarith) hqn
  constructor <;> nlinarith

#print axioms next_prepared_window_card_data
#print axioms raw_prepared_trim_le_total
#print axioms next_prepared_trim_le_total
#print axioms raw_prepared_relative_error_le_sixteenth
#print axioms raw_sample_metadata_quarter_sizes
#print axioms raw_prepared_outer_sample_quarter_sizes
end TypedTriangle.Vortex
