/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRawPathsNextCore
public import RequestProject.TypedTriangle.VortexRelativeRawPathsPreparedVortex
public import RequestProject.TypedTriangle.VortexPaidChildEquiv
public import RequestProject.S07V31.TerminalAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace TypedTriangle.Vortex.IntrinsicRawPathsPreparedVortex
variable {I : Type} {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
  {h N M d T m : ℕ} {a εRoute t : ℝ}

/-- The already constructed prepared next graph lies inside the future
raw core that the reference protects. -/
theorem nextPreparedEdges_subset_future {X : Type} [Fintype X]
    {H : Host X I} {μ : Finset X → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    chain.nextPreparedEdges ⊆ edges chain.preparedHost ∩ triEdges chain.nextRawWindow := by
  intro f hf
  have hRaw := chain.nextPreparedEdges_subset_raw hf
  refine mem_inter.mpr ⟨hRaw,?_⟩
  induction f using Sym2.ind with
  | _ u v =>
    have huv : chain.preparedHost.G.Adj u v := by simpa [edges] using hRaw
    exact mem_triEdges.mpr ⟨chain.nextPreparedEdges_supported _ hf _ (by simp),
      chain.nextPreparedEdges_supported _ hf _ (by simp),huv.ne⟩

/-- Future reference inclusion immediately discharges the next-edge field
of the exact paid child, on its literal window carrier. -/
theorem nextPreparedEdges_mapped_subset_child {X Y : Type} [Fintype X] [Fintype Y]
    {H : Host X I} {μ : Finset X → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (e : Survivors chain.head.trim ≃ Y) (Jraw Jchild : Host Y I)
    (hAdj : ∀u v, chain.preparedHost.G.Adj u v ↔ Jraw.G.Adj (e u) (e v))
    (hFuture : edges Jraw ∩ triEdges (chain.nextRawWindow.map e.toEmbedding) ⊆ edges Jchild) :
    chain.nextPreparedEdges.image (Sym2.map e) ⊆ edges Jchild := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
  obtain ⟨hRaw,hCore⟩ := mem_inter.mp (chain.nextPreparedEdges_subset_future hg)
  apply hFuture
  refine mem_inter.mpr ⟨?_,?_⟩
  · rw [← edges_image_equiv e chain.preparedHost Jraw hAdj]
    exact mem_image.mpr ⟨g,hRaw,rfl⟩
  · rw [triEdges_embedding]
    exact mem_image.mpr ⟨g,hCore,rfl⟩

/-- The future raw sample has the same relative size bound that was
proved for that sample, including in the terminal case. -/
theorem nextRawWindow_card_le {X : Type} [Fintype X]
    {H : Host X I} {μ : Finset X → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (hq : 0 ≤ q) (metadata : chain.HasRelativeWindows) :
    (chain.nextRawWindow.card : ℝ) ≤ 2*q*Fintype.card (Survivors chain.head.trim) := by
  cases chain with
  | terminal node upper =>
    simp only [nextRawWindow,card_empty,Nat.cast_zero]
    positivity
  | descend node W lower shrink route paths intermediate next_index tail =>
    exact metadata.1.size_upper.le

/-- Protecting the future raw clique consumes only the number of its
vertices at each parent root, even after lifting from the prepared window. -/
theorem future_core_lift_degree_le {X : Type} [Fintype X]
    (W : Finset X) (E : Finset (Sym2 {v // v ∈ W}))
    (U : Finset {v // v ∈ W}) :
    letI : DecidableEq {v // v ∈ W} := Classical.decEq _
    ∀v, SparseEdge.degIn (SampledResource.lift W (E ∩ triEdges U)) v ≤ U.card := by
  letI : DecidableEq {v // v ∈ W} := Classical.decEq _
  let ι : {v // v ∈ W} ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  have hSub : SampledResource.lift W (E ∩ triEdges U) ⊆ triEdges (U.map ι) := by
    rw [triEdges_embedding]
    exact Finset.image_subset_image inter_subset_right
  intro v
  have hMono : SparseEdge.degIn (SampledResource.lift W (E ∩ triEdges U)) v ≤
      SparseEdge.degIn (triEdges (U.map ι)) v :=
    card_le_card (filter_subset_filter _ hSub)
  have hCore : SparseEdge.degIn (triEdges (U.map ι)) v ≤ (U.map ι).card :=
    S07V31.degIn_triEdges_le _ v
  simpa only [card_map] using hMono.trans hCore

#print axioms nextPreparedEdges_subset_future
#print axioms nextPreparedEdges_mapped_subset_child
#print axioms future_core_lift_degree_le
#print axioms nextRawWindow_card_le
end TypedTriangle.Vortex.IntrinsicRawPathsPreparedVortex
