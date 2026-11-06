/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRawPathsPaidAssemblyBase
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.IntrinsicRawPathsPreparedVortex
variable {I : Type} {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
  {h N M d T m : ℕ} {a εRoute t : ℝ}

/-- The next raw sample is a concrete allowed choice of the protected
future vertex core; preparation only makes its actual child smaller. -/
def nextRawWindow {X : Type} [Fintype X] {H : Host X I} {μ : Finset X → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    Finset (Survivors chain.head.trim) :=
  match chain with
  | .terminal _ _ => ∅
  | .descend _ W _ _ _ _ _ _ _ => W

theorem nextPreparedEdges_subset_raw {X : Type} [Fintype X]
    {H : Host X I} {μ : Finset X → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    chain.nextPreparedEdges ⊆ edges chain.preparedHost := by
  cases chain with
  | terminal node upper => simp [nextPreparedEdges]
  | descend node W lower shrink route paths intermediate next_index tail =>
    letI : DecidableEq (Survivors node.trim) := Classical.decEq _
    letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
    intro f hf
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    induction g using Sym2.ind with
    | _ u v =>
      have huv : tail.preparedHost.G.Adj u v := by simpa [edges] using hg
      have hParent : (restrictedHost H node.trim).G.Adj
          (nextPreparedEmbedding W tail.head.trim u)
          (nextPreparedEmbedding W tail.head.trim v) := huv
      simpa [edges,preparedHost,head] using hParent

theorem nextPreparedEdges_supported {X : Type} [Fintype X]
    {H : Host X I} {μ : Finset X → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    ∀ f ∈ chain.nextPreparedEdges, ∀ v ∈ f, v ∈ chain.nextRawWindow := by
  cases chain with
  | terminal node upper => simp [nextPreparedEdges]
  | descend node W lower shrink route paths intermediate next_index tail =>
    letI : DecidableEq (Survivors node.trim) := Classical.decEq _
    letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
    intro f hf v hv
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    obtain ⟨u,hu,rfl⟩ := Sym2.mem_map.mp hv
    change u.val.val ∈ W
    simpa using u.val.property

#print axioms nextPreparedEdges_subset_raw
#print axioms nextPreparedEdges_supported
end TypedTriangle.Vortex.IntrinsicRawPathsPreparedVortex
