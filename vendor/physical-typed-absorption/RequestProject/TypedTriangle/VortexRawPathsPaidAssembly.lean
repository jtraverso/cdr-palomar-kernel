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
namespace TypedTriangle.Vortex
namespace IntrinsicRawPathsPreparedVortex
variable {I : Type} {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
  {h N M d T m : ℕ} {a εRoute t : ℝ}

private theorem partition_change_instances {X I : Type}
    (H : Host X I) (P L : Finset (Sym2 X))
    (f₁ f₂ : Fintype X) (d₁ d₂ : DecidableEq (Sym2 X))
    (hEq : @edges X I f₁ H = @Union.union _ (@Finset.instUnion _ d₁) P L) :
    @edges X I f₂ H = @Union.union _ (@Finset.instUnion _ d₂) P L := by
  cases Subsingleton.elim f₁ f₂
  cases Subsingleton.elim d₁ d₂
  exact hEq

/-- Actual varying-dimension assembly over the given raw chain. Every edge
lift uses the literal two-val embedding of its prepared child. -/
theorem assemble {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) :
    letI : DecidableEq (Survivors chain.head.trim) := Classical.decEq _
    LocalLayers chain Cactual αactual ζState → ∀ state : ActualState chain Cactual αactual ζState,
    ∃ P L : Finset (Sym2 (Survivors chain.head.trim)),
      Basal state.host F P ∧ Disjoint P L ∧ edges state.host = P ∪ L ∧
      IsPhysical state.host F L ∧
      ∀ e ∈ L, ∀ v ∈ e, v ∈ chain.terminalWindow := by
  induction chain with
  | terminal node upper =>
    intro _ state
    refine ⟨∅,edges state.host,?_,by simp,by simp,state.physical,?_⟩
    · exact ⟨∅,by simp,by simp,by simp⟩
    · intro e he v hv
      exact mem_univ v
  | descend node W lower shrink route paths intermediate next_index tail ih =>
    letI : DecidableEq (Survivors node.trim) := Classical.decEq _
    intro hLayers state
    obtain ⟨child,P,hP,hDisjoint,hPartition⟩ := hLayers.1 state
    obtain ⟨Ptail,Ltail,hPtail,hTailDisjoint,hTail,hPhysical,hSupport⟩ := ih hLayers.2 child
    letI : DecidableEq (Survivors tail.head.trim) := Classical.decEq _
    let ι : Survivors tail.head.trim ↪ Survivors node.trim :=
      nextPreparedEmbedding W tail.head.trim
    have hProtected := state.next_edges
    rw [nextPreparedEdges.eq_2 node W lower shrink route paths intermediate next_index tail] at hProtected
    have hProtected' : embeddedEdges ι (edges tail.preparedHost) ⊆ edges state.host := by
      convert hProtected using 1 <;> simp only [head.eq_2,ι]
    have hAdj : ∀ u v, child.host.G.Adj u v → state.host.G.Adj (ι u) (ι v) := by
      intro u v huv
      have heRaw : s(u,v) ∈ edges tail.preparedHost :=
        SparseEdge.mem_edges.mpr (child.graph_le huv)
      have heIn : Sym2.map ι s(u,v) ∈ embeddedEdges ι (edges tail.preparedHost) :=
        mem_image.mpr ⟨s(u,v),heRaw,rfl⟩
      have heActual : Sym2.map ι s(u,v) ∈ edges state.host := hProtected' heIn
      exact SparseEdge.mem_edges.mp heActual
    have hLab : ∀ u, child.host.lab u = state.host.lab (ι u) := by
      intro u
      exact (congrFun child.labels u).trans (congrFun state.labels (ι u)).symm
    have hCombined := assemble_embedded_paid_layer child.host state.host F ι hAdj hLab
      state.physical P Ptail Ltail tail.terminalWindow hP hPartition hDisjoint
      hPtail (partition_change_instances child.host Ptail Ltail _ _ _ _ hTail) hTailDisjoint hSupport
    have hPhysicalPush := physical_embedding child.host state.host F ι hAdj hLab hPhysical
    refine ⟨P ∪ embeddedEdges ι Ptail,embeddedEdges ι Ltail,
      hCombined.1,hCombined.2.1,hCombined.2.2.1,hPhysicalPush,?_⟩
    rw [terminalWindow.eq_2 node W lower shrink route paths intermediate next_index tail]
    exact hCombined.2.2.2.2

#print axioms assemble
end IntrinsicRawPathsPreparedVortex
end TypedTriangle.Vortex
