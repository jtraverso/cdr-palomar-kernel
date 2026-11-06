/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicRawPathsPreparedVortex
public import RequestProject.TypedTriangle.VortexEmbeddedPaidAssembly
public import RequestProject.TypedTriangle.VortexPhysicalEmbedding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

/-- The literal two-val embedding of the next prepared window. -/
def nextPreparedEmbedding {X : Type} [Fintype X]
    (W : Finset X) (B : Finset (Survivors (univ \ W))) : Survivors B ↪ X :=
  (survivingVertexEmbedding B).trans (survivingVertexEmbedding (univ \ W))

namespace IntrinsicRawPathsPreparedVortex
variable {I : Type} {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
  {h N M d T m : ℕ} {a εRoute t : ℝ}

/-- The actual first prepared node of this finite raw chain. -/
def head {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    IntrinsicRawPreparedLayer H F α₀ C β h N M d T μ :=
  match chain with
  | .terminal node _ => node
  | .descend node _ _ _ _ _ _ _ _ => node

def preparedHost {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    Host (Survivors chain.head.trim) I := restrictedHost H chain.head.trim

/-- Concrete terminal support expressed in the current prepared vertex type. -/
def terminalWindow {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    Finset (Survivors chain.head.trim) :=
  match chain with
  | .terminal _ _ => univ
  | .descend node W _ _ _ _ _ _ tail =>
      letI : DecidableEq (Survivors node.trim) := Classical.decEq _
      (terminalWindow tail).map (nextPreparedEmbedding W tail.head.trim)

/-- Raw edges that the current actual host must preserve literally. -/
def nextPreparedEdges {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    Finset (Sym2 (Survivors chain.head.trim)) :=
  match chain with
  | .terminal _ _ => ∅
  | .descend node W _ _ _ _ _ _ tail =>
      letI : DecidableEq (Survivors node.trim) := Classical.decEq _
      embeddedEdges (nextPreparedEmbedding W tail.head.trim) (edges tail.preparedHost)

theorem card_terminalWindow {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ) :
    chain.terminalWindow.card = chain.terminalOrder := by
  induction chain with
  | terminal node upper => rfl
  | descend node W lower shrink route paths intermediate next_index tail ih =>
    letI : DecidableEq (Survivors node.trim) := Classical.decEq _
    simpa only [terminalWindow,Finset.card_map,terminalOrder] using ih

/-- Technical state for the paid consumer. All geometric and H1 constants
are uniform parameters; the next prepared raw graph is retained exactly. -/
structure ActualState {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) where
  host : Host (Survivors chain.head.trim) I
  graph_le : host.G ≤ chain.preparedHost.G
  labels : host.lab = chain.preparedHost.lab
  seed : Finset (Survivors chain.head.trim) → ℝ
  diffuse : IsDiffuseSeed host F Cactual seed
  physical : IsPhysical host F (edges host)
  common : CommonNbrCond host F αactual
  clean : CleanHingeCond host F αactual h
  next_edges : chain.nextPreparedEdges ⊆ edges host
  holes : ∀ v, (SparseEdge.degIn (edges chain.preparedHost \ edges host) v : ℝ) ≤
    ζState * Fintype.card (Survivors chain.head.trim)

/-- Intermediate assembly interface: each actual local bank must produce
an exact basal layer and a state on the same raw tail. This is not theorem T
and its layer interface must be instantiated by the concrete bank. -/
def LocalLayers {V : Type} [Fintype V] {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) : Prop :=
  match chain with
  | .terminal _ _ => True
  | .descend node W lower shrink route paths intermediate next_index tail =>
      letI : DecidableEq (Survivors node.trim) := Classical.decEq _
      (∀ state : ActualState (.descend node W lower shrink route paths intermediate next_index tail)
          Cactual αactual ζState,
        ∃ child : ActualState tail Cactual αactual ζState,
        ∃ P : Finset (Sym2 (Survivors node.trim)),
          Basal state.host F P ∧
          Disjoint P (embeddedEdges (nextPreparedEmbedding W tail.head.trim) (edges child.host)) ∧
          edges state.host = P ∪
            embeddedEdges (nextPreparedEmbedding W tail.head.trim) (edges child.host)) ∧
        LocalLayers tail Cactual αactual ζState


#print axioms card_terminalWindow
end IntrinsicRawPathsPreparedVortex
end TypedTriangle.Vortex
