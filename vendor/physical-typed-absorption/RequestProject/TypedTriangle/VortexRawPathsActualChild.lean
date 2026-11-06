/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRawPathsWindowEquiv
public import RequestProject.TypedTriangle.VortexPaidChildEquiv
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open IntrinsicRawPathsPreparedVortex

private theorem holes_change_decEq {X : Type} [Fintype X]
    (R E : Finset (Sym2 X)) (v : X) (b : ℝ)
    (d₁ d₂ : DecidableEq (Sym2 X))
    (hBound : (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₁) R E) v : ℝ) ≤ b) :
    (SparseEdge.degIn
      (@SDiff.sdiff _ (@Finset.instSDiff _ d₂) R E) v : ℝ) ≤ b := by
  cases Subsingleton.elim d₁ d₂
  exact hBound

/-- Convert an actually paid full-window child to the exact tail state and
basal partition required by the varying-dimension recursion. -/
theorem raw_paths_actual_child_of_window_paid_child
    {X I : Type} [Fintype X] {F : Set (Multiset I)}
    {α₀ q C : ℝ} {β : ℕ → ℝ} {h N M d T m : ℕ} {a εRoute t : ℝ}
    (Hraw Hactual : Host X I) (W : Finset X)
    (μ : Finset (Survivors (univ \ W)) → ℝ)
    (tail : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t
      (restrictedHost Hraw (univ \ W)) μ) :
    letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
    ∀ Cactual αactual ζState : ℝ,
    Hactual.G ≤ Hraw.G → Hactual.lab = Hraw.lab →
    embeddedEdges (nextPreparedEmbedding W tail.head.trim)
      (edges tail.preparedHost) ⊆ edges Hactual →
    let ι := nextPreparedEmbedding W tail.head.trim
    let e := embeddingWindowEquiv ι
    let Wfull := embeddingWindow ι
    letI : DecidableEq {y // y ∈ Wfull} := Classical.decEq _
    let JW := embeddingWindowHost ι Hactual
    ∀ (Jchild : Host {y // y ∈ Wfull} I) (ψ : Finset {y // y ∈ Wfull} → ℝ),
      Jchild.G ≤ JW.G → Jchild.lab = JW.lab →
      IsDiffuseSeed Jchild F Cactual ψ → IsPhysical Jchild F (edges Jchild) →
      CommonNbrCond Jchild F αactual → CleanHingeCond Jchild F αactual h →
      (∀ v, (SparseEdge.degIn (edges JW \ edges Jchild) v : ℝ) ≤
        ζState*Fintype.card {y // y ∈ Wfull}) →
      (tail.nextPreparedEdges.image (Sym2.map e) ⊆ edges Jchild) →
      Basal Hactual F (edges Hactual \ SampledResource.lift Wfull (edges Jchild)) →
      ∃ child : ActualState tail Cactual αactual ζState,
      ∃ P : Finset (Sym2 X), Basal Hactual F P ∧
        Disjoint P (embeddedEdges ι (edges child.host)) ∧
        edges Hactual = P ∪ embeddedEdges ι (edges child.host) := by
  letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
  intro Cactual αactual ζState hActual hLabels hPreserved ι e Wfull
  letI : DecidableEq {y // y ∈ Wfull} := Classical.decEq _
  intro JW Jchild ψ hJle hJlab hSeed hPhys h3 hClean hHole hNext hBasal
  have hRawBase : ∀u v, tail.preparedHost.G.Adj u v ↔ Hraw.G.Adj (ι u) (ι v) :=
    fun _ _ => Iff.rfl
  have hRawLabels : ∀u, tail.preparedHost.lab u = Hactual.lab (ι u) := by
    intro u
    rw [hLabels]
    rfl
  have hWindow := preserved_window_host_equiv ι tail.preparedHost Hraw Hactual
    hRawBase hActual hPreserved hRawLabels
  have hRawAdj : ∀ u v, tail.preparedHost.G.Adj u v ↔ JW.G.Adj (e u) (e v) := hWindow.1
  have hRawLab : ∀ u, tail.preparedHost.lab u = JW.lab (e u) := hWindow.2
  let Jnested := pullEquivHost e Jchild
  have hChildAdj : ∀u v, Jnested.G.Adj u v ↔ Jchild.G.Adj (e u) (e v) := fun _ _ => Iff.rfl
  have hImageEdges : (edges Jnested).image (Sym2.map e) = edges Jchild :=
    edges_image_equiv e Jnested Jchild hChildAdj
  obtain ⟨hSeedN,hPhysN,h3N,hCleanN⟩ :=
    paid_child_pull_equiv e Jchild F Cactual αactual h ψ hSeed hPhys h3 hClean
  have hNextN : tail.nextPreparedEdges ⊆ edges Jnested := by
    intro f hf
    have hmap : Sym2.map e f ∈ (edges Jnested).image (Sym2.map e) := by
      rw [hImageEdges]
      exact hNext (mem_image.mpr ⟨f,hf,rfl⟩)
    obtain ⟨g,hg,hgf⟩ := mem_image.mp hmap
    have heq : g = f := Sym2.map.injective e.injective hgf
    exact heq ▸ hg
  have hHolesN : ∀v, (SparseEdge.degIn (edges tail.preparedHost \ edges Jnested) v : ℝ) ≤
      ζState*Fintype.card (Survivors tail.head.trim) := by
    intro v
    have hh := paid_child_holes_pull_equiv e tail.preparedHost JW Jchild ζState hRawAdj hHole v
    exact holes_change_decEq (edges tail.preparedHost) (edges Jnested) v
      (ζState*Fintype.card (Survivors tail.head.trim))
      (@Sym2.instDecidableEq _ (Classical.decEq _)) inferInstance hh
  let child : ActualState tail Cactual αactual ζState := {
    host := Jnested
    graph_le := fun u v huv => (hRawAdj u v).2 (hJle huv)
    labels := by
      funext u
      change Jchild.lab (e u) = tail.preparedHost.lab u
      rw [hJlab]
      exact (hRawLab u).symm
    seed := equivSeed e ψ
    diffuse := hSeedN
    physical := hPhysN
    common := h3N
    clean := hCleanN
    next_edges := hNextN
    holes := hHolesN }
  have hLift : SampledResource.lift Wfull (edges Jchild) =
      embeddedEdges ι (edges Jnested) := by
    have hMap : ∀g, SampledResource.edgeLift Wfull (Sym2.map e g) = Sym2.map ι g := by
      intro g
      induction g using Sym2.ind with
      | _ u v => rfl
    ext f
    constructor
    · intro hf
      obtain ⟨g,hg,hgf⟩ := mem_image.mp hf
      rw [← hImageEdges] at hg
      obtain ⟨b,hb,hbg⟩ := mem_image.mp hg
      exact mem_image.mpr ⟨b,hb,
        ((hMap b).symm.trans (congrArg (SampledResource.edgeLift Wfull) hbg)).trans hgf⟩
    · intro hf
      obtain ⟨g,hg,hgf⟩ := mem_image.mp hf
      refine mem_image.mpr ⟨Sym2.map e g,?_,(hMap g).trans hgf⟩
      rw [← hImageEdges]
      exact mem_image.mpr ⟨g,hg,rfl⟩
  let Echild := embeddedEdges ι (edges Jnested)
  have hSubset : Echild ⊆ edges Hactual := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    induction g using Sym2.ind with
    | _ u v =>
      have huv : Jnested.G.Adj u v := by simpa [edges] using hg
      have hxy := hJle huv
      change Hactual.G.Adj (ι u) (ι v) at hxy
      simpa [edges] using hxy
  refine ⟨child,edges Hactual \ Echild,?_,?_,?_⟩
  · change Basal Hactual F (edges Hactual \ embeddedEdges ι (edges Jnested))
    rw [← hLift]
    exact hBasal
  · change Disjoint (edges Hactual \ Echild) Echild
    exact disjoint_left.mpr (fun _ he heChild => (mem_sdiff.mp he).2 heChild)
  · change edges Hactual = (edges Hactual \ Echild) ∪ Echild
    exact (Finset.sdiff_union_of_subset hSubset).symm

#print axioms raw_paths_actual_child_of_window_paid_child
end TypedTriangle.Vortex
