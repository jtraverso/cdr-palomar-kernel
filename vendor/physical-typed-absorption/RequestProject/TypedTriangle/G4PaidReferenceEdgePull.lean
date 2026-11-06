/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SampledForbiddenTransport
public import RequestProject.TypedTriangle.SparseEdgeDefs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

theorem paid_pull_subset_sampled_edges {V I : Type} [Fintype V]
    (H : Host V I) (W : Finset V) (Ytot : Finset (Sym2 V))
    (hYE : Ytot ⊆ edges H) :
    SampledResource.pull W Ytot ⊆
      edges (⟨H.G.comap (Subtype.val : {x // x ∈ W} → V),
        H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I) := by
  intro e he
  have heH : SampledResource.edgeLift W e ∈ edges H :=
    hYE (Finset.mem_preimage.mp he)
  induction e using Sym2.ind with
  | h u v =>
    have hh : s(u.1,v.1) ∈ edges H := by
      simpa [SampledResource.edgeLift] using heH
    have hAdj : H.G.Adj u.1 v.1 := SparseEdge.mem_edges.mp hh
    exact SparseEdge.mem_edges.mpr hAdj

#print axioms TypedTriangle.CatalogNative.paid_pull_subset_sampled_edges

end TypedTriangle.CatalogNative
