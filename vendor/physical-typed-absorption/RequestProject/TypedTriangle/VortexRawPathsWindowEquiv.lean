/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRawPathsPaidAssemblyBase
public import RequestProject.TypedTriangle.VortexPreservedWindowEquiv
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

/-- The image of the actual prepared child is the raw sample minus its
actual preparation trim, with no further reference trimming. -/
theorem next_prepared_window_eq {X : Type} [Fintype X]
    (W : Finset X) (B : Finset (Survivors (univ \ W))) :
    embeddingWindow (nextPreparedEmbedding W B) = W \ liftVertexSet (univ \ W) B := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    refine mem_sdiff.mpr ⟨?_,?_⟩
    · change x.val.val ∈ W
      simpa using x.val.property
    · intro hb
      have hmem : x.val ∈ B := (mem_liftVertexSet (univ \ W) B x.val).mp hb
      exact x.property hmem
  · intro hy
    obtain ⟨hyW,hyB⟩ := mem_sdiff.mp hy
    let yw : Survivors (univ \ W) := ⟨y,by simpa using hyW⟩
    have hyNotB : yw ∉ B := by
      intro hb
      exact hyB ((mem_liftVertexSet (univ \ W) B yw).mpr hb)
    exact mem_map.mpr ⟨⟨yw,hyNotB⟩,mem_univ _,rfl⟩

/-- The concrete literal two-val map identifies the prepared raw tail with
the bank frontend's induced window in the actual parent. -/
theorem next_prepared_window_host_equiv {X I : Type} [Fintype X]
    (Hraw Hactual : Host X I) (W : Finset X)
    (B : Finset (Survivors (univ \ W)))
    (hActual : Hactual.G ≤ Hraw.G) (hLabels : Hactual.lab = Hraw.lab)
    (hPreserved : embeddedEdges (nextPreparedEmbedding W B)
      (edges (restrictedHost (restrictedHost Hraw (univ \ W)) B)) ⊆ edges Hactual) :
    let J := restrictedHost (restrictedHost Hraw (univ \ W)) B
    let ι := nextPreparedEmbedding W B
    (∀ u v, J.G.Adj u v ↔
      (embeddingWindowHost ι Hactual).G.Adj (embeddingWindowEquiv ι u) (embeddingWindowEquiv ι v)) ∧
    (∀ u, J.lab u = (embeddingWindowHost ι Hactual).lab (embeddingWindowEquiv ι u)) := by
  apply preserved_window_host_equiv _ _ Hraw Hactual (fun _ _ => Iff.rfl) hActual hPreserved
  intro u
  change Hraw.lab u.val.val = Hactual.lab u.val.val
  rw [hLabels]

#print axioms next_prepared_window_eq
#print axioms next_prepared_window_host_equiv
end TypedTriangle.Vortex
