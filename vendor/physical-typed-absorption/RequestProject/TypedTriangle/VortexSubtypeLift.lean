/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VertexZeroExtension
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Translate the first-entry deletion made inside a sampled subtype back
to the original sampled vertex set, without changing the ambient host. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem lifted_prepared_deletion_geometry {V : Type*} [Fintype V]
    (W : Finset V) (A : Finset (Survivors (univ \ W))) :
    (liftVertexSet (univ \ W) A).card = A.card ∧
    liftVertexSet (univ \ W) A ⊆ W ∧
    (univ \ W) ∪ liftVertexSet (univ \ W) A =
      univ \ (W \ liftVertexSet (univ \ W) A) := by
  letI : DecidableEq V := Classical.decEq V
  have hsubset : liftVertexSet (univ \ W) A ⊆ W := by
    intro v hv
    have havoid := Finset.disjoint_left.mp (liftVertexSet_avoids (univ \ W) A) hv
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using havoid
  refine ⟨card_liftVertexSet (univ \ W) A, hsubset, ?_⟩
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

#print axioms lifted_prepared_deletion_geometry

/-- Nested survivors after preparation are canonically the ambient survivors
after the union of the two deleted sets. -/
def nestedPreparedSurvivorsEquiv {V : Type*} [Fintype V]
    (W : Finset V) (A : Finset (Survivors (univ \ W))) :
    Survivors A ≃ Survivors ((univ \ W) ∪ liftVertexSet (univ \ W) A) where
  toFun x := ⟨x.1.1, by
    intro hv
    rcases Finset.mem_union.mp hv with h0 | h1
    · exact x.1.2 h0
    · exact x.2 ((mem_liftVertexSet (univ \ W) A x.1).mp h1)⟩
  invFun y := ⟨⟨y.1, fun h => y.2 (Finset.mem_union_left _ h)⟩, by
    intro hy
    exact y.2 (Finset.mem_union_right _
      ((mem_liftVertexSet (univ \ W) A
        ⟨y.1, fun h => y.2 (Finset.mem_union_left _ h)⟩).mpr hy))⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro y; apply Subtype.ext; rfl

/-- Both induced hosts have identical adjacencies and labels under the
canonical nested-survivor equivalence. -/
theorem nestedPreparedHost_equiv {V I : Type*} [Fintype V]
    (H : Host V I) (W : Finset V) (A : Finset (Survivors (univ \ W)))
    (x y : Survivors A) :
    (restrictedHost (restrictedHost H (univ \ W)) A).G.Adj x y ↔
      (restrictedHost H ((univ \ W) ∪ liftVertexSet (univ \ W) A)).G.Adj
        (nestedPreparedSurvivorsEquiv W A x)
        (nestedPreparedSurvivorsEquiv W A y) := by
  rfl

theorem nestedPreparedHost_lab_equiv {V I : Type*} [Fintype V]
    (H : Host V I) (W : Finset V) (A : Finset (Survivors (univ \ W)))
    (x : Survivors A) :
    (restrictedHost (restrictedHost H (univ \ W)) A).lab x =
      (restrictedHost H ((univ \ W) ∪ liftVertexSet (univ \ W) A)).lab
        (nestedPreparedSurvivorsEquiv W A x) := by
  rfl

#print axioms nestedPreparedHost_equiv
#print axioms nestedPreparedHost_lab_equiv

end TypedTriangle.Vortex
