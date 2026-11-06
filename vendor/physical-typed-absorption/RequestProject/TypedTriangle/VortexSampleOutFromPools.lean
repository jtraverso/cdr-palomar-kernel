/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexSampleBadEdges
public import RequestProject.TypedTriangle.VortexRouteGoodRoot
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-- The robust routes preserve every link lattice, while the common-neighbor
pools remove every exterior bad edge. Both tests refer to the same sample. -/
def sampleOut_of_goodRoots_and_pools {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (q α : ℝ) (hq : 0 < q) (hα : 0 < α)
    (hn : 0 < Fintype.card V)
    (hgood : ∀ v, TypedTriangle.GoodRoot H F W v)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 2 ≤
        ((SparseEdge.commonNbrs H.G H.lab k u v) ∩ W).card) :
    TypedTriangle.SampleOut H F W.card 0 := by
  refine TypedTriangle.sampleOut_of_goodRoots H F W ∅ (le_refl _)
    (Finset.disjoint_empty_right _) (fun v _ _ => hgood v) ?_
  intro x
  rw [badEdges_empty_of_sampled_pools H F W q α hq hα hn hpool]
  simp [TypedTriangle.degIn]

#print axioms sampleOut_of_goodRoots_and_pools

end TypedTriangle.Vortex
