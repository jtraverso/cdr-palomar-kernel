/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SampleCount
public import RequestProject.TypedTriangle.RawCorePreparation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-- H3 pools sampled for all ambient pairs eliminate the exterior bad-edge
graph. The roots of a pair need not lie in the sample. -/
theorem badEdges_empty_of_sampled_pools {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (q α : ℝ) (hq : 0 < q) (hα : 0 < α)
    (hn : 0 < Fintype.card V)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 2 ≤
        ((SparseEdge.commonNbrs H.G H.lab k u v) ∩ W).card) :
    TypedTriangle.badEdges H F W ∅ = ∅ := by
  ext e
  constructor
  · intro he
    have heNo : e ∈ TypedTriangle.noThird H F W :=
      TypedTriangle.badEdges_subset_noThird W ∅ he
    obtain ⟨_, heTri, hNoThird⟩ := Finset.mem_filter.mp heNo
    obtain ⟨u,v,t,rfl,hAllowed⟩ := heTri.exists_tri
    obtain ⟨huv,hut,hvt⟩ := TypedTriangle.distinct_of_card_three hAllowed.1
    have hlabels : ({H.lab u, H.lab v, H.lab t} : Multiset I) ∈ F := by
      have h := hAllowed.2.2
      rwa [Finset.insert_val_of_notMem (by simp [huv,hut]),
        Finset.insert_val_of_notMem (by simp [hvt])] at h
    have hcount := hpool u v huv (H.lab t) hlabels
    have hpositive : 0 < ((SparseEdge.commonNbrs H.G H.lab (H.lab t) u v) ∩ W).card := by
      have hnreal : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
      have hbound : (0:ℝ) < q * α * Fintype.card V / 2 := by positivity
      exact_mod_cast lt_of_lt_of_le hbound hcount
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hpositive
    have hwW : w ∈ W := (Finset.mem_inter.mp hw).2
    have hwCommon : w ∈ TypedTriangle.commonNbrs H (H.lab t) u v := by
      simpa [TypedTriangle.commonNbrs, SparseEdge.commonNbrs] using
        (Finset.mem_inter.mp hw).1
    have hwAllowed : TypedTriangle.IsAllowed H F {u,v,w} :=
      TypedTriangle.allowed_of_commonNbr hAllowed hwCommon
    have hwThird : w ∈ TypedTriangle.thirdsOf H F s(u,v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,v,rfl,hwAllowed⟩
    exact False.elim (hNoThird w hwW hwThird)
  · intro he
    simp at he

#print axioms badEdges_empty_of_sampled_pools

end TypedTriangle.Vortex
