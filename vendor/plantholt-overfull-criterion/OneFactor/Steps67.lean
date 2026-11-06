/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Core67

/-!
# The staircase classes as graphs

`stairClass D G vs Bad i`: the edges of index `i` of the staircase, without the edges `v* y` for
the bad `y`. Each class is a matching (`stairClass_matching`) covering only vertices of the class
`D.cls G i` (`cover_stairClass_subset`).
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The staircase class `i`, without the bad edges at `v*`. -/
def stairClass {HS : Finset V} (D : StairData HS) (G : SimpleGraph V) (vs : V) (Bad : Finset V)
    (i : ℤ) : SimpleGraph V where
  Adj u v := D.Eplus G u v ∧ D.stair u v = i ∧ ¬ (u = vs ∧ v ∈ Bad) ∧ ¬ (v = vs ∧ u ∈ Bad)
  symm := ⟨fun u v h => ⟨h.1.symm, (StairData.stair_symm v u).trans h.2.1, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨fun v h => h.1.2.2.1.ne rfl⟩

variable {HS : Finset V} {D : StairData HS} {G : SimpleGraph V} {vs : V} {Bad : Finset V}

theorem stairClass_adj {i : ℤ} {u v : V} : (stairClass D G vs Bad i).Adj u v ↔
    D.Eplus G u v ∧ D.stair u v = i ∧ ¬ (u = vs ∧ v ∈ Bad) ∧ ¬ (v = vs ∧ u ∈ Bad) := Iff.rfl

theorem stairClass_matching (i : ℤ) : IsMatchingGraph (stairClass D G vs Bad i) :=
  fun _ _ _ ha hb => D.stair_inj ha.1 hb.1 (ha.2.1.trans hb.2.1.symm)

theorem cover_stairClass_subset (i : ℤ) : cover (stairClass D G vs Bad i) ⊆ D.cls G i := by
  intro v hv
  obtain ⟨u, hu⟩ := mem_cover.1 hv
  exact (StairData.mem_cls _ _).2 ⟨hu.1.1, u, hu.1, hu.2.1⟩

end OneFactor
