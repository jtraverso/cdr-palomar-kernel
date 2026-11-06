/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeApproxNibble
public import RequestProject.TypedTriangle.Seed
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.NativeNibble
open PartitionedTriangleAbsorption

/-- A raw host with near-unit loads has a real typed packing leaving small
degree at EVERY vertex, even when its indicator is outside its integer lattice. -/
theorem packing_of_approx_weights (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (φ : Finset V → ℝ), n₀ ≤ Fintype.card V →
        (∀ T, IsAllowed H F T → 0 ≤ φ T ∧ φ T ≤ b/Fintype.card V) →
        (∀ e ∈ edges H, |bdry H F φ e-1| ≤ ε) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧
          ∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤
            η*Fintype.card V := by
  obtain ⟨ε,hε,n₀,hn⟩ := Nibble.nibble_packing_near b η hb hη hη1
  refine ⟨ε,hε,n₀,?_⟩
  intro V I _ H F φ hcard hφ hload
  classical
  obtain ⟨P,hP,hdeg⟩ := hn V hcard (allowed H F).card (system H F) (edges H)
    (weights H F φ) (fun i => triEdges_subset_edges (isAllowed_of_mem_allowed (system_mem H F i)))
    (fun i => (hφ _ (isAllowed_of_mem_allowed (system_mem H F i))).1)
    (fun i => (hφ _ (isAllowed_of_mem_allowed (system_mem H F i))).2)
    (fun e he => by
      rw [system_load]
      simpa only [bdry_eq_sum_triOn,triOn] using hload e he)
  refine ⟨packed H F P,packed_isPacking H F P hP,?_⟩
  rw [packed_edges] at hdeg
  exact hdeg

end TypedTriangle.NativeNibble
