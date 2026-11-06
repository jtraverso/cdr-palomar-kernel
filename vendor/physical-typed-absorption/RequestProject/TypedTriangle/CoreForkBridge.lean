/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V26.ForkNative
public import RequestProject.TypedTriangle.SparseEdgeHost
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section

/-! Discharge the returned fork interfaces from the ORIGINAL host predicates.
No physicality or diffuse seed is imposed on the induced core itself. -/

noncomputable section
open Finset Classical
namespace TypedTriangle.CoreForkBridge
variable {V I : Type*} [Fintype V]

theorem physical_to_fork {H : Host V I} {F : Set (Multiset I)}
    (hH2 : IsPhysical H F (edges H)) : S07V26.H2Phys H.G H.lab F := hH2

theorem diffuse_to_fork {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hC : 0 < C) (hH1 : IsDiffuseSeed H F C φ) :
    S07V26.H1Load H.G H.lab F := by
  refine ⟨fun T => if IsAllowed H F T then φ T else 0, ?_, ?_⟩
  · intro T
    dsimp only
    split_ifs with hT
    · exact (by positivity : (0 : ℝ) ≤ 1 / (C * Fintype.card V)).trans (hH1.1 T hT).1
    · exact le_refl _
  · intro e he
    have he' : e ∈ H.G.edgeSet := (mem_filter.mp he).2
    change (∑ T ∈ univ.filter (fun T => IsAllowed H F T ∧ e ∈ triEdges T),
      if IsAllowed H F T then φ T else 0) = 1
    have hset : univ.filter (fun T => IsAllowed H F T ∧ e ∈ triEdges T) =
        (allowed H F).filter (fun T => e ∈ triEdges T) := by
      ext T
      simp [allowed]
    rw [hset]
    calc
      _ = ∑ T ∈ (allowed H F).filter (fun T => e ∈ triEdges T), φ T := by
        apply sum_congr rfl
        intro T hT
        exact if_pos ((mem_filter.mp (mem_filter.mp hT).1).2)
      _ = 1 := hH1.2 e he'

end TypedTriangle.CoreForkBridge
