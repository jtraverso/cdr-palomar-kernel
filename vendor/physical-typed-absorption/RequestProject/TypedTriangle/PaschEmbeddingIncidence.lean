module
public import RequestProject.TypedTriangle.PaschEmbeddingStatistics
public import RequestProject.TypedTriangle.PaschEdgeAveraging
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {X V : Type*} [DecidableEq X] [DecidableEq V]

/-- Embedding the vertices preserves the pair-codegree certificate, including
pairs of ambient vertices outside the embedded carrier. -/
theorem pairCodegreeBound_mapConfiguration (e : X ↪ V) (R : Finset (Finset X)) (L : ℕ)
    (hR : PairCodegreeBound R L) : PairCodegreeBound (mapConfiguration e R) L := by
  intro a b hab
  by_cases hRange : (∃ x, e x = a) ∧ (∃ y, e y = b)
  · obtain ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩ := hRange
    have hxy : x ≠ y := fun he => hab (congrArg e he)
    have hFilter : (mapConfiguration e R).filter (fun T => e x ∈ T ∧ e y ∈ T) =
        mapConfiguration e (R.filter (fun T => x ∈ T ∧ y ∈ T)) := by
      unfold mapConfiguration
      rw [filter_map]
      congr 1
      apply filter_congr
      intro T _
      change (e x ∈ T.map e ∧ e y ∈ T.map e) ↔ (x ∈ T ∧ y ∈ T)
      exact and_congr (mem_map' e) (mem_map' e)
    rw [hFilter,mapConfiguration,card_map]
    exact hR x y hxy
  · have hEmpty : (mapConfiguration e R).filter (fun T => a ∈ T ∧ b ∈ T) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hTR,ha,hb⟩ := mem_filter.mp hT
      obtain ⟨S,hSR,rfl⟩ := mem_mapConfiguration.mp hTR
      obtain ⟨x,hx,hxa⟩ := mem_map.mp ha
      obtain ⟨y,hy,hyb⟩ := mem_map.mp hb
      exact hRange ⟨⟨x,hxa⟩,⟨y,hyb⟩⟩
    rw [hEmpty,card_empty]
    exact Nat.zero_le _

#print axioms pairCodegreeBound_mapConfiguration
end TypedTriangle.Pasch
