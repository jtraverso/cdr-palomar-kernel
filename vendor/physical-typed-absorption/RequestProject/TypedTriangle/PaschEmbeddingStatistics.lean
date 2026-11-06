module
public import RequestProject.TypedTriangle.PaschEmbedding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {X V : Type*} [DecidableEq X] [DecidableEq V]

theorem mapConfiguration_injective (e : X ↪ V) : Function.Injective (mapConfiguration e) :=
  Finset.map_injective (Finset.mapEmbedding e).toEmbedding

theorem isPasch_mapConfiguration_iff (e : X ↪ V) (S : Finset (Finset X)) :
    IsPasch (mapConfiguration e S) ↔ IsPasch S := by
  refine ⟨?_,fun h => h.mapEmbedding e⟩
  intro h
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [mapConfiguration,card_map] using h.1
  · intro T hT
    have hh := h.2.1 (T.map e) (mem_mapConfiguration.mpr ⟨T,hT,rfl⟩)
    simpa only [card_map] using hh
  · simpa only [support_mapConfiguration,card_map] using h.2.2.1
  · intro x hx
    have he : e x ∈ (mapConfiguration e S).biUnion id := by
      rw [support_mapConfiguration]
      exact mem_map.mpr ⟨x,hx,rfl⟩
    have hh := h.2.2.2.1 (e x) he
    rw [filter_mapConfiguration,mapConfiguration,card_map] at hh
    exact hh
  · intro A hA B hB hAB
    have hne : A.map e ≠ B.map e := fun he => hAB (Finset.map_injective e he)
    have hh := h.2.2.2.2 (mem_mapConfiguration.mpr ⟨A,hA,rfl⟩)
      (mem_mapConfiguration.mpr ⟨B,hB,rfl⟩) hne
    simpa only [←map_inter,card_map] using hh

theorem configurations_mapConfiguration (e : X ↪ V) (P : Finset (Finset X)) :
    configurations (mapConfiguration e P) =
      (configurations P).map (Finset.mapEmbedding (Finset.mapEmbedding e).toEmbedding).toEmbedding := by
  unfold configurations
  rw [mapConfiguration,powersetCard_map,filter_map]
  congr 1
  apply filter_congr
  intro S _
  exact isPasch_mapConfiguration_iff e S

theorem count_mapConfiguration (e : X ↪ V) (P : Finset (Finset X)) :
    count (mapConfiguration e P) = count P := by
  unfold count
  rw [configurations_mapConfiguration,card_map]

/-- Tuple tests transport under an embedding as finite sets of blocks;
there is no tuple orientation or factorial in this identity. -/
theorem tuple_statistic_mapConfiguration (e : X ↪ V) (P : Finset (Finset X))
    (w : Finset (Finset V) → ℝ) (ℓ : ℕ) :
    PatternStatistics.statistic w ℓ (mapConfiguration e P) =
      PatternStatistics.statistic (fun S => w (mapConfiguration e S)) ℓ P := by
  unfold PatternStatistics.statistic
  rw [mapConfiguration,powersetCard_map,sum_map]
  rfl

theorem pasch_target_mapConfiguration (e : X ↪ V) (P : Finset (Finset X))
    (μ : Finset V → ℝ) :
    target μ (mapConfiguration e P) = target (fun T => μ (T.map e)) P := by
  unfold target
  rw [statistic_eq_sum,statistic_eq_sum,configurations_mapConfiguration,sum_map]
  apply sum_congr rfl
  intro S _
  change (∏ T ∈ S.map (Finset.mapEmbedding e).toEmbedding, μ T) = _
  rw [prod_map]
  rfl

#print axioms mapConfiguration_injective
#print axioms isPasch_mapConfiguration_iff
#print axioms configurations_mapConfiguration
#print axioms count_mapConfiguration
#print axioms tuple_statistic_mapConfiguration
#print axioms pasch_target_mapConfiguration
end TypedTriangle.Pasch
