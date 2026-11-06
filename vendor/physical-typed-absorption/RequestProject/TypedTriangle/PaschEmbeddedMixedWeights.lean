module
public import RequestProject.TypedTriangle.PaschEmbeddingStatistics
public import RequestProject.TypedTriangle.PaschPaddedMixedWeights
public import RequestProject.S07V42.Transport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone
variable {X V : Type*} [DecidableEq X] [DecidableEq V]

theorem baseMatching_mapConfiguration_iff (e : X ↪ V) (S : Finset (Finset X)) :
    BaseMatching triEdges (mapConfiguration e S) ↔ BaseMatching triEdges S := by
  have hEdges (T : Finset X) : triEdges (T.map e) =
      (triEdges T).map (S07V42.emb2 e.injective) := S07V42.triEdges_map e.injective T
  constructor
  · intro h A hA B hB hAB
    have hne : A.map e ≠ B.map e := fun he => hAB (Finset.map_injective e he)
    have hh := h (mem_mapConfiguration.mpr ⟨A,hA,rfl⟩)
      (mem_mapConfiguration.mpr ⟨B,hB,rfl⟩) hne
    change Disjoint (triEdges (A.map e)) (triEdges (B.map e)) at hh
    rw [hEdges,hEdges] at hh
    exact (disjoint_map _).mp hh
  · intro h A hA B hB hAB
    obtain ⟨A',hA',rfl⟩ := mem_mapConfiguration.mp hA
    obtain ⟨B',hB',rfl⟩ := mem_mapConfiguration.mp hB
    have hne : A' ≠ B' := fun he => hAB (congrArg (fun T => T.map e) he)
    change Disjoint (triEdges (A'.map e)) (triEdges (B'.map e))
    rw [hEdges,hEdges]
    exact (disjoint_map _).mpr (h hA' hB' hne)

theorem mapConfiguration_subset_iff (e : X ↪ V) (R S : Finset (Finset X)) :
    mapConfiguration e R ⊆ mapConfiguration e S ↔ R ⊆ S := by
  unfold mapConfiguration
  exact map_subset_map

theorem mapConfiguration_sdiff (e : X ↪ V) (S R : Finset (Finset X)) :
    mapConfiguration e (S \ R) = mapConfiguration e S \ mapConfiguration e R := by
  unfold mapConfiguration
  exact map_sdiff S R

def embeddedCompletionWeight (e : X ↪ V) (B : Finset (Finset V))
    (S : Finset (Finset X)) : ℝ := completionWeight B (mapConfiguration e S)

theorem embeddedCompletionWeight_nonneg (e : X ↪ V) (B : Finset (Finset V))
    (S : Finset (Finset X)) : 0 ≤ embeddedCompletionWeight e B S :=
  completionWeight_nonneg B _

variable [Fintype V]

theorem embeddedCompletionWeight_clean (e : X ↪ V) (B : Finset (Finset V))
    (S : Finset (Finset X)) (hS : ¬ BaseMatching triEdges S) :
    embeddedCompletionWeight e B S = 0 := by
  exact completionWeight_zero_of_not_matching B (mapConfiguration e S)
    (fun h => hS ((baseMatching_mapConfiguration_iff e S).mp h))

variable [Fintype X]

def pullTriangle (e : X ↪ V) (T : Finset V) : Finset X :=
  univ.filter (fun x => e x ∈ T)

def liftTriangleWeight (e : X ↪ V) (μ : Finset X → ℝ) (T : Finset V) : ℝ :=
  μ (pullTriangle e T)

theorem pullTriangle_map (e : X ↪ V) (S : Finset X) : pullTriangle e (S.map e) = S := by
  ext x
  simp only [pullTriangle,mem_filter,mem_univ,true_and]
  exact mem_map' e

theorem liftTriangleWeight_map (e : X ↪ V) (μ : Finset X → ℝ) (S : Finset X) :
    liftTriangleWeight e μ (S.map e) = μ S := by
  rw [liftTriangleWeight,pullTriangle_map]

theorem prod_liftTriangleWeight_mapConfiguration (e : X ↪ V) (μ : Finset X → ℝ)
    (S : Finset (Finset X)) :
    (∏ T ∈ mapConfiguration e S, liftTriangleWeight e μ T) = ∏ T ∈ S, μ T := by
  rw [mapConfiguration,prod_map]
  change (∏ T ∈ S, liftTriangleWeight e μ (T.map e)) = _
  simp only [liftTriangleWeight_map]

/-- The ambient completion weight is reindexed exactly on child tuples. -/
theorem mixedMass_embedding (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (μ : Finset X → ℝ) (ℓ : ℕ) :
    mixedMass (mapConfiguration e A) B (liftTriangleWeight e μ) ℓ =
      ∑ S ∈ A.powersetCard ℓ, embeddedCompletionWeight e B S * ∏ T ∈ S, μ T := by
  unfold mixedMass
  rw [mapConfiguration,powersetCard_map,sum_map]
  apply sum_congr rfl
  intro S _
  change completionWeight B (mapConfiguration e S)*
    (∏ T ∈ mapConfiguration e S, liftTriangleWeight e μ T) = _
  rw [prod_liftTriangleWeight_mapConfiguration]
  rfl

/-- Fixed child blocks transport before taking partial clone degrees;
only unfixed blocks contribute diffuse coefficients. -/
theorem mixedDegree_embedding (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (μ : Finset X → ℝ) (ℓ : ℕ) (R : Finset (Finset X)) :
    mixedDegree (mapConfiguration e A) B (liftTriangleWeight e μ) ℓ (mapConfiguration e R) =
      ∑ S ∈ (A.powersetCard ℓ).filter (fun S => R ⊆ S),
        embeddedCompletionWeight e B S * ∏ T ∈ S \ R, μ T := by
  unfold mixedDegree
  change (∑ S ∈ ((A.map (Finset.mapEmbedding e).toEmbedding).powersetCard ℓ).filter
      (fun S => mapConfiguration e R ⊆ S),
      completionWeight B S * ∏ T ∈ S \ mapConfiguration e R, liftTriangleWeight e μ T) = _
  rw [powersetCard_map,filter_map,sum_map]
  change (∑ S ∈ (A.powersetCard ℓ).filter (fun S => mapConfiguration e R ⊆ mapConfiguration e S),
      completionWeight B (mapConfiguration e S)*
        ∏ T ∈ mapConfiguration e S \ mapConfiguration e R, liftTriangleWeight e μ T) = _
  have hFilter : (A.powersetCard ℓ).filter (fun S => mapConfiguration e R ⊆ mapConfiguration e S) =
      (A.powersetCard ℓ).filter (fun S => R ⊆ S) := by
    apply filter_congr
    intro S _
    exact mapConfiguration_subset_iff e R S
  rw [hFilter]
  apply sum_congr rfl
  intro S _
  rw [←mapConfiguration_sdiff,prod_liftTriangleWeight_mapConfiguration]
  rfl

#print axioms baseMatching_mapConfiguration_iff
#print axioms mapConfiguration_subset_iff
#print axioms mapConfiguration_sdiff
#print axioms embeddedCompletionWeight_nonneg
#print axioms embeddedCompletionWeight_clean
#print axioms pullTriangle_map
#print axioms liftTriangleWeight_map
#print axioms prod_liftTriangleWeight_mapConfiguration
#print axioms mixedMass_embedding
#print axioms mixedDegree_embedding
end TypedTriangle.Pasch
