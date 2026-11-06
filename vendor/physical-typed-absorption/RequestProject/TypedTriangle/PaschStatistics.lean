module
public import RequestProject.TypedTriangle.PatternStatistics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch

/-- An unoriented Pasch configuration: four linear triples on six vertices,
with each vertex incident to exactly two triples. -/
def IsPasch {V : Type*} [DecidableEq V] (S : Finset (Finset V)) : Prop :=
  S.card = 4 ∧ (∀ T ∈ S, T.card = 3) ∧ (S.biUnion id).card = 6 ∧
    (∀ v ∈ S.biUnion id, (S.filter (fun T => v ∈ T)).card = 2) ∧
      (S : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1)

instance decidableIsPasch {V : Type*} [DecidableEq V] (S : Finset (Finset V)) :
    Decidable (IsPasch S) := by unfold IsPasch; infer_instance

def configurations {V : Type*} [DecidableEq V] (D : Finset (Finset V)) : Finset (Finset (Finset V)) :=
  (D.powersetCard 4).filter IsPasch

def count {V : Type*} [DecidableEq V] (D : Finset (Finset V)) : ℕ := (configurations D).card

def weight {V : Type*} [DecidableEq V] (w : Finset (Finset V) → ℝ) (S : Finset (Finset V)) : ℝ :=
  if IsPasch S then w S else 0

def statistic {V : Type*} [DecidableEq V] (w : Finset (Finset V) → ℝ) (D : Finset (Finset V)) : ℝ :=
  PatternStatistics.statistic (weight w) 4 D

/-- Actual absolute weighted influence of a triangle, with no constant assumed. -/
def rootedInfluence {V : Type*} [DecidableEq V] (w : Finset (Finset V) → ℝ)
    (D : Finset (Finset V)) (Q : Finset V) : ℝ :=
  PatternStatistics.influence (weight w) 4 D Q

def target {V : Type*} [DecidableEq V] (μ : Finset V → ℝ) (D : Finset (Finset V)) : ℝ :=
  statistic (fun S => ∏ T ∈ S, μ T) D

def rootedCount {V : Type*} [DecidableEq V] (D : Finset (Finset V)) (Q : Finset V) : ℕ :=
  ((configurations D).filter (fun S => Q ∈ S)).card

theorem mem_configurations {V : Type*} [DecidableEq V] {D : Finset (Finset V)} {S : Finset (Finset V)} :
    S ∈ configurations D ↔ S ⊆ D ∧ S.card = 4 ∧ IsPasch S := by
  simp only [configurations, mem_filter, mem_powersetCard, and_assoc]

theorem statistic_eq_sum {V : Type*} [DecidableEq V] (w : Finset (Finset V) → ℝ) (D : Finset (Finset V)) :
    statistic w D = ∑ S ∈ configurations D, w S := by
  simp only [statistic, PatternStatistics.statistic, configurations, weight, sum_filter]

theorem count_eq_statistic_one {V : Type*} [DecidableEq V] (D : Finset (Finset V)) :
    (count D : ℝ) = statistic (fun _ => 1) D := by
  rw [statistic_eq_sum]
  simp [count]

theorem rootedInfluence_eq_sum {V : Type*} [DecidableEq V] (w : Finset (Finset V) → ℝ)
    (D : Finset (Finset V)) (Q : Finset V) :
    rootedInfluence w D Q = ∑ S ∈ (configurations D).filter (fun S => Q ∈ S), |w S| := by
  simp only [rootedInfluence, PatternStatistics.influence, configurations, sum_filter, weight]
  apply sum_congr rfl
  intro S _
  by_cases hS : IsPasch S <;> by_cases hQ : Q ∈ S <;> simp [hS,hQ]

theorem rootedCount_eq_influence_one {V : Type*} [DecidableEq V] (D : Finset (Finset V)) (Q : Finset V) :
    (rootedCount D Q : ℝ) = rootedInfluence (fun _ => 1) D Q := by
  rw [rootedInfluence_eq_sum]
  simp [rootedCount]

private theorem sdiff_irrel {A : Type*} (s t : Finset A) (d : DecidableEq A) :
    @SDiff.sdiff _ (@Finset.instSDiff _ (Classical.decEq A)) s t =
      @SDiff.sdiff _ (@Finset.instSDiff _ d) s t := by
  cases Subsingleton.elim (Classical.decEq A) d
  rfl

theorem statistic_difference_le_influences {V : Type*} [DecidableEq V]
    (w : Finset (Finset V) → ℝ) (D E : Finset (Finset V)) :
    |statistic w D - statistic w E| ≤
      (∑ Q ∈ D \ E, rootedInfluence w D Q) + ∑ Q ∈ E \ D, rootedInfluence w E Q := by
  have h := PatternStatistics.statistic_difference_le_influences (weight w) 4 D E
  simpa only [statistic, rootedInfluence, sdiff_irrel D E inferInstance,
    sdiff_irrel E D inferInstance] using h

theorem nonnegative_statistic_difference_le_max {V : Type*} [DecidableEq V]
    (w : Finset (Finset V) → ℝ) (D E : Finset (Finset V)) (hw : ∀ S, 0 ≤ w S) :
    |statistic w D - statistic w E| ≤
      max (∑ Q ∈ D \ E, rootedInfluence w D Q) (∑ Q ∈ E \ D, rootedInfluence w E Q) := by
  have hw' : ∀ S, 0 ≤ weight w S := by
    intro S
    simp only [weight]
    split_ifs
    · exact hw S
    · exact le_rfl
  have h := PatternStatistics.nonnegative_statistic_difference_le_max (weight w) 4 D E hw'
  simpa only [statistic, rootedInfluence, sdiff_irrel D E inferInstance,
    sdiff_irrel E D inferInstance] using h

theorem target_difference_le_max {V : Type*} [DecidableEq V] (μ : Finset V → ℝ)
    (D E : Finset (Finset V)) (hμ : ∀ T, 0 ≤ μ T) :
    |target μ D - target μ E| ≤
      max (∑ Q ∈ D \ E, rootedInfluence (fun S => ∏ T ∈ S, μ T) D Q)
          (∑ Q ∈ E \ D, rootedInfluence (fun S => ∏ T ∈ S, μ T) E Q) := by
  exact nonnegative_statistic_difference_le_max _ _ _ (fun S => prod_nonneg (fun T _ => hμ T))

/-- The canonical Pasch on six vertices, without choosing an orientation. -/
def sixVertexExample : Finset (Finset (Fin 6)) :=
  {{0,1,2},{0,3,4},{5,1,3},{5,2,4}}

theorem sixVertexExample_isPasch : IsPasch sixVertexExample := by decide

theorem sixVertexExample_count : count sixVertexExample = 1 := by decide

#print axioms statistic_difference_le_influences
#print axioms nonnegative_statistic_difference_le_max
#print axioms target_difference_le_max
#print axioms sixVertexExample_isPasch
#print axioms sixVertexExample_count
end TypedTriangle.Pasch
