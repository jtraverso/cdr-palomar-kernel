module
public import RequestProject.TypedTriangle.PaschEmbeddedMixedWeights
public import RequestProject.TypedTriangle.PaschPaddedCloneEligibility
public import RequestProject.TypedTriangle.PaschLocalMixedEligibility
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone
variable {X V : Type*} [Fintype X] [Fintype V]

/-- Pure child mass pads an ambient exception test. The ambient bank is
kept intact even when its blocks have one vertex outside the child. -/
def embeddedPaddedWeight (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ) (S : Finset (Finset X)) : ℝ :=
  extensionMass A θ S + embeddedCompletionWeight e B S

theorem embeddedPaddedWeight_nonneg (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ)
    (hθ : ∀ T ∈ A, 0 ≤ θ T) (S : Finset (Finset X)) :
    0 ≤ embeddedPaddedWeight e A B θ S :=
  add_nonneg (extensionMass_nonneg A θ S hθ) (embeddedCompletionWeight_nonneg e B S)

theorem embeddedPaddedWeight_clean (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ) (S : Finset (Finset X))
    (hS : ¬ BaseMatching triEdges S) : embeddedPaddedWeight e A B θ S = 0 := by
  simp only [embeddedPaddedWeight,extensionMass_zero_of_not_matching A θ S hS,
    embeddedCompletionWeight_clean e B S hS,zero_add]

theorem embeddedPaddedWeight_mass (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ) (ℓ : ℕ) :
    (∑ S ∈ A.powersetCard ℓ, embeddedPaddedWeight e A B θ S * ∏ T ∈ S, θ T) =
      (Nat.choose 4 ℓ : ℝ)*target θ A +
        mixedMass (mapConfiguration e A) B (liftTriangleWeight e θ) ℓ := by
  simp only [embeddedPaddedWeight,add_mul,sum_add_distrib]
  rw [extensionMass_integrated,mixedMass_embedding]

theorem embeddedPaddedWeight_degree (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ) (ℓ : ℕ)
    (R : Finset (Finset X)) (hR : R.card ≤ ℓ) :
    (∑ S ∈ (A.powersetCard ℓ).filter (fun S => R ⊆ S),
      embeddedPaddedWeight e A B θ S * ∏ T ∈ S \ R, θ T) =
      (Nat.choose (4-R.card) (ℓ-R.card) : ℝ)*extensionMass A θ R +
        mixedDegree (mapConfiguration e A) B (liftTriangleWeight e θ) ℓ
          (mapConfiguration e R) := by
  simp only [embeddedPaddedWeight,add_mul,sum_add_distrib]
  rw [extensionMass_integrated_over_supersets A θ R ℓ hR,mixedDegree_embedding]

def embeddedPaddedFloorWeight (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (μ : Finset X → ℝ) (n : ℝ) :=
  embeddedPaddedWeight e A B (floorWeights A μ n)

theorem embedded_padded_floor_actual_mass_div (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (μ : Finset X → ℝ) (n : ℝ) (ℓ : ℕ) :
    tupleMass (indexedPackets A) (floorCopies A μ n)
      (indexedTupleWeight A (embeddedPaddedFloorWeight e A B μ n)) ℓ / (n^2)^ℓ =
      (Nat.choose 4 ℓ : ℝ)*target (floorWeights A μ n) A +
        mixedMass (mapConfiguration e A) B (liftTriangleWeight e (floorWeights A μ n)) ℓ := by
  rw [tupleMass_general_indexed_div_of_clean A (floorCopies A μ n) (n^2)
    (embeddedPaddedFloorWeight e A B μ n) ℓ (fun S _ hS =>
      embeddedPaddedWeight_clean e A B (floorWeights A μ n) S hS)]
  exact embeddedPaddedWeight_mass e A B (floorWeights A μ n) ℓ

theorem embedded_padded_floor_actual_degree_div (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (μ : Finset X → ℝ) (n : ℝ) (ℓ : ℕ)
    (R : Finset A) (hR : R.card ≤ ℓ) :
    tupleExtensionMass (indexedPackets A) (floorCopies A μ n)
      (indexedTupleWeight A (embeddedPaddedFloorWeight e A B μ n)) ℓ R / (n^2)^(ℓ-R.card) =
      (Nat.choose (4-R.card) (ℓ-R.card) : ℝ)*
        extensionMass A (floorWeights A μ n) (indexProjection A R) +
        mixedDegree (mapConfiguration e A) B (liftTriangleWeight e (floorWeights A μ n)) ℓ
          (mapConfiguration e (indexProjection A R)) := by
  rw [tupleExtensionMass_general_indexed_div_of_clean A (floorCopies A μ n) (n^2)
    (embeddedPaddedFloorWeight e A B μ n) ℓ R (fun S _ hS =>
      embeddedPaddedWeight_clean e A B (floorWeights A μ n) S hS)]
  have hh := embeddedPaddedWeight_degree e A B (floorWeights A μ n) ℓ
    (indexProjection A R) (by simpa only [indexProjection_card] using hR)
  simpa only [indexProjection_card,embeddedPaddedFloorWeight,floorWeights] using hh

#print axioms embeddedPaddedWeight_nonneg
#print axioms embeddedPaddedWeight_clean
#print axioms embeddedPaddedWeight_mass
#print axioms embeddedPaddedWeight_degree
#print axioms embedded_padded_floor_actual_mass_div
#print axioms embedded_padded_floor_actual_degree_div
end TypedTriangle.Pasch
