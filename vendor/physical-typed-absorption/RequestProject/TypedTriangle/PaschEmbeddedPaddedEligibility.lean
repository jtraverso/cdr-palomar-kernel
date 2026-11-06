module
public import RequestProject.TypedTriangle.PaschEmbeddedPaddedWeights
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone
variable {X V : Type*} [Fintype X] [Fintype V]

theorem embeddedPaddedWeight_mass_lower (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ) (ℓ : ℕ)
    (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3) (hθ : ∀ T ∈ A, 0 ≤ θ T)
    {c n : ℝ} (hc : 0 ≤ c) (hTarget : c*n^2 ≤ target θ A) :
    c*n^2 ≤ ∑ S ∈ A.powersetCard ℓ, embeddedPaddedWeight e A B θ S * ∏ T ∈ S, θ T := by
  rw [embeddedPaddedWeight_mass]
  have hTarget0 : 0 ≤ target θ A := (by positivity : (0 : ℝ) ≤ c*n^2).trans hTarget
  have hLift : ∀ T ∈ mapConfiguration e A, 0 ≤ liftTriangleWeight e θ T := by
    intro T hT
    obtain ⟨Q,hQ,rfl⟩ := mem_mapConfiguration.mp hT
    rw [liftTriangleWeight_map]
    exact hθ Q hQ
  have hMixed := mixedMass_nonneg (mapConfiguration e A) B (liftTriangleWeight e θ) ℓ hLift
  have hChoose : (1 : ℝ) ≤ Nat.choose 4 ℓ := by
    rcases (show ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 by omega) with rfl | rfl | rfl <;> norm_num [Nat.choose]
  nlinarith only [hTarget,hMixed,mul_le_mul_of_nonneg_right hChoose hTarget0]

theorem embeddedPaddedWeight_degree_le (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (θ : Finset X → ℝ) (C : ℝ) (L : ℕ)
    (hC : 1 ≤ C) (hn : 0 < Fintype.card X) (hA : ∀ Q ∈ A, Q.card = 3)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hBX : ∀ Q ∈ B, 2 ≤ (Q ∩ (univ : Finset X).map e).card)
    (hθ0 : ∀ T ∈ A, 0 ≤ θ T)
    (hθb : ∀ T ∈ A, θ T ≤ C/(Fintype.card X : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (R : Finset (Finset X)) (hRA : R ⊆ A) (hR1 : 1 ≤ R.card) (hRℓ : R.card ≤ ℓ) :
    (∑ S ∈ (A.powersetCard ℓ).filter (fun S => R ⊆ S),
      embeddedPaddedWeight e A B θ S * ∏ T ∈ S \ R, θ T) ≤
        (6*C^3+localMixedDegreeScale C L)*(Fintype.card X : ℝ) := by
  rw [embeddedPaddedWeight_degree e A B θ ℓ R hRℓ]
  have hExt := extensionMass_le_two_mul_cube A θ R hC (by omega) hA hRA hR1
    (by omega) hθ0 hθb
  have hExt0 := extensionMass_nonneg A θ R hθ0
  have hChoose : (Nat.choose (4-R.card) (ℓ-R.card) : ℝ) ≤ 3 := by
    rcases (show R.card = 1 ∨ R.card = 2 ∨ R.card = 3 by omega) with hR | hR | hR <;>
      rcases (show ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 by omega) with hℓ | hℓ | hℓ <;>
      norm_num [hR,hℓ]
  have hBase : (Nat.choose (4-R.card) (ℓ-R.card) : ℝ)*extensionMass A θ R ≤ 6*C^3 := by
    have hh := mul_le_mul_of_nonneg_right hChoose hExt0
    linarith only [hh,hExt]
  have hAmap : ∀ Q ∈ mapConfiguration e A, Q.card = 3 := by
    intro Q hQ
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQ
    simpa only [card_map] using hA T hT
  have hAX : ∀ Q ∈ mapConfiguration e A, Q ⊆ (univ : Finset X).map e := by
    intro Q hQ
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQ
    exact map_subset_map.mpr (subset_univ T)
  have hLift0 : ∀ Q ∈ mapConfiguration e A, 0 ≤ liftTriangleWeight e θ Q := by
    intro Q hQ
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQ
    simpa only [liftTriangleWeight_map] using hθ0 T hT
  have hLiftB : ∀ Q ∈ mapConfiguration e A,
      liftTriangleWeight e θ Q ≤ C/(((univ : Finset X).map e).card : ℝ) := by
    intro Q hQ
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQ
    simpa only [liftTriangleWeight_map,card_map,card_univ] using hθb T hT
  have hMixed := mixedDegree_le_local_scale_mul_child_order (mapConfiguration e A) B
    (liftTriangleWeight e θ) ((univ : Finset X).map e) C L (by linarith only [hC])
    (by simpa only [card_map,card_univ] using hn) hAmap hAX hL hB hBX hLift0 hLiftB
    ℓ hℓ1 hℓ3 (mapConfiguration e R)
    ((mapConfiguration_subset_iff e R A).mpr hRA)
    (by simpa only [mapConfiguration,card_map] using hR1)
    (by simpa only [mapConfiguration,card_map] using hRℓ)
  simp only [card_map,card_univ] at hMixed
  have hnR : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hn
  have hBaseN := mul_le_mul_of_nonneg_left hnR (show (0 : ℝ) ≤ 6*C^3 by positivity)
  nlinarith only [hBase,hMixed,hBaseN]

/-- Eligibility of the actual clone weight depends on child order and a
quartic function of the previous pair codegree, never on ambient order. -/
theorem embedded_padded_floor_tuple_eligible (e : X ↪ V) (A : Finset (Finset X))
    (B : Finset (Finset V)) (μ : Finset X → ℝ) (C c : ℝ) (L : ℕ)
    (hC : 1 ≤ C) (hc : 0 < c) (hn : 0 < Fintype.card X)
    (hA : ∀ Q ∈ A, Q.card = 3) (hL : PairCodegreeBound B L)
    (hB : ∀ Q ∈ B, Q.card = 3)
    (hBX : ∀ Q ∈ B, 2 ≤ (Q ∩ (univ : Finset X).map e).card)
    (hμb : ∀ T ∈ A, floorWeights A μ (Fintype.card X : ℝ) T ≤ C/(Fintype.card X : ℝ))
    (hTarget : c*(Fintype.card X : ℝ)^2 ≤ target (floorWeights A μ (Fintype.card X : ℝ)) A)
    (hScale : ((6*C^3+localMixedDegreeScale C L)/c)^2 ≤ (Fintype.card X : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (R : Finset A) (hR1 : 1 ≤ R.card) (hRℓ : R.card ≤ ℓ) :
    let n := (Fintype.card X : ℝ)
    tupleExtensionMass (indexedPackets A) (floorCopies A μ n)
      (indexedTupleWeight A (embeddedPaddedFloorWeight e A B μ n)) ℓ R *
        (n^2)^((R.card : ℝ)+1/4) ≤
      tupleMass (indexedPackets A) (floorCopies A μ n)
        (indexedTupleWeight A (embeddedPaddedFloorWeight e A B μ n)) ℓ := by
  let n := (Fintype.card X : ℝ)
  let θ := floorWeights A μ n
  let G := 6*C^3+localMixedDegreeScale C L
  have hn0 : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hG : 0 < G := by dsimp only [G,localMixedDegreeScale,mixedDegreeScale]; positivity
  have hθ0 : ∀ T ∈ A, 0 ≤ θ T := fun T _ => floorWeights_nonneg A μ n T
  have hDegree := embeddedPaddedWeight_degree_le e A B θ C L hC hn hA hL hB hBX
    hθ0 hμb ℓ hℓ1 hℓ3 (indexProjection A R) (indexProjection_subset A R)
    (by simpa only [indexProjection_card] using hR1)
    (by simpa only [indexProjection_card] using hRℓ)
  rw [embeddedPaddedWeight_degree e A B θ ℓ (indexProjection A R)
    (by simpa only [indexProjection_card] using hRℓ)] at hDegree
  simp only [indexProjection_card] at hDegree
  have hDegreeDiv := (embedded_padded_floor_actual_degree_div e A B μ n ℓ R hRℓ).trans_le hDegree
  have hActualDegree := (div_le_iff₀ (pow_pos (sq_pos_of_pos hn0) (ℓ-R.card))).mp hDegreeDiv
  have hLower := embeddedPaddedWeight_mass_lower e A B θ ℓ hℓ1 hℓ3 hθ0 hc.le hTarget
  rw [embeddedPaddedWeight_mass] at hLower
  have hMassDiv := hLower.trans_eq (embedded_padded_floor_actual_mass_div e A B μ n ℓ).symm
  have hActualMass := (le_div_iff₀ (pow_pos (sq_pos_of_pos hn0) ℓ)).mp hMassDiv
  apply tuple_eligibility_of_gamma_sqrt_at_arity (gamma := G*n) (target := c*n^2) hn0 hRℓ
  · exact hActualDegree.trans_eq (mul_comm _ _)
  · exact (mul_comm _ _).le.trans hActualMass
  · exact linear_gamma_sqrt_le_quadratic hG hc hn0 hScale

#print axioms embeddedPaddedWeight_mass_lower
#print axioms embeddedPaddedWeight_degree_le
#print axioms embedded_padded_floor_tuple_eligible
end TypedTriangle.Pasch
