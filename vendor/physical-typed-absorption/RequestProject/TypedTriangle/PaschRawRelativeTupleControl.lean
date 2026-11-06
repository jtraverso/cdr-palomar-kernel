module
public import RequestProject.TypedTriangle.PaschRelativeTupleControl
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
variable {V I : Type*} [Fintype V]

/-- A linear test with zero mass or a positive linear quota has genuine
clone eligibility. The resulting estimate is relative to its original
profile mass, including the floor-rounding error. No exact load identity is used. -/
theorem relative_error_of_floor_linear_control_of_coefficients {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {C c ε : ℝ} (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card V) ≤ μ T)
    (hC : 0 < C) (hc : 0 < c) (hε : 0 ≤ ε)
    (hn : 0 < (Fintype.card V : ℝ))
    (hRound : 2*C ≤ Fintype.card V)
    (hSqrt : Real.sqrt (Fintype.card V : ℝ) ≤ c*Fintype.card V/2)
    (hρ : (((Fintype.card V : ℝ)^2)^(-egj13Epsilon)) ≤ ε)
    (hRatio : C/Fintype.card V ≤ ε)
    (P : Finset (Finset V)) (W : Finset V → ℝ)
    (hW : ∀ T, 0 ≤ W T ∧ W T ≤ 1)
    (hMass : (∑ T ∈ allowed H F, μ T*W T) = 0 ∨
      c*Fintype.card V ≤ ∑ T ∈ allowed H F, μ T*W T)
    (hControl : floorTupleTestControl (allowed H F) μ P (linearTupleWeight W) 1) :
    |(∑ T ∈ P, W T)-(∑ T ∈ allowed H F, μ T*W T)| ≤
      2*ε*(∑ T ∈ allowed H F, μ T*W T) := by
  let A := allowed H F
  let n := (Fintype.card V : ℝ)
  let φ : A → ℝ := fun i => μ i.val
  let a : A → ℝ := fun i => W i.val
  have hφ (i : A) : 1/(C*n) ≤ φ i :=
    hLow i.val (isAllowed_of_mem_allowed i.property)
  have ha (i : A) : 0 ≤ a i ∧ a i ≤ 1 := hW i.val
  have hSource : (∑ i : A, φ i*a i) = ∑ T ∈ allowed H F, μ T*W T :=
    sum_coe_sort A (fun T => μ T*W T)
  have hMass' : (∑ i : A, φ i*a i) = 0 ∨ c*n ≤ ∑ i : A, φ i*a i := by
    simpa only [hSource,n] using hMass
  have hEligible : ∀ j, 1 ≤ j → j ≤ 1 → ∀ R : Finset A, R.card = j →
      tupleExtensionMass (indexedPackets A) (floorCopies A μ n)
        (indexedTupleWeight A (linearTupleWeight W)) 1 R *
          (n^2)^((j : ℝ)+1/4) ≤
      tupleMass (indexedPackets A) (floorCopies A μ n)
        (indexedTupleWeight A (linearTupleWeight W)) 1 := by
    intro j hj1 hj R hR
    have hjEq : j = 1 := by omega
    have hR1 : R.card = 1 := hR.trans hjEq
    obtain ⟨i,rfl⟩ := card_eq_one.mp hR1
    rw [hjEq,indexed_linearTupleWeight,tupleExtensionMass_linear_singleton]
    simpa only [Nat.cast_one, floorCopies, φ, a, n] using
      floor_linear_eligible (indexedPackets A) hC hn hRound hSqrt φ a hφ ha hMass' i
  have hTest := hControl hEligible
  rw [statistic_linear,indexed_linearTupleWeight] at hTest
  simp only [pow_one] at hTest
  change |(∑ T ∈ P, W T)-
      tupleMass (indexedPackets A) (floorMultiplicity (n^2) φ) (linearTupleWeight a) 1/(n^2)| ≤
    (n^2)^(-egj13Epsilon)*
      (tupleMass (indexedPackets A) (floorMultiplicity (n^2) φ) (linearTupleWeight a) 1/(n^2)) at hTest
  rw [←normalizedLinearMass_actual] at hTest
  have hBounds := floor_linear_mass_bounds hC hn φ a hφ (fun i => (ha i).1)
  have hBias := floor_linear_mass_close hC hn φ a hφ (fun i => (ha i).1)
  have hs0 : 0 ≤ ∑ i : A, φ i*a i :=
    sum_nonneg (fun i _ => mul_nonneg ((by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hφ i)) (ha i).1)
  have hm0 : 0 ≤ normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a :=
    sum_nonneg (fun i _ => mul_nonneg (div_nonneg (Nat.cast_nonneg _) (sq_nonneg n)) (ha i).1)
  rw [←hSource]
  calc
    _ ≤ |(∑ T ∈ P, W T)-normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a|+
        |normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a-∑ i : A, φ i*a i| :=
      abs_sub_le _ _ _
    _ ≤ ε*(∑ i : A, φ i*a i)+ε*(∑ i : A, φ i*a i) :=
      add_le_add (hTest.trans (mul_le_mul hρ hBounds.2 hm0 hε))
        (hBias.trans (mul_le_mul_of_nonneg_right hRatio hs0))
    _ = _ := by ring

#print axioms relative_error_of_floor_linear_control_of_coefficients
end TypedTriangle.Pasch
