module
public import RequestProject.TypedTriangle.ClonedFloorMultiplicity
public import RequestProject.TypedTriangle.ClonedTupleLinear
public import RequestProject.TypedTriangle.PaschEGJEligibility
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone
variable {E ι : Type*} [Fintype E] [Fintype ι]

def normalizedLinearMass (m : ι → ℕ) (p : ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, ((m i : ℝ)/p)*a i

theorem normalizedLinearMass_actual (P : ι → Finset E) (m : ι → ℕ) (p : ℝ) (a : ι → ℝ) :
    normalizedLinearMass m p a = tupleMass P m (linearTupleWeight a) 1/p := by
  rw [tupleMass_linear,sum_div]
  unfold normalizedLinearMass
  apply sum_congr rfl
  intro i _
  ring

theorem floor_linear_mass_bounds {C n : ℝ} (hC : 0 < C) (hn : 0 < n)
    (φ a : ι → ℝ) (hφ : ∀ i, 1/(C*n) ≤ φ i) (ha : ∀ i, 0 ≤ a i) :
    (1-C/n)*(∑ i, φ i*a i) ≤ normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a ∧
      normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a ≤ ∑ i, φ i*a i := by
  constructor
  · rw [mul_sum]
    apply sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right (floorMultiplicity_normalized C n hC hn φ hφ i).1 (ha i)
    simpa only [mul_assoc] using hh
  · apply sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (floorMultiplicity_normalized C n hC hn φ hφ i).2 (ha i)

theorem floor_linear_mass_close {C n : ℝ} (hC : 0 < C) (hn : 0 < n)
    (φ a : ι → ℝ) (hφ : ∀ i, 1/(C*n) ≤ φ i) (ha : ∀ i, 0 ≤ a i) :
    |normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a - (∑ i, φ i*a i)| ≤
      (C/n)*(∑ i, φ i*a i) := by
  obtain ⟨hlo,hhi⟩ := floor_linear_mass_bounds hC hn φ a hφ ha
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith only [hlo]

/-- A zero or uniformly active linear statistic is eligible at clone scale n².
This includes vertex-star tests, including the isolated-vertex branch. -/
theorem floor_linear_eligible (P : ι → Finset E) {C n d : ℝ}
    (hC : 0 < C) (hn : 0 < n) (hRound : 2*C ≤ n)
    (hSqrt : Real.sqrt n ≤ d*n/2) (φ a : ι → ℝ)
    (hφ : ∀ i, 1/(C*n) ≤ φ i) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hMass : (∑ i, φ i*a i) = 0 ∨ d*n ≤ ∑ i, φ i*a i) (i : ι) :
    a i*(n^2)^((1:ℝ)+1/4) ≤ tupleMass P (floorMultiplicity (n^2) φ) (linearTupleWeight a) 1 := by
  have hφPos (j : ι) : 0 < φ j := lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(C*n)) (hφ j)
  have hSource0 : 0 ≤ ∑ j, φ j*a j := sum_nonneg (fun j _ => mul_nonneg (hφPos j).le (ha j).1)
  let target := normalizedLinearMass (floorMultiplicity (n^2) φ) (n^2) a
  have hTarget0 : 0 ≤ target := sum_nonneg (fun j _ => mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (sq_nonneg n)) (ha j).1)
  have hBound : a i*Real.sqrt n ≤ target := by
    rcases hMass with hz | hlow
    · have hTerm := (sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (univ : Finset ι)) => mul_nonneg (hφPos j).le (ha j).1)).mp hz i (mem_univ _)
      have hai : a i = 0 := (mul_eq_zero.mp hTerm).resolve_left (ne_of_gt (hφPos i))
      simpa only [hai,zero_mul] using hTarget0
    · have hBounds := (floor_linear_mass_bounds hC hn φ a hφ (fun j => (ha j).1)).1
      have hRatio : C/n ≤ 1/2 := (div_le_iff₀ hn).mpr (by linarith only [hRound])
      have hHalf : (∑ j, φ j*a j)/2 ≤ target := by
        have hp := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-C/n by linarith only [hRatio]) hSource0
        linarith only [hp,hBounds]
      calc a i*Real.sqrt n ≤ Real.sqrt n := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha i).2 (Real.sqrt_nonneg n)
        _ ≤ d*n/2 := hSqrt
        _ ≤ target := (div_le_div_of_nonneg_right hlow (by norm_num)).trans hHalf
  have hActual : target = tupleMass P (floorMultiplicity (n^2) φ) (linearTupleWeight a) 1/(n^2) :=
    normalizedLinearMass_actual P _ _ _
  rw [hActual] at hBound
  have hh := (le_div_iff₀ (sq_pos_of_pos hn)).mp hBound
  have he : (n^2)^((1:ℝ)+1/4) = (n^2)*Real.sqrt n := by
    rw [Real.rpow_add (sq_pos_of_pos hn),Real.rpow_one,TypedTriangle.Pasch.square_rpow_quarter hn.le]
  rw [he]
  convert hh using 1 <;> ring

#print axioms normalizedLinearMass_actual
#print axioms floor_linear_mass_bounds
#print axioms floor_linear_mass_close
#print axioms floor_linear_eligible
end TypedTriangle.WeightedClone
