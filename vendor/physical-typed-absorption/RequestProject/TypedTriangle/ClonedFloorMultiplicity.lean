module
public import RequestProject.TypedTriangle.SeedCaps
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
variable {ι E : Type*} [Fintype ι] [Fintype E]

/-- Lower rounding keeps the clone resource degrees below the original scale. -/
def floorMultiplicity (p : ℝ) (φ : ι → ℝ) (i : ι) : ℕ := ⌊p * φ i⌋₊

theorem floorMultiplicity_bounds (p : ℝ) (hp : 0 ≤ p) (φ : ι → ℝ)
    (hφ : ∀ i, 0 ≤ φ i) (i : ι) :
    p * φ i - 1 ≤ (floorMultiplicity p φ i : ℝ) ∧
      (floorMultiplicity p φ i : ℝ) ≤ p * φ i := by
  have hlo := Nat.lt_floor_add_one (p * φ i)
  exact ⟨by dsimp [floorMultiplicity]; linarith,
    Nat.floor_le (mul_nonneg hp (hφ i))⟩

theorem floorMultiplicity_normalized (C n : ℝ) (hC : 0 < C) (hn : 0 < n)
    (φ : ι → ℝ) (hφ : ∀ i, 1 / (C * n) ≤ φ i) (i : ι) :
    (1 - C / n) * φ i ≤ (floorMultiplicity (n ^ 2) φ i : ℝ) / n ^ 2 ∧
      (floorMultiplicity (n ^ 2) φ i : ℝ) / n ^ 2 ≤ φ i := by
  have hφ0 : ∀ j, 0 ≤ φ j := fun j => (by positivity : (0 : ℝ) ≤ 1 / (C * n)).trans (hφ j)
  obtain ⟨hlo, hhi⟩ := floorMultiplicity_bounds (n ^ 2) (sq_nonneg n) φ hφ0 i
  have hscale : 1 ≤ C * n * φ i := by
    have hh := mul_le_mul_of_nonneg_left (hφ i) (by positivity : (0 : ℝ) ≤ C * n)
    have he : (C * n) * (1 / (C * n)) = 1 := by field_simp [ne_of_gt hC,ne_of_gt hn]
    rwa [he] at hh
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
    have he : (1 - C / n) * φ i * n ^ 2 = (n ^ 2 - C * n) * φ i := by
      field_simp [ne_of_gt hn]
      <;> ring
    rw [he]
    nlinarith only [hlo, hscale]
  · exact (div_le_iff₀ (sq_pos_of_pos hn)).mpr (by simpa only [mul_comm] using hhi)

theorem floorMultiplicity_degree_cap (P : ι → Finset E) (φ : ι → ℝ) (p : ℝ)
    (hp : 0 ≤ p) (hφ : ∀ i, 0 ≤ φ i)
    (hload : ∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) (e : E) :
    ((∑ i, if e ∈ P i then floorMultiplicity p φ i else 0 : ℕ) : ℝ) ≤ p := by
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  calc
    _ ≤ ∑ i, if e ∈ P i then p * φ i else 0 := by
      apply sum_le_sum
      intro i _
      split_ifs
      · exact (floorMultiplicity_bounds p hp φ hφ i).2
      · exact le_rfl
    _ = p * ∑ i, if e ∈ P i then φ i else 0 := by
      rw [mul_sum]
      simp only [mul_ite, mul_zero]
    _ ≤ p := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hload e) hp

theorem floorMultiplicity_codegree_cap (P : ι → Finset E) (φ : ι → ℝ) (p b : ℝ)
    (hp : 0 ≤ p) (hb : 0 ≤ b) (hφ : ∀ i, 0 ≤ φ i) (hφb : ∀ i, φ i ≤ b)
    (hlin : ∀ e f, e ≠ f → (univ.filter (fun i => e ∈ P i ∧ f ∈ P i)).card ≤ 1)
    (e f : E) (hef : e ≠ f) :
    ((∑ i, if e ∈ P i ∧ f ∈ P i then floorMultiplicity p φ i else 0 : ℕ) : ℝ) ≤ p * b := by
  let S := univ.filter (fun i => e ∈ P i ∧ f ∈ P i)
  have hcard : (S.card : ℝ) ≤ 1 := by exact_mod_cast hlin e f hef
  have hsum : (∑ i ∈ S, (floorMultiplicity p φ i : ℝ)) ≤ (S.card : ℝ) * (p * b) := by
    calc
      _ ≤ ∑ _i ∈ S, p * b := sum_le_sum (fun i _ =>
        ((floorMultiplicity_bounds p hp φ hφ i).2).trans
          (mul_le_mul_of_nonneg_left (hφb i) hp))
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hh := hsum.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hcard (mul_nonneg hp hb))
  simpa only [S, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using hh

theorem floorMultiplicity_total_cap (P : ι → Finset E) (φ : ι → ℝ) (p : ℝ)
    (hp : 0 ≤ p) (hφ : ∀ i, 0 ≤ φ i) (hP : ∀ i, (P i).Nonempty)
    (hload : ∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) :
    ((∑ i, floorMultiplicity p φ i : ℕ) : ℝ) ≤ p * Fintype.card E := by
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ i, p * φ i := sum_le_sum (fun i _ => (floorMultiplicity_bounds p hp φ hφ i).2)
    _ = p * ∑ i, φ i := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (fractional_total_mass_cap P φ hφ hP hload) hp

#print axioms floorMultiplicity_bounds
#print axioms floorMultiplicity_normalized
#print axioms floorMultiplicity_degree_cap
#print axioms floorMultiplicity_codegree_cap
#print axioms floorMultiplicity_total_cap
end TypedTriangle.WeightedClone
