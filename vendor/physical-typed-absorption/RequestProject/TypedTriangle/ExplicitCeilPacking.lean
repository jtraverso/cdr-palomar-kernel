/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitDiffuseWeightedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone.Explicit

/-- One-sided extraction permits zero fractional coefficients. The additive
rounding cost is paid by geometric candidate counts, without a weight floor. -/
theorem ceil_matching_lower_explicit (C c η : ℝ) (q : ℕ)
    (hC : 1 ≤ C) (hc : 0 < c) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ n : ℝ, cloneCut C c η (Pseudorandom.Explicit.egjCut (1/4) 4) q ≤ n →
      ∀ (E ι κ : Type) [Fintype E] [Fintype ι] [Fintype κ]
        (P : ι → Finset E) (φ : ι → ℝ) (W : κ → ι → ℝ),
      (Fintype.card E : ℝ) ≤ n^2 → (Fintype.card ι : ℝ) ≤ n^3 →
      (∀ i, (P i).card = 3) → (∀ i, 0 ≤ φ i ∧ φ i ≤ C/n) →
      (∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) →
      (∀ e, ((univ.filter fun i => e ∈ P i).card : ℝ) ≤ n) →
      (∀ e f, e ≠ f → (univ.filter fun i => e ∈ P i ∧ f ∈ P i).card ≤ 1) →
      (Fintype.card κ : ℝ) ≤ n^q →
      (∀ k i, 0 ≤ W k i ∧ W k i ≤ 1) →
      (∀ k, c*n ≤ ∑ i, φ i*W k i) →
      ∃ Q : Finset ι, (Q : Set ι).PairwiseDisjoint P ∧
        ∀ k, (1-η)*(∑ i, φ i*W k i) ≤ ∑ i ∈ Q, W k i := by
  intro n hn E ι κ _ _ _ P φ W hE hι hcard hφ hload hinc hlin hκ hW hmass
  obtain ⟨hn1,hD₀,hD1,hcode,hsize,htests,hmasscap,herror⟩ :=
    clone_numerics_explicit C c η (Pseudorandom.Explicit.egjCut (1/4) 4) q
      (by linarith) hc hη n hn
  have hnpos : 0 < n := by linarith
  let D := n^2+C*n
  let p := n^2
  let mult := seedMultiplicity p φ
  have hp : 0 ≤ p := sq_nonneg n
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hφ0 : ∀ i, 0 ≤ φ i := fun i => (hφ i).1
  have hP : ∀ i, (P i).Nonempty := fun i => card_pos.mp (by rw [hcard]; norm_num)
  have hdeg : ∀ e, ((∑ i, if e ∈ P i then mult i else 0 : ℕ) : ℝ) ≤ D := by
    intro e
    let w : ι → ℝ := fun i => if e ∈ P i then 1 else 0
    have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; split_ifs <;> norm_num
    have hh := (multiplicity_mass_bounds p hp φ w hφ0 hw).2
    have hs : ∑ i, φ i*w i ≤ 1 := by simpa [w] using hload e
    have hi : ∑ i, w i ≤ n := by simpa [w, sum_filter] using hinc e
    have hm : p*(∑ i, φ i*w i) ≤ p := by simpa using mul_le_mul_of_nonneg_left hs hp
    have hCn : n ≤ C*n := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hnpos.le
    have hh' : (∑ i, (mult i : ℝ)*w i) ≤ D := by dsimp [D,p] at *; linarith
    simpa [w, mult] using hh'
  have hcod : ∀ e f, e ≠ f →
      ((∑ i, if e ∈ P i ∧ f ∈ P i then mult i else 0 : ℕ) : ℝ) ≤ D^((3:ℝ)/4) := by
    intro e f hef
    have hh := multiplicity_codegree_cap P φ p (C/n) hp (by positivity)
      hφ0 (fun i => (hφ i).2) hlin e f hef
    have he : p*(C/n)+1 = C*n+1 := by dsimp [p]; field_simp
    rw [he] at hh
    exact hh.trans hcode
  have htotal : ((∑ i, mult i : ℕ) : ℝ) ≤ Real.exp (D^(((1:ℝ)/3200)^2)) := by
    have hh := (multiplicity_mass_bounds p hp φ (fun _ => 1) hφ0 (by simp)).2
    simp only [mul_one, sum_const, nsmul_eq_mul, card_univ] at hh
    have hs := fractional_total_mass_cap P φ hφ0 hP hload
    have hm := mul_le_mul_of_nonneg_left (hs.trans hE) hp
    have hCn : n^3 ≤ (C*n)*n^2 := by
      have hh := mul_le_mul_of_nonneg_right hC (show 0 ≤ n^3 by positivity)
      nlinarith
    have ht : ((∑ i, mult i : ℕ) : ℝ) ≤ D*n^2 := by
      have hh' : ((∑ i, mult i : ℕ) : ℝ) ≤ p*(∑ i, φ i)+Fintype.card ι := by
        simpa only [mult, Nat.cast_sum] using hh
      dsimp [D,p] at *
      nlinarith
    exact ht.trans hsize
  have hMatch := matching_from_integer_multiplicities_explicit
    (1/4) (by norm_num) (by norm_num) 3 (by norm_num)
  norm_num at hMatch htotal htests
  obtain ⟨copies,hcopies,hweights⟩ := hMatch D hD₀ hD1 E ι P mult hcard
    (fun e => by simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using hdeg e)
    (fun e f hef => by simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using hcod e f hef)
    (by simpa only [Nat.cast_sum] using htotal) κ W
    (fun k i => (hW k i).1) (hκ.trans htests)
  obtain ⟨Q,hQ,hQC⟩ := project_matching P mult hP copies hcopies
  refine ⟨Q,hQ,?_⟩
  intro k
  have hS : 0 ≤ ∑ i, φ i*W k i := sum_nonneg fun i _ => mul_nonneg (hφ0 i) (hW k i).1
  have hlo := (multiplicity_mass_bounds p hp φ (W k) hφ0 (fun i => (hW k i).1)).1
  have hmatch := hweights k (by
    intro i _
    calc W k i * D^((5:ℝ)/4) ≤ D^((5:ℝ)/4) :=
        by simpa using mul_le_mul_of_nonneg_right (hW k i).2 (Real.rpow_nonneg hDpos.le _)
      _ ≤ p*(c*n) := hmasscap
      _ ≤ p*(∑ j, φ j*W k j) := mul_le_mul_of_nonneg_left (hmass k) hp
      _ ≤ ∑ j, (mult j : ℝ)*W k j := hlo)
  rw [← hQC (W k)] at hmatch
  have hu0 : 0 ≤ D^(-((1:ℝ)/3200)) := Real.rpow_nonneg hDpos.le _
  have hz0 : 0 ≤ C*n/D := by positivity
  have he : D^(-((1:ℝ)/3200))+2*(C*n/D) ≤ η := by
    convert herror using 1 <;> dsimp [D] <;> ring
  have hu1 : D^(-((1:ℝ)/3200)) ≤ 1 := by linarith only [he,hη1,hz0]
  have hnorm : p/D = 1-C*n/D := by dsimp [p,D]; field_simp; ring
  have hfactor : 1-η ≤ (1-D^(-((1:ℝ)/3200)))*(p/D) := by
    rw [hnorm]
    nlinarith only [he,mul_nonneg hu0 hz0,hz0]
  have hscaled := mul_le_mul_of_nonneg_right hfactor hS
  have hlod := div_le_div_of_nonneg_right hlo hDpos.le
  have hmult := mul_le_mul_of_nonneg_left hlod (by linarith : 0 ≤ 1-D^(-((1:ℝ)/3200)))
  have hlowmatch := (abs_le.mp hmatch).1
  have he : (p*(∑ i, φ i*W k i))/D = (p/D)*(∑ i, φ i*W k i) := by ring
  rw [he] at hmult
  nlinarith

#print axioms ceil_matching_lower_explicit
end TypedTriangle.WeightedClone.Explicit
