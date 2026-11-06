/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.FractionalPacking
public import RequestProject.TypedTriangle.SeedCaps
public import RequestProject.TypedTriangle.PackingNumerics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Filter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone

/-- Weighted nibble for an actual linear system of triples with a diffuse
fractional decomposition. All EGJ caps and rounding budgets are discharged;
the tests need only be nonnegative, bounded by one and have linear seed mass. -/
theorem diffuse_weighted_matching (C c η : ℝ) (q : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hη : 0 < η) :
    ∃ n₀ : ℝ, ∀ n : ℝ, n₀ ≤ n →
      ∀ (E ι κ : Type) [Fintype E] [Fintype ι] [Fintype κ]
        (P : ι → Finset E) (φ : ι → ℝ) (W : κ → ι → ℝ),
      (Fintype.card E:ℝ) ≤ n^2 →
      (∀ i, (P i).card = 3) →
      (∀ i, 1/(C*n) ≤ φ i ∧ φ i ≤ C/n) →
      (∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) →
      (∀ e f, e ≠ f → (univ.filter fun i => e ∈ P i ∧ f ∈ P i).card ≤ 1) →
      (Fintype.card κ:ℝ) ≤ n^q →
      (∀ k i, 0 ≤ W k i ∧ W k i ≤ 1) →
      (∀ k, c*n ≤ ∑ i, φ i*W k i) →
      ∃ Q : Finset ι, (Q : Set ι).PairwiseDisjoint P ∧
        ∀ k, |(∑ i ∈ Q, W k i)-(∑ i, φ i*W k i)| ≤ η*(∑ i, φ i*W k i) := by
  obtain ⟨D₀,hMatch⟩ := fractional_matching_of_caps (1/4) (by norm_num) (by norm_num) 3 (by norm_num)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (eventually_clone_numerics C c η D₀ q hC.le hc hη)
  refine ⟨n₀,?_⟩
  intro n hn E ι κ _ _ _ P φ W hE hcard hφ hload hlin hκ hW hmass
  obtain ⟨hn1,hD₀,hD1,hcode,hsize,htests,hmasscap,herror⟩ := hn₀ n hn
  have hnpos : 0 < n := by linarith
  have hφ₀ : ∀ i, 0 ≤ φ i := fun i => (by positivity : (0:ℝ) ≤ 1/(C*n)).trans (hφ i).1
  have hfloor : ∀ i, 1 ≤ (C*n)*φ i := by
    intro i
    have hh := mul_le_mul_of_nonneg_left (hφ i).1 (by positivity : (0:ℝ) ≤ C*n)
    have he : (C*n)*(1/(C*n))=1 := by field_simp
    rwa [he] at hh
  have hP : ∀ i, (P i).Nonempty := fun i => card_pos.mp (by rw [hcard]; norm_num)
  have hp : (0:ℝ) ≤ n^2 := sq_nonneg _
  have ha : 0 ≤ C*n := by positivity
  have hpD : n^2 ≤ n^2+C*n := le_add_of_nonneg_right ha
  have hdegree := multiplicity_degree_cap P φ (n^2) (C*n) hp ha hφ₀ hfloor hload
  have hcodegree : ∀ e f, e ≠ f →
      ((∑ i, if e ∈ P i ∧ f ∈ P i then seedMultiplicity (n^2) φ i else 0:ℕ):ℝ) ≤
        (n^2+C*n)^((3:ℝ)/4) := by
    intro e f hef
    have hh := multiplicity_codegree_cap P φ (n^2) (C/n) hp (by positivity) hφ₀
      (fun i => (hφ i).2) hlin e f hef
    have he : n^2*(C/n)+1=C*n+1 := by field_simp <;> ring
    rw [he] at hh
    exact hh.trans hcode
  have htotal := multiplicity_total_cap P φ (n^2) (C*n) hp ha hφ₀ hfloor hP hload
  have htotal' : ((∑ i, seedMultiplicity (n^2) φ i:ℕ):ℝ) ≤
      Real.exp ((n^2+C*n)^(((1:ℝ)/3200)^2)) :=
    htotal.trans ((mul_le_mul_of_nonneg_left hE (by positivity)).trans hsize)
  obtain ⟨Q,hQ,hWeights⟩ := hMatch (n^2+C*n) (n^2) (C*n) hD₀ hD1 hp hpD ha
    E ι P φ hcard hφ₀ hfloor hdegree (by norm_num at hcodegree ⊢; exact hcodegree)
      (by norm_num at htotal' ⊢; exact htotal') κ W (fun k i => (hW k i).1)
      (by norm_num at htests ⊢; exact hκ.trans htests)
  refine ⟨Q,hQ,?_⟩
  intro k
  have hS : 0 ≤ ∑ i, φ i*W k i := sum_nonneg fun i _ => mul_nonneg (hφ₀ i) (hW k i).1
  have hh := hWeights k (by
    intro i
    have hw := mul_le_mul_of_nonneg_right (hW k i).2
      (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ n^2+C*n) ((5:ℝ)/4))
    norm_num at hw ⊢
    exact hw.trans (hmasscap.trans (mul_le_mul_of_nonneg_left (hmass k) hp)))
  have hfac : (n^2+C*n)^(-((1:ℝ)/3200))*(n^2+C*n)/(n^2+C*n)+
      (n^2+C*n-n^2+C*n)/(n^2+C*n) ≤ η := by
    have hd : n^2+C*n ≠ 0 := by positivity
    convert herror using 1 <;> field_simp <;> ring
  norm_num at hh hfac
  exact hh.trans (mul_le_mul_of_nonneg_right hfac hS)
end TypedTriangle.WeightedClone
