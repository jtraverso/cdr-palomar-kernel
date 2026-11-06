/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SeedMultiplicity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.WeightedClone
variable {E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq E]

/-- A lower bound on the fractional coefficients controls the number of
candidates through a resource, even when no geometric counting lemma is used. -/
lemma fractional_incidence_card (P : ι → Finset E) (φ : ι → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hfloor : ∀ i, 1 ≤ a*φ i)
    (hload : ∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) (e : E) :
    ((univ.filter fun i => e ∈ P i).card : ℝ) ≤ a := by
  calc ((univ.filter fun i => e ∈ P i).card : ℝ)
      = ∑ i ∈ univ.filter (fun i => e ∈ P i), (1:ℝ) := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => e ∈ P i), a*φ i :=
      sum_le_sum fun i _ => hfloor i
    _ = a*(∑ i, if e ∈ P i then φ i else 0) := by rw [mul_sum]; simp only [sum_filter,mul_ite,mul_zero]
    _ ≤ a := by simpa using mul_le_mul_of_nonneg_left (hload e) ha

/-- Literal clone degrees follow from exact fractional loads and diffuseness. -/
lemma multiplicity_degree_cap (P : ι → Finset E) (φ : ι → ℝ) (p a : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hφ : ∀ i, 0 ≤ φ i) (hfloor : ∀ i, 1 ≤ a*φ i)
    (hload : ∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) (e : E) :
    ((∑ i, if e ∈ P i then seedMultiplicity p φ i else 0 : ℕ):ℝ) ≤ p+a := by
  let w : ι → ℝ := fun i => if e ∈ P i then 1 else 0
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; split_ifs <;> positivity
  have hh := (multiplicity_mass_factor p a hp φ w hφ hw hfloor).2
  have hs : (∑ i, φ i*w i) ≤ 1 := by simpa [w] using hload e
  have hb := hh.trans (mul_le_mul_of_nonneg_left hs (add_nonneg hp ha))
  simpa [w] using hb

/-- In a linear candidate system, a pair of resources belongs to at most one
candidate. Cloning preserves this geometric saving in the codegree bound. -/
lemma multiplicity_codegree_cap (P : ι → Finset E) (φ : ι → ℝ) (p b : ℝ)
    (hp : 0 ≤ p) (hb₀ : 0 ≤ b) (hφ : ∀ i, 0 ≤ φ i) (hb : ∀ i, φ i ≤ b)
    (hlin : ∀ e f, e ≠ f → (univ.filter fun i => e ∈ P i ∧ f ∈ P i).card ≤ 1)
    (e f : E) (hef : e ≠ f) :
    ((∑ i, if e ∈ P i ∧ f ∈ P i then seedMultiplicity p φ i else 0 : ℕ):ℝ) ≤ p*b+1 := by
  let S := univ.filter fun i => e ∈ P i ∧ f ∈ P i
  have hsum : ∑ i ∈ S, (seedMultiplicity p φ i:ℝ) ≤ ∑ i ∈ S, (p*b+1) := by
    apply sum_le_sum
    intro i _
    have hh := (multiplicity_bounds p hp φ hφ i).2.le
    have := mul_le_mul_of_nonneg_left (hb i) hp
    linarith
  have hcard : (S.card:ℝ) ≤ 1 := by exact_mod_cast hlin e f hef
  have hbpos : 0 ≤ p*b+1 := by positivity
  have hsum' : ∑ i ∈ S, (seedMultiplicity p φ i:ℝ) ≤ (S.card:ℝ)*(p*b+1) := by
    simpa only [sum_const,nsmul_eq_mul] using hsum
  have hh := hsum'.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcard hbpos)
  simpa [S,sum_filter] using hh

/-- Total fractional mass is at most the number of resources: every candidate
uses at least one resource and every resource has load at most one. -/
lemma fractional_total_mass_cap (P : ι → Finset E) (φ : ι → ℝ)
    (hφ : ∀ i, 0 ≤ φ i) (hP : ∀ i, (P i).Nonempty)
    (hload : ∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) :
    (∑ i, φ i) ≤ Fintype.card E := by
  calc (∑ i, φ i)
      ≤ ∑ i, ∑ e, (if e ∈ P i then φ i else 0) := by
        apply sum_le_sum
        intro i _
        have hi : (1:ℝ) ≤ (P i).card := by exact_mod_cast card_pos.mpr (hP i)
        simpa only [sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul,one_mul] using
          mul_le_mul_of_nonneg_right hi (hφ i)
    _ = ∑ e, ∑ i, (if e ∈ P i then φ i else 0) := sum_comm
    _ ≤ ∑ _ : E, (1:ℝ) := sum_le_sum fun e _ => hload e
    _ = Fintype.card E := by simp

lemma multiplicity_total_cap (P : ι → Finset E) (φ : ι → ℝ) (p a : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hφ : ∀ i, 0 ≤ φ i) (hfloor : ∀ i, 1 ≤ a*φ i)
    (hP : ∀ i, (P i).Nonempty)
    (hload : ∀ e, ∑ i, (if e ∈ P i then φ i else 0) ≤ 1) :
    ((∑ i, seedMultiplicity p φ i : ℕ):ℝ) ≤ (p+a)*Fintype.card E := by
  have hh := (multiplicity_mass_factor p a hp φ (fun _ => 1) hφ (by simp) hfloor).2
  simp only [mul_one] at hh
  have hh' : ((∑ i, seedMultiplicity p φ i : ℕ):ℝ) ≤ (p+a)*(∑ i, φ i) := by simpa using hh
  exact hh'.trans
    (mul_le_mul_of_nonneg_left (fractional_total_mass_cap P φ hφ hP hload) (add_nonneg hp ha))
end TypedTriangle.WeightedClone
