/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.WeightedClone
variable {ι : Type*} [Fintype ι]

def seedMultiplicity (p : ℝ) (φ : ι → ℝ) (i : ι) : ℕ := ⌈p*φ i⌉₊

lemma multiplicity_bounds (p : ℝ) (hp : 0≤p) (φ : ι → ℝ)
    (hφ : ∀ i, 0≤φ i) (i : ι) :
    p*φ i≤(seedMultiplicity p φ i:ℝ) ∧
      (seedMultiplicity p φ i:ℝ)<p*φ i+1 :=
  ⟨Nat.le_ceil _,Nat.ceil_lt_add_one (mul_nonneg hp (hφ i))⟩

lemma multiplicity_load_le (p : ℝ) (hp : 0≤p) (φ : ι → ℝ)
    (hφ : ∀ i, 0≤φ i) (S : Finset ι) (hload : ∑ i ∈ S, φ i=1) :
    ∑ i ∈ S, (seedMultiplicity p φ i:ℝ) ≤ p+S.card := by
  calc ∑ i ∈ S, (seedMultiplicity p φ i:ℝ)
      ≤ ∑ i ∈ S, (p*φ i+1) := sum_le_sum fun i _ => (multiplicity_bounds p hp φ hφ i).2.le
    _ = p+S.card := by rw [sum_add_distrib,←mul_sum,hload]; simp

lemma multiplicity_mass_bounds (p : ℝ) (hp : 0≤p) (φ w : ι → ℝ)
    (hφ : ∀ i, 0≤φ i) (hw : ∀ i, 0≤w i) :
    p*(∑ i, φ i*w i)≤∑ i, (seedMultiplicity p φ i:ℝ)*w i ∧
      (∑ i, (seedMultiplicity p φ i:ℝ)*w i)≤p*(∑ i, φ i*w i)+∑ i, w i := by
  constructor
  · rw [mul_sum]
    apply sum_le_sum
    intro i _
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (multiplicity_bounds p hp φ hφ i).1 (hw i)
  · calc (∑ i, (seedMultiplicity p φ i:ℝ)*w i)
        ≤ ∑ i, (p*φ i+1)*w i := sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (multiplicity_bounds p hp φ hφ i).2.le (hw i)
      _ = p*(∑ i, φ i*w i)+∑ i, w i := by
        simp_rw [add_mul,one_mul,mul_assoc]
        rw [sum_add_distrib,mul_sum]

lemma seed_mass_dominates (a : ℝ) (φ w : ι → ℝ)
    (hfloor : ∀ i, 1≤a*φ i) (hw : ∀ i, 0≤w i) :
    ∑ i, w i≤a*(∑ i, φ i*w i) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_right (hfloor i) (hw i)
  simpa only [one_mul,mul_assoc] using hh

lemma multiplicity_mass_factor (p a : ℝ) (hp : 0≤p) (φ w : ι → ℝ)
    (hφ : ∀ i, 0≤φ i) (hw : ∀ i, 0≤w i) (hfloor : ∀ i, 1≤a*φ i) :
    p*(∑ i, φ i*w i)≤∑ i, (seedMultiplicity p φ i:ℝ)*w i ∧
      (∑ i, (seedMultiplicity p φ i:ℝ)*w i)≤(p+a)*(∑ i, φ i*w i) := by
  obtain ⟨hlo,hhi⟩ := multiplicity_mass_bounds p hp φ w hφ hw
  refine ⟨hlo,?_⟩
  have := seed_mass_dominates a φ w hfloor hw
  nlinarith

/-- The normalization error caused by rounding weights to multiplicities.
Taking p=n^2, D=n^2+n and a=Cn makes its relative factor O(1/n). -/
lemma multiplicity_normalization_error {p a D S M : ℝ}
    (ha : 0≤a) (hD : 0<D) (hpD : p≤D) (hS : 0≤S)
    (hlo : p*S≤M) (hhi : M≤(p+a)*S) :
    |M/D-S|≤((D-p+a)/D)*S := by
  have heq : M/D-S=(M-D*S)/D := by field_simp
  rw [heq,abs_div,abs_of_pos hD]
  have hbound : |M-D*S|≤(D-p+a)*S := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |M-D*S|/D ≤ ((D-p+a)*S)/D := div_le_div_of_nonneg_right hbound hD.le
    _ = ((D-p+a)/D)*S := by ring

end TypedTriangle.WeightedClone
