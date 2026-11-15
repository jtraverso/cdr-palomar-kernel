/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.FourSeedGale

/-! # A stronger uniform seed margin from the quadratic profile identity -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CDRBicolour.PaperIII
open Finset CDRBicolour.KBicolor

/-- The quadratic identity forces every pair of classes to carry at least a fifth
of the total mass. This is stronger than adding their separate class floors. -/
theorem four_profile_pair_mass {n x y z t : ℤ} (hn : 101≤n)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) (ht : 0≤t)
    (hs : x+y+z+t=n) (hq : 3*(x^2+y^2+z^2+t^2)=n^2+2*n) :
    n≤5*(x+y) := by
  have hbalance : 6*(x+y)^2-6*n*(x+y)+n^2≤4*n := by
    rw [←hs] at hq ⊢
    nlinarith only [hq,sq_nonneg (x-y),sq_nonneg (z-t)]
  by_contra h
  have hsmall : 5*(x+y)<n := by omega
  have hp := mul_nonneg (show 0≤n-5*(x+y) by omega)
    (show 0≤4*n-5*(x+y) by omega)
  have hn2 : 100*n<n^2 := by nlinarith
  nlinarith only [hbalance,hp,hn2]

theorem four_seed_single_lower70 {n x : ℤ} (hn : 4900≤n) (hx : 0≤x)
    (hlo : n≤70*x) : x*(n-x)≤70*x*(x-1) := by
  have hlin : 0≤70*(x-1)-(n-x) := by linarith only [hn,hlo]
  nlinarith only [mul_nonneg hx hlin]

theorem four_seed_triple_lower70 {n x : ℤ} (hn : 4900≤n) (hx : 0≤x)
    (hhi : 70*x≤34*n) : x*(n-x)≤70*x*(n-2*x+1) := by
  have hlin : 0≤70*(n-2*x+1)-(n-x) := by linarith only [hn,hhi]
  nlinarith only [mul_nonneg hx hlin]

theorem four_seed_pair_lower70 {n x y : ℤ} (hn : 4900≤n)
    (hx : 0≤x) (hy : 0≤y) (hw : n≤5*(x+y)) :
    (x+y)*(n-x-y)≤70*(x^2+y^2-x*y-x-y) := by
  have hlin : 0≤74*(x+y)-4*n-280 := by linarith only [hn,hw]
  nlinarith only [mul_nonneg (add_nonneg hx hy) hlin,sq_nonneg (x-y)]

/-- All sixteen cuts hold with margin `1/70`, using the same class bounds as
the earlier `1/137` theorem and a smaller local seed cut-off. -/
theorem seed_of_robust_four_profile70 {v : ℕ} (hv : 4900≤v) (cs : Fin 4 → ℕ)
    (hs : ∑ X,cs X=v) (hq : 3*∑ X,(cs X : ℤ)^2=(v : ℤ)^2+2*v)
    (hlo : ∀ X,v≤70*cs X) (hhi : ∀ X,70*cs X≤34*v) :
    ∃ a,SeedData cs (1/70) a := by
  classical
  have hvZ : (4900 : ℤ)≤v := by exact_mod_cast hv
  have hpos : ∀ X,(0 : ℤ)≤cs X := fun _ => Int.natCast_nonneg _
  have hl : ∀ X,(v : ℤ)≤70*cs X := fun X => by exact_mod_cast hlo X
  have hu : ∀ X,70*(cs X : ℤ)≤34*v := fun X => by exact_mod_cast hhi X
  have hSingle := fun X => four_seed_single_lower70 hvZ (hpos X) (hl X)
  have hTriple := fun X => four_seed_triple_lower70 hvZ (hpos X) (hu X)
  have hsZ : (cs 0 : ℤ)+cs 1+cs 2+cs 3=v := by
    exact_mod_cast (show cs 0+cs 1+cs 2+cs 3=v by simpa only [Fin.sum_univ_four] using hs)
  have hqZ := hq
  simp only [Fin.sum_univ_four] at hqZ
  have hm01 := four_profile_pair_mass (by omega : (101 : ℤ)≤v)
    (hpos 0) (hpos 1) (hpos 2) (hpos 3) hsZ hqZ
  have hm02 := four_profile_pair_mass (by omega : (101 : ℤ)≤v)
    (hpos 0) (hpos 2) (hpos 1) (hpos 3) (by linarith only [hsZ]) (by nlinarith only [hqZ])
  have hm03 := four_profile_pair_mass (by omega : (101 : ℤ)≤v)
    (hpos 0) (hpos 3) (hpos 1) (hpos 2) (by linarith only [hsZ]) (by nlinarith only [hqZ])
  have hm12 := four_profile_pair_mass (by omega : (101 : ℤ)≤v)
    (hpos 1) (hpos 2) (hpos 0) (hpos 3) (by linarith only [hsZ]) (by nlinarith only [hqZ])
  have hm13 := four_profile_pair_mass (by omega : (101 : ℤ)≤v)
    (hpos 1) (hpos 3) (hpos 0) (hpos 2) (by linarith only [hsZ]) (by nlinarith only [hqZ])
  have hm23 := four_profile_pair_mass (by omega : (101 : ℤ)≤v)
    (hpos 2) (hpos 3) (hpos 0) (hpos 1) (by linarith only [hsZ]) (by nlinarith only [hqZ])
  have s0 := hSingle 0
  have s1 := hSingle 1
  have s2 := hSingle 2
  have s3 := hSingle 3
  have t0 := hTriple 0
  have t1 := hTriple 1
  have t2 := hTriple 2
  have t3 := hTriple 3
  have p01 := four_seed_pair_lower70 hvZ (hpos 0) (hpos 1) hm01
  have p02 := four_seed_pair_lower70 hvZ (hpos 0) (hpos 2) hm02
  have p03 := four_seed_pair_lower70 hvZ (hpos 0) (hpos 3) hm03
  have p12 := four_seed_pair_lower70 hvZ (hpos 1) (hpos 2) hm12
  have p13 := four_seed_pair_lower70 hvZ (hpos 1) (hpos 3) hm13
  have p23 := four_seed_pair_lower70 hvZ (hpos 2) (hpos 3) hm23
  rw [←hsZ] at hqZ s0 s1 s2 s3 t0 t1 t2 t3 p01 p02 p03 p12 p13 p23
  apply seed_of_gale galeInt_verified cs (v := v) (M := 70) (by norm_num)
    (fun X => by have := hlo X; omega) hs hq
  intro S
  have hcompl : ∀ f : Fin 4 → ℤ, ∑ Y ∈ Sᶜ,f Y = (∑ Y,f Y)-(∑ Y ∈ S,f Y) := by
    intro f
    have hh := sum_compl_add_sum S f
    linarith
  simp_rw [hcompl]
  rw [←hsZ]
  fin_cases S <;> norm_num [Fin.sum_univ_four] <;>
    nlinarith only [hqZ,s0,s1,s2,s3,t0,t1,t2,t3,p01,p02,p03,p12,p13,p23]

end CDRBicolour.PaperIII
