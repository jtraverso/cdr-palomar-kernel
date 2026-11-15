/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.SeedGale
public import CDRIIILib.PaperIII.GalePalomar
public import GaleHoffmanSolution

/-! # A positive four-class seed from explicit cut margins -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CDRBicolour.PaperIII
open Finset CDRBicolour.KBicolor

/-- The registered feasibility proof is imported, rather than assumed. -/
theorem galeInt_verified : GaleInt := by
  apply galeInt_of_palomar
  intro N _ _ c hc d
  exact GaleHoffman.feasibility_int c hc d

theorem four_seed_single_lower {n x : ℤ} (hn : 19180≤n) (hx : 0≤x) (hlo : n≤70*x) :
    x*(n-x)≤137*x*(x-1) := by
  have hlin : 0≤137*(x-1)-(n-x) := by linarith only [hn,hlo]
  nlinarith only [mul_nonneg hx hlin]

theorem four_seed_triple_lower {n x : ℤ} (hn : 19180≤n) (hx : 0≤x) (hhi : 70*x≤34*n) :
    x*(n-x)≤137*x*(n-2*x+1) := by
  have hlin : 0≤137*(n-2*x+1)-(n-x) := by linarith only [hn,hhi]
  nlinarith only [mul_nonneg hx hlin]

theorem four_seed_pair_lower {n x y : ℤ} (hn : 19180≤n) (hx : 0≤x) (hy : 0≤y)
    (hloX : n≤70*x) (hloY : n≤70*y) :
    (x+y)*(n-x-y)≤137*(x^2+y^2-x*y-x-y) := by
  have hw : n≤35*(x+y) := by linarith only [hloX,hloY]
  have hlin : 0≤141*(x+y)-4*n-548 := by linarith only [hn,hw]
  nlinarith only [mul_nonneg (add_nonneg hx hy) hlin,sq_nonneg (x-y)]

/-- Every one of the sixteen class cuts is verified; no seed or flow is an input. -/
theorem seed_of_robust_four_profile {v : ℕ} (hv : 19180≤v) (cs : Fin 4 → ℕ)
    (hs : ∑ X,cs X=v) (hq : 3*∑ X,(cs X : ℤ)^2=(v : ℤ)^2+2*v)
    (hlo : ∀ X,v≤70*cs X) (hhi : ∀ X,70*cs X≤34*v) :
    ∃ a,SeedData cs (1/137) a := by
  classical
  have hvZ : (19180 : ℤ)≤v := by exact_mod_cast hv
  have hpos : ∀ X,(0 : ℤ)≤cs X := fun _ => Int.natCast_nonneg _
  have hl : ∀ X,(v : ℤ)≤70*cs X := fun X => by exact_mod_cast hlo X
  have hu : ∀ X,70*(cs X : ℤ)≤34*v := fun X => by exact_mod_cast hhi X
  have hSingle := fun X => four_seed_single_lower hvZ (hpos X) (hl X)
  have hTriple := fun X => four_seed_triple_lower hvZ (hpos X) (hu X)
  have hPair := fun X Y => four_seed_pair_lower hvZ (hpos X) (hpos Y) (hl X) (hl Y)
  have hsZ : (cs 0 : ℤ)+cs 1+cs 2+cs 3=v := by
    exact_mod_cast (show cs 0+cs 1+cs 2+cs 3=v by simpa only [Fin.sum_univ_four] using hs)
  have hqZ := hq
  simp only [Fin.sum_univ_four] at hqZ
  rw [←hsZ] at hqZ
  have s0 := hSingle 0
  have s1 := hSingle 1
  have s2 := hSingle 2
  have s3 := hSingle 3
  have t0 := hTriple 0
  have t1 := hTriple 1
  have t2 := hTriple 2
  have t3 := hTriple 3
  have p01 := hPair 0 1
  have p02 := hPair 0 2
  have p03 := hPair 0 3
  have p12 := hPair 1 2
  have p13 := hPair 1 3
  have p23 := hPair 2 3
  rw [←hsZ] at s0 s1 s2 s3 t0 t1 t2 t3 p01 p02 p03 p12 p13 p23
  apply seed_of_gale galeInt_verified cs (v := v) (M := 137) (by norm_num)
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
