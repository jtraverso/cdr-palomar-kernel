/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.CrossTypeCounts
public import CDRBicolour.KBicolor.Wilson.Quantitative
public import CountingCone.UpperBound

/-! # The common residual is smaller than the prescribed interior margin -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption
variable {n g B k : ℕ} {S : Finset (Finset (Fin g))}

theorem card_variable_packing (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (Λ : VariableCross.Family S B) :
    #(VariableCross.packing e Λ)=Fintype.card (VariableCross.Block S)*B^2 := by
  rw [VariableCross.packing,card_image_of_injective _ (VariableCross.triangle_injective e hS Λ)]
  simp only [card_univ,VariableCross.Cell,Fintype.card_prod,Fintype.card_fin]
  ring

theorem six_card_decomposition (lab : Fin n → Fin k) (D : Finset (Finset (Fin n)))
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D) (hn : 1 ≤ n) :
    6*(#D : ℝ)=(n : ℝ)*(n-1) := by
  have hsts : _root_.STS.IsSTS D := (mem_filter.mp (mem_kBlocks_of_decomp lab hD)).2.1
  have h3 := _root_.STS.three_mul_card_blocks hsts
  rw [Fintype.card_fin] at h3
  have h2 : 2*n.choose 2=n*(n-1) := by
    rw [Nat.choose_two_right]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have he : 6*#D=n*(n-1) := by omega
  have heR : ((6*#D : ℕ) : ℝ)=((n*(n-1) : ℕ) : ℝ) := by exact_mod_cast he
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hn,Nat.cast_one] using heR

theorem residual_small_of_coverage (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (lab : Fin n → Fin k) (Λ : VariableCross.Family S B) (R : Finset (Finset (Fin n)))
    (hfull : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab))
      (R ∪ VariableCross.packing e Λ))
    (hd : Disjoint R (VariableCross.packing e Λ)) (hn : 1 ≤ n)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hgθ : 1 ≤ θ*g)
    (hcover : (1-θ)*n ≤ (g : ℝ)*B) : (#R : ℝ) ≤ θ/2*(n : ℝ)^2 := by
  let O : ℝ := Fintype.card (VariableCross.Block S)
  have hO : 0 ≤ O := Nat.cast_nonneg _
  have hpairs : (g : ℝ)*(g-1) ≤ 6*O := by
    have hh := Wilson.group_pairs_le_OT hS
    have hgpos : 1 ≤ g := by
      by_contra hg0
      have hgz : g=0 := by omega
      simp only [hgz,Nat.cast_zero,mul_zero] at hgθ
      linarith
    have hhR : ((g*(g-1) : ℕ) : ℝ) ≤ ((6*#(CDRBicolour.Absorption.Count.Wilson.OT S) : ℕ) : ℝ) := by exact_mod_cast hh
    simpa only [O,VariableCross.Block,Fintype.card_coe,Nat.cast_mul,Nat.cast_sub hgpos,
      Nat.cast_one,Nat.cast_ofNat] using hhR
  have hgroup : (1-θ)*(g : ℝ)^2 ≤ (g : ℝ)*(g-1) := by
    nlinarith [mul_le_mul_of_nonneg_right hgθ (Nat.cast_nonneg (α := ℝ) g)]
  have hpoint : ((1-θ)*(n : ℝ))^2 ≤ ((g : ℝ)*B)^2 :=
    pow_le_pow_left₀ (by positivity) hcover 2
  have hcoef : (1-θ)^3*(n : ℝ)^2 ≤ 6*(O*(B : ℝ)^2) := calc
    _ = (1-θ)*((1-θ)*(n : ℝ))^2 := by ring
    _ ≤ (1-θ)*((g : ℝ)*B)^2 := mul_le_mul_of_nonneg_left hpoint (by linarith)
    _ = ((1-θ)*(g : ℝ)^2)*(B : ℝ)^2 := by ring
    _ ≤ ((g : ℝ)*(g-1))*(B : ℝ)^2 := mul_le_mul_of_nonneg_right hgroup (sq_nonneg _)
    _ ≤ (6*O)*(B : ℝ)^2 := mul_le_mul_of_nonneg_right hpairs (sq_nonneg _)
    _ = _ := by ring
  have hcard := six_card_decomposition lab _ hfull hn
  rw [card_union_of_disjoint hd,card_variable_packing e hS Λ] at hcard
  push_cast at hcard
  have hcube : 1-3*θ ≤ (1-θ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg θ) (show 0 ≤ 3-θ by linarith)]
  have hcubeN := mul_le_mul_of_nonneg_right hcube (sq_nonneg (n : ℝ))
  dsimp only [O] at hcoef
  nlinarith

end CDRBicolour.KBicolor.PrescribedCounting
