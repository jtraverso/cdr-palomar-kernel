/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.RobustSeed
public import CDRIIILib.KBicolor.Wilson.SeedParameters

/-!
# Residual H1 at an explicit order threshold

Near-full coverage, a cone pattern and the original robust SeedData suffice.
All local inverse and correction budgets follow from fixed explicit parameters.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption
open scoped Classical

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}

theorem residual_H1_at_threshold (hk : 3 ≤ k) (o : Fin k)
    (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) (hg : 1 ≤ g)
    {δ η ρ : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hρhalf : ρ ≤ 1/2)
    (hρgroup : ρ ≤ 1/((g : ℝ)+1))
    (hn : seedThreshold g o δ η ≤ n)
    (hcover : (1-ρ)*(n : ℝ) ≤ ((g*Fintype.card A*t : ℕ) : ℝ))
    {a : Fin k → Fin k → ℝ} (hs : SeedData (ksz lab) η a)
    (hcls : ∀ X, δ*n ≤ ksz lab X)
    (hclose : ∀ X, |(Hilton.csize κ X : ℝ)/Fintype.card A - (ksz lab X : ℝ)/n| ≤ seedAccuracy g o δ η)
    (hglobal : 3*∑ X, (ksz lab X : ℝ)^2 = (n : ℝ)^2+2*n)
    (hcone : 3*∑ X, Hilton.csize κ X^2 = (∑ X, Hilton.csize κ X)^2) :
    ∃ μ : Finset (Fin n) → ℝ,
      IsDiffuseSeed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
        (globalSeedConstant (g : ℝ) η δ) μ := by
  let B : ℝ := (Fintype.card A*t : ℕ)
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hcover' : (1-ρ)*(n : ℝ) ≤ (g : ℝ)*B := by
    simpa only [B,Nat.cast_mul,mul_assoc] using hcover
  have hBbound : (n : ℝ) ≤ 2*(g : ℝ)*B := by
    have hp := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hρhalf)
    nlinarith [hcover']
  obtain ⟨h2,hsize,horder⟩ := seedThreshold_budgets hg o hδ hη hn hBbound
  have hnR : (0 : ℝ) < n := by
    have hh : 0 < δ*(n : ℝ) := by linarith
    exact pos_of_mul_pos_right hh hδ.le
  have hnNat : 0 < n := by exact_mod_cast hnR
  have hBR : 0 < B := by nlinarith [hBbound]
  have hBNat : 0 < Fintype.card A*t := by dsimp [B] at hBR; exact_mod_cast hBR
  have hmass : (#(reserve h) : ℝ)+(g : ℝ)*B=n := by dsimp [B]; exact_mod_cast reserve_order h
  have hRB : #(reserve h) ≤ Fintype.card A*t := by
    have hh := reserve_le_group_of_mass hgR hnR.le hmass hcover' hρgroup
    dsimp [B] at hh
    exact_mod_cast hh
  obtain ⟨hξ,hξδ,hξbudget⟩ := seedAccuracy_spec hk hg o hδ hη
  exact residual_H1 h hk o hS Λ hg hnNat hBNat hRB hη hδ hξ.le hξδ hs hcls h2
    hclose hglobal hcone hsize hξbudget horder

end CDRBicolour.KBicolor.Wilson
