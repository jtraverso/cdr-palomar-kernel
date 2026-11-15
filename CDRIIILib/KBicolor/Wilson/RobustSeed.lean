/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.ResidualSeed

/-!
# H1 with explicit pattern-accuracy and group-order budgets

The inverse is constructed with R=8/delta and m=floor(delta*B/2), where B is
the group order. No local seed, compatibility equation, or inverse is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined
open scoped Classical

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}

theorem residual_H1 (hk : 3 ≤ k) (o : Fin k)
    (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) (hg : 1 ≤ g) (hn : 0 < n)
    (hB : 0 < Fintype.card A*t) (hRB : #(reserve h) ≤ Fintype.card A*t)
    {η δ ξ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hξ0 : 0 ≤ ξ) (hξδ : ξ ≤ δ/2)
    {a : Fin k → Fin k → ℝ} (hs : SeedData (ksz lab) η a)
    (hcls : ∀ X, δ*n ≤ ksz lab X) (h2 : 2 ≤ δ*n)
    (hclose : ∀ X, |(Hilton.csize κ X : ℝ)/Fintype.card A - (ksz lab X : ℝ)/n| ≤ ξ)
    (hglobal : 3*∑ X, (ksz lab X : ℝ)^2 = (n : ℝ)^2+2*n)
    (hcone : 3*∑ X, Hilton.csize κ X^2 = (∑ X, Hilton.csize κ X)^2)
    (hsize : 2*((inverseFloorMinimum δ : ℝ)+1) ≤ δ*(Fintype.card A*t : ℕ))
    (hξbudget : 8*(g : ℝ)*localInverseConstant o (8/δ)*k*((g : ℝ)+1)*ξ ≤ η*δ)
    (horder : 32*(g : ℝ)*localInverseConstant o (8/δ) ≤ η*δ*(Fintype.card A*t : ℕ)) :
    ∃ μ : Finset (Fin n) → ℝ,
      IsDiffuseSeed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
        (globalSeedConstant (g : ℝ) η δ) μ := by
  let B : ℝ := (Fintype.card A*t : ℕ)
  let m : ℕ := ⌊δ*B/2⌋₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBR : 0 < B := by dsimp [B]; exact_mod_cast hB
  have hA : 0 < Fintype.card A := by
    by_contra hA
    have hz : Fintype.card A=0 := Nat.eq_zero_of_not_pos hA
    simp only [hz,zero_mul] at hB
    omega
  have hAR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hsizeo : (ksz lab o : ℝ) ≤ n := by
    have hh := card_le_univ (univ.filter fun v : Fin n => lab v=o)
    simp only [Fintype.card_fin] at hh
    change ((#(univ.filter fun v : Fin n => lab v=o) : ℕ) : ℝ) ≤ n
    exact_mod_cast hh
  have hδ8 : δ ≤ 8 := by nlinarith [hcls o]
  obtain ⟨hR,h512,hmR,hmfloor,hfloorbal⟩ := inverse_floor_parameters hδ hδ8 hsize
  have hm : ∀ X, m ≤ Hilton.csize κ X*t + #((reserve h).filter fun v => lab v=X) := by
    intro X
    have hdiff := scaled_group_discrepancy hAR hnR (Nat.cast_nonneg t) (hclose X)
    have hdiff' : |((Hilton.csize κ X*t : ℕ) : ℝ)-(B/n)*ksz lab X| ≤ B*ξ := by
      simpa only [B,Nat.cast_mul] using hdiff
    have hscaledcls := mul_le_mul_of_nonneg_left (hcls X) (div_nonneg hBR.le hnR.le)
    have hid : (B/n)*(δ*n)=δ*B := by field_simp <;> ring
    rw [hid] at hscaledcls
    have hlow : δ*B/2 ≤ ((Hilton.csize κ X*t : ℕ) : ℝ) := by
      nlinarith [(abs_le.mp hdiff').1,mul_nonneg hBR.le (sub_nonneg.mpr hξδ)]
    have hh : (m : ℝ) ≤ ((Hilton.csize κ X*t : ℕ) : ℝ) +
        #((reserve h).filter fun v => lab v=X) := by
      have hp : (0 : ℝ) ≤ #((reserve h).filter fun v => lab v=X) := by positivity
      linarith
    exact_mod_cast hh
  have hbal : ((Fintype.card A*t + #(reserve h) : ℕ) : ℝ) ≤ (8/δ)*m := by
    have hRB' : (#(reserve h) : ℝ) ≤ B := by dsimp [B]; exact_mod_cast hRB
    have hh : ((Fintype.card A*t + #(reserve h) : ℕ) : ℝ) ≤ 2*B := by
      push_cast
      dsimp [B] at hRB' ⊢
      push_cast at hRB' ⊢
      linarith
    exact hh.trans hfloorbal
  exact residual_H1_from_pattern h hk o hS Λ hg hn hB hRB hη hδ hξ0 hs hcls h2
    hclose hglobal hcone hR hm h512 hmR hbal hξbudget horder

theorem seedData_eta_le_half {c : Fin k → ℕ} {η : ℝ} {a : Fin k → Fin k → ℝ}
    (hk : 2 ≤ k) (hs : SeedData c η a) : η ≤ 1/2 := by
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i ≠ j := by intro he; have hh := congrArg Fin.val he; dsimp [i,j] at hh; omega
  nlinarith [hs.1 i j hij,hs.2.1 i j hij,hs.2.1 j i (Ne.symm hij)]

theorem globalSeedConstant_ge_one {g η δ : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1/2) :
    1 ≤ globalSeedConstant g η δ := by
  apply le_trans _ (le_max_left _ _)
  apply (le_div_iff₀ hη).mpr
  linarith

end CDRBicolour.KBicolor.Wilson
