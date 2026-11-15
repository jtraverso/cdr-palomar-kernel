/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.PieceCounts
public import CDRIIILib.KBicolor.Wilson.AssemblyBounds

/-!
# Constructing H1 of the common Wilson residual from the original seed data

No local or global diffuse seed is assumed. The approximate seeds, their exact
balance and bounded-inverse corrections are constructed on the actual pieces.
The remaining assumptions are explicit size and approximation budgets.
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

theorem residual_H1_from_pattern (hk : 3 ≤ k) (o : Fin k)
    (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) (hg : 1 ≤ g) (hn : 0 < n)
    (hB : 0 < Fintype.card A*t) (hRB : #(reserve h) ≤ Fintype.card A*t)
    {η δ ξ R : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hξ0 : 0 ≤ ξ)
    {a : Fin k → Fin k → ℝ} (hs : SeedData (ksz lab) η a)
    (hcls : ∀ X, δ*n ≤ ksz lab X) (h2 : 2 ≤ δ*n)
    (hclose : ∀ X, |(Hilton.csize κ X : ℝ)/Fintype.card A - (ksz lab X : ℝ)/n| ≤ ξ)
    (hglobal : 3*∑ X, (ksz lab X : ℝ)^2 = (n : ℝ)^2+2*n)
    (hcone : 3*∑ X, Hilton.csize κ X^2 = (∑ X, Hilton.csize κ X)^2)
    {m : ℕ} (hR : 1 ≤ R)
    (hm : ∀ X, m ≤ Hilton.csize κ X*t + #((reserve h).filter fun v => lab v = X))
    (h512 : 512 ≤ m) (hmR : 64*R^3 ≤ m)
    (hbal : ((Fintype.card A*t + #(reserve h) : ℕ) : ℝ) ≤ R*m)
    (hξbudget : 8*(g : ℝ)*localInverseConstant o R*k*((g : ℝ)+1)*ξ ≤ η*δ)
    (horder : 32*(g : ℝ)*localInverseConstant o R ≤ η*δ*(Fintype.card A*t : ℕ)) :
    ∃ μ : Finset (Fin n) → ℝ,
      IsDiffuseSeed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
        (globalSeedConstant (g : ℝ) η δ) μ := by
  let B : ℝ := (Fintype.card A*t : ℕ)
  let N : ℝ := (Fintype.card A*t + #(reserve h) : ℕ)
  let x : ℝ := B/n
  let y : ℝ := #(reserve h)/n
  let G : ℝ := g
  let K : ℝ := localInverseConstant o R
  let EG : ℝ := B*ξ
  let ER : ℝ := G*B*ξ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBR : 0 < B := by dsimp [B]; exact_mod_cast hB
  have hgR : 1 ≤ G := by dsimp [G]; exact_mod_cast hg
  have hg0 : 0 < G := by linarith
  have hA : 0 < Fintype.card A := by
    by_contra hA
    have hA0 : Fintype.card A=0 := Nat.eq_zero_of_not_pos hA
    simp only [hA0,zero_mul] at hB
    omega
  have hAR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hx : 0 < x := div_pos hBR hnR
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyx : y ≤ x := by
    dsimp [y,x,B]
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast hRB
  have hmass : G*x+y=1 := by
    have hh : (#(reserve h) : ℝ) + (g : ℝ)*B = n := by
      dsimp [B]
      exact_mod_cast reserve_order h
    dsimp [G,x,y]
    field_simp
    nlinarith [hh]
  have hx1 : x ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hgR) hx.le]
  have hBn : x*n=B := by dsimp [x]; field_simp
  have hN : N=(x+y)*n := by
    dsimp [N,x,y,B]
    push_cast
    field_simp <;> ring
  have hK : 0 ≤ K := by dsimp [K,localInverseConstant]; positivity
  have hEG : 0 ≤ EG := mul_nonneg hBR.le hξ0
  have hER : 0 ≤ ER := by dsimp [ER]; positivity
  have hsize : ∀ X, (ksz lab X : ℝ) ≤ n := by
    intro X
    have hh := card_le_univ (univ.filter fun v : Fin n => lab v=X)
    simp only [Fintype.card_fin] at hh
    change ((#(univ.filter fun v : Fin n => lab v=X) : ℕ) : ℝ) ≤ n
    exact_mod_cast hh
  have hgroup : ∀ X, |((Hilton.csize κ X*t : ℕ) : ℝ)-x*ksz lab X| ≤ EG := by
    intro X
    have hh := scaled_group_discrepancy hAR hnR (Nat.cast_nonneg t) (hclose X)
    simpa only [Nat.cast_mul,EG,x,B] using hh
  have hreserve : ∀ X, |(#((reserve h).filter fun v => lab v=X) : ℝ)-y*ksz lab X| ≤ ER := by
    intro X
    have hconserve : (#((reserve h).filter fun v => lab v=X) : ℝ) +
        G*(Hilton.csize κ X : ℝ)*t = ksz lab X := by
      dsimp [G]
      exact_mod_cast reserve_class_card h X
    have hid : (#((reserve h).filter fun v => lab v=X) : ℝ)-y*ksz lab X =
        -G*((Hilton.csize κ X : ℝ)*t-x*ksz lab X) := by
      linear_combination hconserve - (ksz lab X : ℝ)*hmass
    calc
      _ = G*|((Hilton.csize κ X*t : ℕ) : ℝ)-x*ksz lab X| := by
        rw [hid,abs_mul,abs_neg,abs_of_nonneg hg0.le,Nat.cast_mul]
      _ ≤ G*EG := mul_le_mul_of_nonneg_left (hgroup X) hg0.le
      _ = ER := by dsimp [EG,ER]; ring
  have hEeq : EG=x*n*ξ := by dsimp [EG]; rw [hBn]
  have hEReq : ER=G*x*n*ξ := by dsimp [ER]; rw [← hBn]; ring
  have hscaled : localDefectBound k (2/(δ*n)) EG ER x = normalizedDefectBudget k G δ ξ n x := by
    rw [hEeq,hEReq,localDefectBound_scaled k hδ hnR hx]
  have horder' : 32*G*K ≤ η*δ*n*x := by
    have hid : η*δ*n*x = η*δ*B := by rw [← hBn]; ring
    rw [hid]
    exact horder
  have hsmall : K*localDefectBound k (2/(δ*n)) EG ER x ≤ η/(2*G) := by
    rw [hscaled]
    exact explicit_local_correction_budget hg0 hδ hnR hx hξbudget horder'
  have hlocal : ∀ i : Fin g, ∃ φ : Finset (Piece h i) → ℝ,
      MincG (pieceLab h i) (bicF k) φ =
        (fun e : E0 (Piece h i) => reserveTarget (pieceReserve h i) G e.1) ∧
      ∀ T ∈ triG (pieceLab h i) (bicF k),
        η/(2*G*N) ≤ φ T ∧ φ T ≤ (4/δ+η/(2*G))/N := by
    intro i
    obtain ⟨Bi⟩ := briK (pieceLab h i) hk o hR
      (fun X => by rw [piece_class_counts]; exact hm X) h512 hmR
      (by rw [piece_order]; exact hbal)
    obtain ⟨φ,heq,hφ⟩ := optimized_local_seed (pieceLab h i) (pieceReserve h i) (ksz lab) a
      hgR hx hx1 hy hyx hη hδ hnR hs hcls hsize h2 hEG hER
      (fun X => by rw [piece_group_counts]; exact hgroup X)
      (fun X => by rw [piece_reserve_counts]; exact hreserve X)
      (by rw [piece_order]; exact hN)
      (piece_balance_from_profile h hglobal hcone i) Bi hK hsmall
    refine ⟨φ,heq,fun T hT => ?_⟩
    simpa only [piece_order] using hφ T hT
  choose φ hM hφ using hlocal
  have hb := global_seed_constant_bounds hgR hx hy hyx hη hδ hnR hmass hN
  refine ⟨assembledSeed h φ,global_seed_of_local h hS Λ (by omega) ?_ hφ hM hb.2.1 hb.2.2⟩
  dsimp [N]
  positivity

end CDRBicolour.KBicolor.Wilson
