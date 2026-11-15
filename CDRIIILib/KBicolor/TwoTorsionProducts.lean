/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/-! # A fixed-order family of abelian groups with different two-torsion sizes

Only Z/4 and Z/2 factors are needed. There is no appeal to a classification
theorem for finite groups or to an external number-theoretic result.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical

abbrev TwoTorsionElement (A : Type*) [AddCommGroup A] := {a : A // a+a=0}

def torsionProdEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] :
    TwoTorsionElement (A×B) ≃ TwoTorsionElement A × TwoTorsionElement B where
  toFun p := (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2, congrArg Prod.snd p.2⟩)
  invFun p := ⟨(p.1.1,p.2.1), Prod.ext p.1.2 p.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Prod.ext <;> apply Subtype.ext <;> rfl

def torsionFunEquiv (ι A : Type*) [AddCommGroup A] :
    TwoTorsionElement (ι → A) ≃ (ι → TwoTorsionElement A) where
  toFun p i := ⟨p.1 i, congrFun p.2 i⟩
  invFun p := ⟨fun i => (p i).1, funext (fun i => (p i).2)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by funext i; apply Subtype.ext; rfl

theorem torsion_card_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] :
    Fintype.card (TwoTorsionElement (A×B)) =
      Fintype.card (TwoTorsionElement A) * Fintype.card (TwoTorsionElement B) := by
  classical
  rw [Fintype.card_congr (torsionProdEquiv A B), Fintype.card_prod]

theorem torsion_card_fun (ι A : Type*) [AddCommGroup A] [Fintype ι] [Fintype A] :
    Fintype.card (TwoTorsionElement (ι → A)) =
      Fintype.card (TwoTorsionElement A) ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (torsionFunEquiv ι A), Fintype.card_fun]

theorem torsion_card_zmod_two : Fintype.card (TwoTorsionElement (ZMod 2)) = 2 := by decide
theorem torsion_card_zmod_four : Fintype.card (TwoTorsionElement (ZMod 4)) = 2 := by decide

abbrev DyadicLatinGroup (r i : ℕ) := (Fin i → ZMod 4) × (Fin (r-2*i) → ZMod 2)

theorem dyadicLatinGroup_card {r i : ℕ} (hi : 2*i ≤ r) :
    Fintype.card (DyadicLatinGroup r i) = 2^r := by
  simp only [DyadicLatinGroup, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [show (4:ℕ)=2^2 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem dyadicLatinGroup_two_torsion {r i : ℕ} (hi : 2*i ≤ r) :
    Fintype.card (TwoTorsionElement (DyadicLatinGroup r i)) = 2^(r-i) := by
  calc
    _ = Fintype.card (TwoTorsionElement (Fin i → ZMod 4) ×
        TwoTorsionElement (Fin (r-2*i) → ZMod 2)) :=
      Fintype.card_congr (torsionProdEquiv _ _)
    _ = Fintype.card (Fin i → TwoTorsionElement (ZMod 4)) *
        Fintype.card (Fin (r-2*i) → TwoTorsionElement (ZMod 2)) := by
      rw [Fintype.card_prod]
      exact congrArg₂ (fun x y : ℕ => x*y)
        (Fintype.card_congr (torsionFunEquiv (Fin i) (ZMod 4)))
        (Fintype.card_congr (torsionFunEquiv (Fin (r-2*i)) (ZMod 2)))
    _ = 2^(r-i) := by
      rw [Fintype.card_fun, Fintype.card_fun, torsion_card_zmod_four, torsion_card_zmod_two]
      simp only [Fintype.card_fin]
      rw [← pow_add]
      congr 1
      omega


end CDRBicolour.KBicolor.LatinPasch
