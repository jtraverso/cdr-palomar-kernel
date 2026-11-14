/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.SeedDefect

/-!
# Exact compatibility of the actual local edge target

The scalar profile identity is converted to the incidence functional by
counting ordered pairs with their colour and reserve flag. This includes the
diagonal correction in every colour; the cancellation is exact.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined
open CDRBicolour.Absorption.Count.Wilson

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

def classPairSum (z : Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, (if i = j then (-2 : ℝ) else 1) *
    (z i * z j - if i = j then z i else 0)

theorem classPairSum_eq (z : Fin k → ℝ) : classPairSum z = -profileDefect z := by
  have hterm : ∀ i j, (if i = j then (-2 : ℝ) else 1) *
      (z i * z j - if i = j then z i else 0) =
      z i * z j - 3 * (if i = j then z i * z j else 0) +
        2 * (if i = j then z i else 0) := by
    intro i j
    split_ifs <;> ring
  simp only [classPairSum, hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_ite_eq, mem_univ, ite_true]
  simp only [profileDefect, coneQuadratic]
  rw [← sum_mul]
  simp only [pow_two]
  ring

def sideLabel (lab : V → Fin k) (R : Finset V) (v : V) : Fin k × Bool :=
  (lab v, decide (v ∈ R))

theorem sideLabel_counts (lab : V → Fin k) (R : Finset V) (i : Fin k) (b : Bool) :
    (nI (sideLabel lab R) (i,b) : ℝ) =
      if b then (#(R.filter fun v => lab v = i) : ℝ)
      else (#((univ \ R).filter fun v => lab v = i) : ℝ) := by
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    congr 1
    unfold nI sideLabel
    congr 1
    ext v
    simp [and_comm]

def flaggedWeight (g : ℝ) (X Y : Fin k × Bool) : ℝ :=
  (if X.1 = Y.1 then (-2 : ℝ) else 1) *
    (if X.2 = true ∧ Y.2 = true then 1 / g else 1)

theorem flagged_pair_sum (g : ℝ) (x y : Fin k → ℝ) :
    (∑ X : Fin k × Bool, ∑ Y : Fin k × Bool,
      flaggedWeight g X Y *
        ((if X.2 then y X.1 else x X.1) * (if Y.2 then y Y.1 else x Y.1) -
          if X = Y then (if X.2 then y X.1 else x X.1) else 0)) =
      -profileDefect (x+y) + (1-1/g) * profileDefect y := by
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ j, ∑ b : Bool, ∑ d : Bool,
        flaggedWeight g (i,b) (j,d) *
          ((if b then y i else x i) * (if d then y j else x j) -
            if (i,b) = (j,d) then (if b then y i else x i) else 0) := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ = ∑ i, ∑ j, (if i=j then (-2 : ℝ) else 1) *
        (((x i+y i)*(x j+y j) - if i=j then x i+y i else 0) -
          (1-1/g) * (y i*y j - if i=j then y i else 0)) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hij : i=j <;>
        simp [Fintype.sum_bool, flaggedWeight, hij, Prod.mk.injEq] <;> ring
    _ = classPairSum (x+y) - (1-1/g) * classPairSum y := by
      simp only [classPairSum, Pi.add_apply, mul_sub, sum_sub_distrib,
        mul_left_comm _ (1-1/g), ← mul_sum]
    _ = _ := by rw [classPairSum_eq, classPairSum_eq]; ring

theorem ell_reserveTarget_identity (lab : V → Fin k) (R : Finset V) (g : ℝ) :
    let x : Fin k → ℝ := fun i => (#((univ \ R).filter fun v => lab v = i) : ℝ)
    let y : Fin k → ℝ := fun i => (#(R.filter fun v => lab v = i) : ℝ)
    2 * ellG' (wlk lab) (fun e : E0 V => reserveTarget R g e.1) =
      -profileDefect (x+y) + (1-1/g) * profileDefect y := by
  intro x y
  have hpt : ∀ u v, wlk lab s(u,v) * reserveTarget R g s(u,v) =
      flaggedWeight g (sideLabel lab R u) (sideLabel lab R v) := by
    intro u v
    by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> by_cases hc : lab u = lab v <;>
      simp [wlk, reserveTarget, flaggedWeight, sideLabel, hu, hv, hc]
  have h2 : 2 * ellG' (wlk lab) (fun e : E0 V => reserveTarget R g e.1) =
      ∑ p ∈ (univ : Finset V).offDiag,
        flaggedWeight g (sideLabel lab R p.1) (sideLabel lab R p.2) := by
    simp_rw [← hpt]
    rw [sum_offDiag_E0 (fun e => wlk lab e * reserveTarget R g e)]
    rfl
  rw [h2, sum_offDiag_lab]
  have hcount : ∀ X : Fin k × Bool, (nI (sideLabel lab R) X : ℝ) =
      if X.2 then y X.1 else x X.1 := by
    rintro ⟨i,b⟩
    exact sideLabel_counts lab R i b
  simp_rw [hcount]
  exact flagged_pair_sum g x y

theorem local_target_compatible (lab : V → Fin k) (R : Finset V) {g : ℝ}
    (hg : 0 < g)
    (hbalance : g * profileDefect
      ((fun i => (#((univ \ R).filter fun v => lab v = i) : ℝ)) +
       (fun i => (#(R.filter fun v => lab v = i) : ℝ))) =
      (g-1) * profileDefect (fun i => (#(R.filter fun v => lab v = i) : ℝ))) :
    ellG' (wlk lab) (fun e : E0 V => reserveTarget R g e.1) = 0 := by
  have hh := ell_reserveTarget_identity lab R g
  dsimp only at hh
  have hmul := congrArg (fun z : ℝ => g*z) hh
  field_simp at hmul
  nlinarith [hbalance]

end CDRBicolour.KBicolor.Wilson
