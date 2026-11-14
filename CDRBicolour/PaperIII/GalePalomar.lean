/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.Defs

/-!
# `GaleInt` from the registered Palomar statement

`PalomarFeasibilityInt` is, verbatim, the statement `GaleHoffman.feasibility_int` of Palomar
**PALOMAR-2026-11-06-000015 v1** (repository `jtraverso/gale-hoffman-feasibility` @ `fa52c29`),
specialised to node types in `Type`. It uses inflow demands with inequality and the cut condition
`d(Sᶜ) ≤ c(S, Sᶜ)`; `GaleInt` uses exact outflow with `Σ d = 0` and `d(S) ≤ c(S, Sᶜ)`.
The bridge takes `-d` as the Palomar demand.
-/

@[expose] public section

namespace CDRBicolour.PaperIII

open Finset

/-- `GaleHoffman.feasibility_int` (Palomar PALOMAR-2026-11-06-000015 v1), at `Type`. -/
def PalomarFeasibilityInt : Prop :=
  ∀ (N : Type) [Fintype N] [DecidableEq N] (c : N → N → ℤ), (∀ x y, 0 ≤ c x y) →
    ∀ (d : N → ℤ),
    ((∃ f : N → N → ℤ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y)

theorem galeInt_of_palomar (h : PalomarFeasibilityInt) : GaleInt := by
  intro N _ _ c hc d hd
  have key := h N c hc (fun x => -d x)
  beta_reduce at key
  have hcompl : ∀ S : Finset N, ∑ x ∈ Sᶜ, -d x = ∑ x ∈ S, d x := fun S => by
    rw [sum_neg_distrib]
    have := sum_compl_add_sum S d
    rw [hd] at this; linarith
  have hanti : ∀ f : N → N → ℤ, (∀ x y, f x y + f y x = 0) →
      ∀ x, ∑ y, f y x = -∑ y, f x y := fun f hf x => by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun y _ => by linarith [hf x y]
  have htot : ∀ f : N → N → ℤ, (∀ x y, f x y + f y x = 0) → ∑ x, ∑ y, f x y = 0 :=
    fun f hf => by
      have h1 : ∑ x, ∑ y, f x y = ∑ x, ∑ y, f y x := sum_comm
      have h2 : ∑ x, ∑ y, f y x = -∑ x, ∑ y, f x y := by
        rw [← sum_neg_distrib]; exact sum_congr rfl fun x _ => hanti f hf x
      linarith
  constructor
  · rintro ⟨f, hf1, hf2, hf3⟩ S
    have hf1' : ∀ x y, f x y + f y x = 0 := fun x y => by linarith [hf1 x y]
    rw [← hcompl S]
    exact key.1 ⟨f, hf1', hf2, fun x => le_of_eq (by rw [hanti f hf1' x, hf3 x])⟩ S
  · intro hS
    obtain ⟨f, hf1, hf2, hf3⟩ := key.2 (fun S => by rw [hcompl S]; exact hS S)
    refine ⟨f, fun x y => by linarith [hf1 x y], hf2, fun x => ?_⟩
    have hle : ∀ x, ∑ y, f x y ≤ d x := fun x => by
      have := hf3 x; rw [hanti f hf1 x] at this; linarith
    have hsum : ∑ x, (d x - ∑ y, f x y) = 0 := by
      rw [sum_sub_distrib, hd, htot f hf1]; ring
    have hz := (sum_eq_zero_iff_of_nonneg (fun x _ => sub_nonneg.2 (hle x))).1 hsum x
      (mem_univ x)
    linarith

end CDRBicolour.PaperIII
