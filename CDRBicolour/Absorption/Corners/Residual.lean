/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Plant
public import CDRBicolour.Absorption.Corners.Lattice3
public import CDRBicolour.Absorption.Corners.Seed3

/-!
# From leave degrees to the residual conditions (item 3, corners)

For a packing `P` with leave `L = ⋃ E(T)`:

* `res_count`: the residual neighbours of `u` with label `Y` and the leave neighbours with label `Y`
  partition the other points of class `Y`;
* `ell_wpi_res`: `π_u(𝟏_{E∖L})` is the number of residual neighbours of `u` in its own class
  minus the number in the next class, so balance in the sense of H1 is balance of degrees;
* `LN_union`: leave neighbourhoods of a union of packings.
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset SimpleGraph TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

theorem not_mem_diag (P : Finset (Finset V)) (u : V) : s(u, u) ∉ P.biUnion triEdges := by
  intro h
  obtain ⟨T, -, hT⟩ := mem_biUnion.1 h
  exact triEdges_nondiag T _ hT (Sym2.mk_isDiag_iff.2 rfl)

/-- **Residual and leave neighbours partition the class.** -/
theorem res_count (P : Finset (Finset V)) (u : V) (Y : Fin 3) :
    #(univ.filter fun v => (rG (P.biUnion triEdges)).Adj u v ∧ lab v = Y) + #(LN lab P u Y) =
      csz lab Y - if lab u = Y then 1 else 0 := by
  have hsplit : (univ.filter fun v => lab v = Y ∧ v ≠ u) =
      (univ.filter fun v => (rG (P.biUnion triEdges)).Adj u v ∧ lab v = Y) ∪ LN lab P u Y := by
    ext v
    simp only [LN, mem_filter, mem_univ, true_and, mem_union, rG_adj]
    constructor
    · rintro ⟨hv, hne⟩
      by_cases hL : s(u, v) ∈ P.biUnion triEdges
      · exact Or.inr ⟨hv, hL⟩
      · exact Or.inl ⟨⟨hL, Ne.symm hne⟩, hv⟩
    · rintro (⟨⟨-, hne⟩, hv⟩ | ⟨hv, hL⟩)
      · exact ⟨hv, Ne.symm hne⟩
      · refine ⟨hv, fun e => ?_⟩
        subst e; exact not_mem_diag P v hL
  have hdisj : Disjoint (univ.filter fun v => (rG (P.biUnion triEdges)).Adj u v ∧ lab v = Y)
      (LN lab P u Y) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [LN, mem_filter, mem_univ, true_and, rG_adj] at h1 h2
    exact h1.1.1 h2.2
  rw [← card_union_of_disjoint hdisj, ← hsplit]
  unfold csz
  split_ifs with hu
  · rw [show (univ.filter fun v => lab v = Y ∧ v ≠ u) = (univ.filter fun v => lab v = Y).erase u by
      ext v; simp [and_comm], card_erase_of_mem (by simp [hu])]
  · rw [Nat.sub_zero]
    congr 1; ext v
    simp only [mem_filter, mem_univ, true_and, and_iff_left_iff_imp]
    rintro hv rfl; exact hu hv

theorem LN_union (P Q : Finset (Finset V)) (u : V) (Y : Fin 3) :
    LN lab (P ∪ Q) u Y = LN lab P u Y ∪ LN lab Q u Y := by
  ext v
  simp only [LN, mem_filter, mem_univ, true_and, mem_union]
  rw [union_biUnion, mem_union]
  tauto

/-- **`π_u` of the residual edge set** in terms of residual degrees. -/
theorem ell_wpi_res (L : Finset (Sym2 V)) (u : V) :
    ellG' (wpi lab u) (fun e : E0 V => if e.1 ∈ L then 0 else 1) =
      (#(univ.filter fun v => (rG L).Adj u v ∧ lab v = lab u) : ℝ) -
        #(univ.filter fun v => (rG L).Adj u v ∧ lab v = lab u + 1) := by
  set S : Finset (Sym2 V) := (univ.erase u).image fun v => s(u, v) with hS
  have hSd : ∀ f ∈ S, ¬ f.IsDiag := by
    intro f hf
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hf
    rw [Sym2.mk_isDiag_iff]; exact fun e => (mem_erase.1 hv).1 e.symm
  have hz : ∀ e : Sym2 V, u ∉ e → wpi lab u e = 0 := by
    intro e hu
    induction e using Sym2.ind with
    | _ p q =>
    have hp : p ≠ u := fun h => hu (by rw [h]; simp)
    have hq : q ≠ u := fun h => hu (by rw [h]; simp)
    simp [wpi_mk, hp, hq]
  have hmem : ∀ e : E0 V, u ∈ e.1 → e.1 ∈ S := by
    rintro ⟨e, hed⟩ hu
    induction e using Sym2.ind with
    | _ p q =>
    have hpq : p ≠ q := by simpa using hed
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact mem_image.2 ⟨q, mem_erase.2 ⟨Ne.symm hpq, mem_univ _⟩, rfl⟩
    · exact mem_image.2 ⟨p, mem_erase.2 ⟨hpq, mem_univ _⟩, Sym2.eq_swap⟩
  have h1 : ellG' (wpi lab u) (fun e : E0 V => if e.1 ∈ L then 0 else 1) =
      ∑ e : E0 V, (if e.1 ∈ S then wpi lab u e.1 * (if e.1 ∈ L then 0 else 1) else 0) := by
    simp only [ellG', LinearMap.coe_mk, AddHom.coe_mk]
    refine sum_congr rfl fun e _ => ?_
    by_cases hS' : e.1 ∈ S
    · rw [if_pos hS']
    · rw [if_neg hS', hz e.1 (fun hu => hS' (hmem e hu)), zero_mul]
  rw [h1, sum_E0 (fun f => wpi lab u f * if f ∈ L then 0 else 1) S hSd, hS, sum_image]
  · have h2 : ∀ v ∈ univ.erase u, wpi lab u s(u, v) * (if s(u, v) ∈ L then (0 : ℝ) else 1) =
        (if (rG L).Adj u v ∧ lab v = lab u then 1 else 0) -
          (if (rG L).Adj u v ∧ lab v = lab u + 1 then 1 else 0) := by
      intro v hv
      have hvu : v ≠ u := (mem_erase.1 hv).1
      have n1 : lab u ≠ lab u + 1 := (fin3_ne_add1 _).symm
      have hw : wpi lab u s(u, v) = chi lab u v := by rw [wpi_mk, if_pos rfl, if_neg hvu, add_zero]
      rw [hw]
      unfold chi
      set A := (rG L).Adj u v
      by_cases hL : s(u, v) ∈ L
      · have nA : ¬ A := fun h => (rG_adj.1 h).1 hL
        rw [if_pos hL, mul_zero, if_neg (show ¬ (A ∧ lab v = lab u) from fun h => nA h.1),
          if_neg (show ¬ (A ∧ lab v = lab u + 1) from fun h => nA h.1), sub_zero]
      · have hadj : A := rG_adj.2 ⟨hL, Ne.symm hvu⟩
        rw [if_neg hL, mul_one]
        by_cases h1 : lab v = lab u
        · rw [if_pos h1, if_pos (show A ∧ lab v = lab u from ⟨hadj, h1⟩),
            if_neg (show ¬ (A ∧ lab v = lab u + 1) from fun h => n1 (h1.symm.trans h.2))]
          ring
        · rw [if_neg h1, if_neg (show ¬ (A ∧ lab v = lab u) from fun h => h1 h.2)]
          by_cases h2 : lab v = lab u + 1
          · rw [if_pos h2, if_pos (show A ∧ lab v = lab u + 1 from ⟨hadj, h2⟩)]; ring
          · rw [if_neg h2, if_neg (show ¬ (A ∧ lab v = lab u + 1) from fun h => h2 h.2)]; ring
    rw [sum_congr rfl h2, sum_sub_distrib, sum_boole, sum_boole, filter_erase, filter_erase,
      erase_eq_of_notMem (by simp), erase_eq_of_notMem (by simp)]
  · intro v _ v' _ h
    rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

end CDRBicolour.Absorption.Corners
