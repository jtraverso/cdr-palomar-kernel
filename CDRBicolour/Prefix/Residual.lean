/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.Prefix

/-!
# Degrees of the residual `F`

Every `B`-row missing `v` pairs `v` with exactly one partner, and different rows use different
pairs; hence `deg_F v + mult v = |C| - 1` (`resid_degree_add_mult`).
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.L184

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  {G : SimpleGraph Rw} [DecidableRel G.Adj] {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}

theorem unusedGraph_adj_iff {x y : Cl} :
    (unusedGraph M).Adj x y ↔ x ≠ y ∧ ∀ j, s(x, y) ∉ M j := by
  simp only [unusedGraph, SimpleGraph.fromRel_adj, ne_eq, Sym2.eq_swap (a := y)]
  tauto

/-- **Degrees of an unused-pairs graph**: `deg v + mult v = |Cl| - 1`. -/
theorem unused_degree_add_mult (hM : ∀ j, IsPerfectPairing (M j) (miss G χ j))
    (hMd : PairDisjoint M) (v : Cl) :
    (unusedGraph M).degree v + mult G χ v = Fintype.card Cl - 1 := by
  classical
  set Q := (univ.erase v).filter fun u => ∃ j, s(v, u) ∈ M j with hQ
  -- neighbours of `v` in `F` are the points `≠ v` outside `Q`
  have hnb : (unusedGraph M).neighborFinset v = (univ.erase v).filter fun u => ¬ ∃ j, s(v, u) ∈ M j := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, unusedGraph_adj_iff, mem_filter, mem_erase, mem_univ,
      and_true, not_exists]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩
  have hsplit := card_filter_add_card_filter_not (s := univ.erase v)
    (fun u => ∃ j, s(v, u) ∈ M j)
  rw [← hQ, ← hnb, SimpleGraph.card_neighborFinset_eq_degree, card_erase_of_mem (mem_univ v),
    card_univ] at hsplit
  -- `|Q| = mult v`
  have hQcard : Q.card = mult G χ v := by
    symm
    unfold mult
    refine card_bij (fun j hj => Sym2.Mem.other ((hM j).2.2 v (mem_filter.1 hj).2).exists.choose_spec.2) ?_ ?_ ?_
    · intro j hj
      set h := ((hM j).2.2 v (mem_filter.1 hj).2).exists.choose_spec
      have hspec := Sym2.other_spec h.2
      rw [hQ, mem_filter, mem_erase]
      refine ⟨⟨?_, mem_univ _⟩, j, by rw [hspec]; exact h.1⟩
      intro heq
      have hd := (hM j).1 _ h.1
      rw [← hspec, heq] at hd
      exact hd (Sym2.mk_isDiag_iff.2 rfl)
    · intro j hj j' hj' heq
      set h := ((hM j).2.2 v (mem_filter.1 hj).2).exists.choose_spec
      set h' := ((hM j').2.2 v (mem_filter.1 hj').2).exists.choose_spec
      have e1 := Sym2.other_spec h.2
      have e2 := Sym2.other_spec h'.2
      have hp : ((hM j).2.2 v (mem_filter.1 hj).2).exists.choose =
          ((hM j').2.2 v (mem_filter.1 hj').2).exists.choose := by
        rw [← e1, ← e2, heq]
      exact row_of_pair_unique hMd h.1 (hp ▸ h'.1)
    · intro u hu
      rw [hQ, mem_filter] at hu
      obtain ⟨-, j, hj⟩ := hu
      have hvm : v ∈ miss G χ j := (hM j).2.1 _ hj v (Sym2.mem_mk_left _ _)
      refine ⟨j, mem_filter.2 ⟨mem_univ _, hvm⟩, ?_⟩
      set h := ((hM j).2.2 v hvm).exists.choose_spec
      have hp : ((hM j).2.2 v hvm).exists.choose = s(v, u) :=
        ((hM j).2.2 v hvm).unique h ⟨hj, Sym2.mem_mk_left _ _⟩
      have e1 := Sym2.other_spec h.2
      exact Sym2.congr_right.1 (e1.trans hp)
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] {col : V → Fin 3} {d : PrefixData col}

theorem resid_degree_add_mult (hv : d.Valid) (v : CType col) :
    (resid d.MB).degree v + mult (GB d.MA) d.χB v = Fintype.card (CType col) - 1 :=
  unused_degree_add_mult hv.hMB hv.hMBd v

theorem GB_degree_add_mult (hv : d.Valid) (v : BType col) :
    (GB d.MA).degree v + mult (GA d.μ) d.χA v = Fintype.card (BType col) - 1 :=
  unused_degree_add_mult hv.hMA hv.hMAd v

end CDRBicolour.Prefix
