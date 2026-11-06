/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Defs
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Plantholt's Lemma 1.3 (external theorem E1), formalized

Statement (as quoted by Bongard–Hoffmann–Volkmann, Australas. J. Combin. 28 (2003)):
*Let `G` have even order `n` and `δ(G) > n/2`. If an odd set `S` (`|S| ≥ 3`) induces a
`Δ(G)`-full or `Δ(G)`-overfull subgraph, then `S = V(G) - x` for a vertex `x`.*

Proof by counting darts: with `s = |S|`, `m = |Sᶜ|`, `I`, `J` the darts inside `S`, `Sᶜ`
and `c` the darts across,
`I + c ≤ sΔ`, `Δ(s-1) ≤ I ≤ s(s-1)`, `mδ ≤ J + c`, `J ≤ m(m-1)`.
Hence `c ≤ Δ ≤ s` and `m(δ - m + 1) ≤ s`; with `2δ > s + m` this forces `m ≤ 1`, and `m`
is odd.
-/

@[expose] public section

namespace CDRBicolour

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Darts with both ends in `S`. -/
def innerDarts (S : Finset V) : Finset G.Dart :=
  univ.filter fun d => d.fst ∈ S ∧ d.snd ∈ S

/-- Darts leaving `S`. -/
def cutDarts (S : Finset V) : Finset G.Dart :=
  univ.filter fun d => d.fst ∈ S ∧ d.snd ∉ S

theorem sum_degree_eq_card_darts (S : Finset V) :
    ∑ v ∈ S, G.degree v = (univ.filter fun d : G.Dart => d.fst ∈ S).card := by
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := S)
    (by intro d hd; simpa using hd)]
  refine sum_congr rfl fun v hv => ?_
  rw [← G.dart_fst_fiber_card_eq_degree v, filter_filter]
  congr 1
  apply filter_congr
  intro d _
  constructor
  · intro h; first | exact h.2 | exact ⟨by rw [h]; exact hv, h⟩
  · intro h; first | exact h.2 | exact ⟨by rw [h]; exact hv, h⟩

theorem card_fst_mem_eq (S : Finset V) :
    (univ.filter fun d : G.Dart => d.fst ∈ S).card =
      (innerDarts G S).card + (cutDarts G S).card := by
  rw [← card_filter_add_card_filter_not (fun d : G.Dart => d.snd ∈ S)]
  unfold innerDarts cutDarts
  rw [filter_filter, filter_filter]

theorem fst_mem_edge (d : G.Dart) : d.fst ∈ d.edge := Sym2.mem_mk_left _ _
theorem snd_mem_edge (d : G.Dart) : d.snd ∈ d.edge := Sym2.mem_mk_right _ _

theorem card_innerDarts (S : Finset V) :
    (innerDarts G S).card = 2 * (edgesIn G S).card := by
  calc (innerDarts G S).card
      = ∑ e ∈ edgesIn G S, ((innerDarts G S).filter fun d => d.edge = e).card := by
        refine card_eq_sum_card_fiberwise ?_
        intro d hd
        simp only [innerDarts, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hd
        simp only [edgesIn, coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq]
        refine ⟨d.edge_mem, fun v hv => ?_⟩
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hd.1
        · exact hd.2
    _ = ∑ _e ∈ edgesIn G S, 2 := by
        refine sum_congr rfl fun e he => ?_
        have he' := he
        simp only [edgesIn, mem_filter, SimpleGraph.mem_edgeFinset] at he'
        rw [← G.dart_edge_fiber_card e he'.1]
        congr 1
        ext d
        simp only [innerDarts, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨-, h⟩; exact h
        · intro h
          refine ⟨⟨he'.2 _ (h ▸ fst_mem_edge G d), he'.2 _ (h ▸ snd_mem_edge G d)⟩, h⟩
    _ = 2 * (edgesIn G S).card := by rw [sum_const, smul_eq_mul, mul_comm]

theorem card_innerDarts_le (S : Finset V) :
    (innerDarts G S).card ≤ S.card * S.card - S.card := by
  rw [← offDiag_card]
  refine card_le_card_of_injOn (fun d : G.Dart => d.toProd) ?_ ?_
  · intro d hd
    simp only [innerDarts, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hd
    simp only [coe_offDiag, Set.mem_offDiag, mem_coe]
    exact ⟨hd.1, hd.2, d.adj.ne⟩
  · intro d₁ _ d₂ _ h
    exact SimpleGraph.Dart.ext _ _ h

theorem card_cutDarts_compl (S : Finset V) :
    (cutDarts G S).card = (cutDarts G Sᶜ).card := by
  refine card_nbij' (fun d => d.symm) (fun d => d.symm) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [cutDarts, coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_compl,
      not_not] at hd ⊢
    exact ⟨hd.2, hd.1⟩
  · intro d hd
    simp only [cutDarts, coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_compl,
      not_not] at hd ⊢
    exact ⟨hd.2, hd.1⟩
  · intro d _; exact d.symm_symm
  · intro d _; exact d.symm_symm

/-- **Plantholt's Lemma 1.3** (E1). -/
theorem plantholt_lemma_1_3 : Plantholt_Lemma_1_3 := by
  intro W _ _ G _ hEven hdeg S hS
  obtain ⟨hodd, h3, hfull⟩ := hS
  -- counting facts
  have hsm : S.card + Sᶜ.card = Fintype.card W := card_add_card_compl S
  have hI := card_innerDarts G S
  have hIle := card_innerDarts_le G S
  have hJle := card_innerDarts_le G Sᶜ
  have hcut := card_cutDarts_compl G S
  have hdegS : ∑ v ∈ S, G.degree v ≤ S.card * G.maxDegree := by
    calc ∑ v ∈ S, G.degree v ≤ ∑ _v ∈ S, G.maxDegree :=
          sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = S.card * G.maxDegree := by rw [sum_const, smul_eq_mul]
  have hdegC : Sᶜ.card * G.minDegree ≤ ∑ v ∈ Sᶜ, G.degree v := by
    calc Sᶜ.card * G.minDegree = ∑ _v ∈ Sᶜ, G.minDegree := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ Sᶜ, G.degree v := sum_le_sum fun v _ => G.minDegree_le_degree v
  rw [sum_degree_eq_card_darts, card_fst_mem_eq] at hdegS hdegC
  have hδΔ := G.minDegree_le_maxDegree
  -- name the quantities
  set s := S.card with hs
  set m := Sᶜ.card with hm
  set I := (innerDarts G S).card
  set J := (innerDarts G Sᶜ).card
  set c := (cutDarts G S).card
  set Δ := G.maxDegree
  set δ := G.minDegree
  set e := (edgesIn G S).card
  rw [← hcut] at hdegC
  -- parity of `m`
  have hmodd : Odd m := by
    obtain ⟨k, hk⟩ := hEven
    obtain ⟨j, hj⟩ := hodd
    exact ⟨k - j - 1, by omega⟩
  -- natural-number forms
  have hΔs : Δ * (s - 1) + Δ = Δ * s := by
    have h1 : s = (s - 1) + 1 := by omega
    conv_rhs => rw [h1]
    ring
  have N3 : J + m ≤ m * m := by have := Nat.le_mul_self m; omega
  have N4 : I + s ≤ s * s := by have := Nat.le_mul_self s; omega
  have N5 : Δ * s ≤ I + Δ := by omega
  have N6 : s + m + 1 ≤ 2 * δ := by omega
  -- `m ≤ 1`
  have key : m ≤ 1 := by
    by_contra hm1
    have hm3 : 3 ≤ m := by obtain ⟨j, hj⟩ := hmodd; omega
    have F1 : (I : ℤ) + c ≤ s * Δ := by exact_mod_cast hdegS
    have F2 : (m : ℤ) * δ ≤ J + c := by exact_mod_cast hdegC
    have F3 : (J : ℤ) + m ≤ m * m := by exact_mod_cast N3
    have F4 : (I : ℤ) + s ≤ s * s := by exact_mod_cast N4
    have F5 : (s : ℤ) * Δ ≤ I + Δ := by rw [mul_comm]; exact_mod_cast N5
    have F6 : (s : ℤ) + m + 1 ≤ 2 * δ := by exact_mod_cast N6
    have F7 : (δ : ℤ) ≤ Δ := by exact_mod_cast hδΔ
    have F8 : (3 : ℤ) ≤ s := by exact_mod_cast h3
    have F9 : (3 : ℤ) ≤ m := by exact_mod_cast hm3
    have Hc : (c : ℤ) ≤ Δ := by linarith
    have HΔ : (Δ : ℤ) ≤ s := by
      by_contra hlt
      push_neg at hlt
      have := mul_lt_mul_of_pos_right hlt (show (0 : ℤ) < s - 1 by linarith)
      nlinarith
    have Hsm : (m : ℤ) + 1 ≤ s := by linarith
    have A : (m : ℤ) * ((s : ℤ) + m + 1) ≤ m * (2 * δ) :=
      mul_le_mul_of_nonneg_left F6 (by linarith)
    have B : (0 : ℤ) ≤ ((m : ℤ) - 2) * ((s : ℤ) - (m + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hm1 : m = 1 := by obtain ⟨j, hj⟩ := hmodd; omega
  obtain ⟨x, hx⟩ := card_eq_one.1 hm1
  refine ⟨x, ?_⟩
  ext v
  have hv : v ∈ Sᶜ ↔ v = x := by rw [hx, mem_singleton]
  rw [mem_compl] at hv
  rw [mem_erase]
  simp only [mem_univ, and_true]
  constructor
  · intro h hvx; exact (hv.2 hvx) h
  · intro h; by_contra h'; exact h (hv.1 h')

end CDRBicolour
