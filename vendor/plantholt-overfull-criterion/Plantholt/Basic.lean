/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Plantholt.Dirac

/-!
# Plantholt 2004: induced edge counts, fullness, and Lemma 2.1

`inside G S` is the subgraph induced on `S`, as a graph on `V`; `eIn G S` is its number of edges.
`NoOverfull G D`: no odd set `S` has `2 e(S) > D (|S| − 1)`.

`card_add_one_of_full` (**Plantholt, Lemma 2.1**): if `|V|` is even, every degree is between `δ'`
and `D ≤ |V| − 1`, and `2δ' ≥ |V| + 2`, then an odd set `S` with `|S| ≥ 3` and
`2 e(S) ≥ D (|S| − 1)` has `|S| = |V| − 1`.
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The subgraph induced on `S`, as a graph on `V`. -/
def inside (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm.symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The number of edges with both ends in `S`. -/
noncomputable def eIn (G : SimpleGraph V) (S : Finset V) : ℕ := #(inside G S).edgeFinset

/-- No odd set spans more than `D (|S| − 1) / 2` edges. -/
def NoOverfull (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∀ S : Finset V, Odd #S → 2 * eIn G S ≤ D * (#S - 1)

/-- `S` spans a `D`-full (or overfull) subgraph. -/
def IsFull (G : SimpleGraph V) (D : ℕ) (S : Finset V) : Prop :=
  3 ≤ #S ∧ Odd #S ∧ D * (#S - 1) ≤ 2 * eIn G S

variable (G : SimpleGraph V)

/-- Neighbours of `v` in `S`. -/
noncomputable def nbIn (S : Finset V) (v : V) : Finset V := (G.neighborFinset v).filter (· ∈ S)

theorem inside_adj {S : Finset V} {u v : V} :
    (inside G S).Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := Iff.rfl

theorem neighborFinset_inside (S : Finset V) (v : V) :
    (inside G S).neighborFinset v = if v ∈ S then nbIn G S v else ∅ := by
  ext u
  rw [mem_neighborFinset, inside_adj]
  split_ifs with hv
  · simp [nbIn, hv]
  · simp [hv]

theorem degree_inside (S : Finset V) (v : V) :
    (inside G S).degree v = if v ∈ S then #(nbIn G S v) else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_inside]
  split_ifs <;> simp

/-- Handshake inside `S`. -/
theorem two_mul_eIn (S : Finset V) : 2 * eIn G S = ∑ v ∈ S, #(nbIn G S v) := by
  rw [eIn, ← sum_degrees_eq_twice_card_edges]
  rw [← sum_filter_add_sum_filter_not univ (· ∈ S)]
  have h1 : ∑ v ∈ univ.filter (· ∈ S), (inside G S).degree v = ∑ v ∈ S, #(nbIn G S v) := by
    rw [filter_mem_eq_inter, univ_inter]
    exact sum_congr rfl fun v hv => by rw [degree_inside, if_pos hv]
  have h2 : ∑ v ∈ univ.filter (· ∉ S), (inside G S).degree v = 0 :=
    sum_eq_zero fun v hv => by rw [degree_inside, if_neg (mem_filter.1 hv).2]
  rw [h1, h2, add_zero]

theorem eIn_univ : eIn G univ = #G.edgeFinset := by
  rw [eIn]
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [mem_edgeFinset, mem_edgeFinset, mem_edgeSet, mem_edgeSet, inside_adj]
    simp

theorem nbIn_univ (v : V) : nbIn G univ v = G.neighborFinset v := by
  simp [nbIn]

/-- Deleting one vertex. -/
theorem eIn_erase_add (x : V) : eIn G (univ.erase x) + G.degree x = #G.edgeFinset := by
  have h := two_mul_eIn G (univ.erase x)
  have hu := two_mul_eIn G univ
  rw [eIn_univ] at hu
  rw [← sum_erase_add _ _ (mem_univ x)] at hu
  have hx : #(nbIn G univ x) = G.degree x := by rw [nbIn_univ, card_neighborFinset_eq_degree]
  have hsplit : ∀ v ∈ univ.erase x, #(nbIn G univ v) =
      #(nbIn G (univ.erase x) v) + if G.Adj v x then 1 else 0 := by
    intro v _
    have he : nbIn G (univ.erase x) v = (G.neighborFinset v).erase x := by
      ext u; simp [nbIn, mem_erase, and_comm]
    rw [nbIn_univ, he, card_erase_eq_ite]
    by_cases hvx : G.Adj v x
    · have hx : x ∈ G.neighborFinset v := by rw [mem_neighborFinset]; exact hvx
      rw [if_pos hx, if_pos hvx]
      have := card_pos.2 ⟨x, hx⟩; omega
    · have hx : x ∉ G.neighborFinset v := by rw [mem_neighborFinset]; exact hvx
      rw [if_neg hx, if_neg hvx, add_zero]
  rw [sum_congr rfl hsplit, sum_add_distrib, ← h, hx] at hu
  have hdeg : ∑ v ∈ univ.erase x, (if G.Adj v x then 1 else 0) = G.degree x := by
    rw [← sum_filter, sum_const, smul_eq_mul, mul_one, ← card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
    constructor
    · rintro ⟨-, h⟩; exact h.symm
    · intro h; exact ⟨h.ne', h.symm⟩
  rw [hdeg] at hu
  omega

/-- The coboundary of `S`, counted from `S`. -/
noncomputable def cob (S : Finset V) : ℕ := ∑ v ∈ S, #((G.neighborFinset v).filter (· ∉ S))

theorem sum_degree_eq (S : Finset V) : ∑ v ∈ S, G.degree v = 2 * eIn G S + cob G S := by
  rw [two_mul_eIn, cob, ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  rw [nbIn, card_filter_add_card_filter_not, card_neighborFinset_eq_degree]

/-- The coboundary counted from the complement. -/
theorem cob_eq_compl (S : Finset V) :
    cob G S = ∑ u ∈ Sᶜ, #((G.neighborFinset u).filter (· ∈ S)) := by
  rw [cob]
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := S) (t := Sᶜ)
    (r := fun v u => G.Adj v u)
  convert h using 2 with v hv u hu
  · congr 1
    ext u
    simp only [bipartiteAbove, mem_filter, mem_neighborFinset, mem_compl]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
  · congr 1
    ext v
    simp only [bipartiteBelow, mem_filter, mem_neighborFinset]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩

/-- A vertex outside `S` sends at least `deg − (|Sᶜ| − 1)` edges into `S`. -/
theorem le_card_filter_mem {S : Finset V} {u : V} (hu : u ∈ Sᶜ) :
    G.degree u ≤ #((G.neighborFinset u).filter (· ∈ S)) + (#Sᶜ - 1) := by
  rw [← card_neighborFinset_eq_degree, ← card_filter_add_card_filter_not (p := (· ∈ S))]
  have : #((G.neighborFinset u).filter (· ∉ S)) ≤ #(Sᶜ.erase u) := by
    apply card_le_card
    intro w hw
    simp only [mem_filter, mem_neighborFinset] at hw
    simp only [mem_erase, mem_compl]
    exact ⟨hw.1.ne', hw.2⟩
  rw [card_erase_of_mem hu] at this
  omega

theorem le_card_filter_not_mem {S : Finset V} {v : V} (hv : v ∈ S) :
    G.degree v ≤ #((G.neighborFinset v).filter (· ∉ S)) + (#S - 1) := by
  rw [← card_neighborFinset_eq_degree, ← card_filter_add_card_filter_not (p := (· ∉ S))]
  have : #((G.neighborFinset v).filter (fun u => ¬ u ∉ S)) ≤ #(S.erase v) := by
    apply card_le_card
    intro w hw
    simp only [mem_filter, mem_neighborFinset, not_not] at hw
    simp only [mem_erase]
    exact ⟨hw.1.ne', hw.2⟩
  rw [card_erase_of_mem hv] at this
  omega

/-- Arithmetic core of Lemma 2.1. -/
theorem lemma21_arith {n k s δ' c : ℕ} (hn : k + s = n) (hk : 3 ≤ k) (hs : 3 ≤ s)
    (hδ : n + 2 ≤ 2 * δ') (hc : c + 1 ≤ n) (hck : k * δ' ≤ c + k * (k - 1))
    (hcs : s * δ' ≤ c + s * (s - 1)) : False := by
  rcases le_total k s with hks | hks
  · have h1 : (k : ℤ) * δ' ≤ c + k * ((k : ℤ) - 1) := by
      have h := hck
      zify [show 1 ≤ k by omega] at h
      exact h
    have : (0 : ℤ) ≤ ((k : ℤ) - 2) * ((n : ℤ) - 2 * k) :=
      mul_nonneg (by omega) (by omega)
    have h2 : (n : ℤ) + 2 ≤ 2 * δ' := by exact_mod_cast hδ
    have h3 : (c : ℤ) + 1 ≤ n := by exact_mod_cast hc
    nlinarith
  · have h1 : (s : ℤ) * δ' ≤ c + s * ((s : ℤ) - 1) := by
      have h := hcs
      zify [show 1 ≤ s by omega] at h
      exact h
    have : (0 : ℤ) ≤ ((s : ℤ) - 2) * ((n : ℤ) - 2 * s) :=
      mul_nonneg (by omega) (by omega)
    have h2 : (n : ℤ) + 2 ≤ 2 * δ' := by exact_mod_cast hδ
    have h3 : (c : ℤ) + 1 ≤ n := by exact_mod_cast hc
    nlinarith

/-- **Plantholt, Lemma 2.1.** -/
theorem card_add_one_of_full {D δ' : ℕ} (hev : Even (Fintype.card V))
    (hmax : ∀ v, G.degree v ≤ D) (hmin : ∀ v, δ' ≤ G.degree v)
    (hD : D + 1 ≤ Fintype.card V) (hδ : Fintype.card V + 2 ≤ 2 * δ')
    {S : Finset V} (hS : IsFull G D S) : #S + 1 = Fintype.card V := by
  obtain ⟨hs3, hodd, hfull⟩ := hS
  have hcard : #S + #Sᶜ = Fintype.card V := card_add_card_compl S
  -- the coboundary is at most `D`
  have hsum := sum_degree_eq G S
  have hsumle : ∑ v ∈ S, G.degree v ≤ #S * D := by
    calc ∑ v ∈ S, G.degree v ≤ ∑ _v ∈ S, D := sum_le_sum fun v _ => hmax v
      _ = #S * D := by rw [sum_const, smul_eq_mul]
  have hcobD : cob G S ≤ D := by
    have : D * (#S - 1) + D = #S * D := by
      rw [mul_comm #S D, ← Nat.mul_succ]; congr 1; omega
    omega
  -- lower bounds
  have hlo1 : #Sᶜ * δ' ≤ cob G S + #Sᶜ * (#Sᶜ - 1) := by
    rw [cob_eq_compl]
    calc #Sᶜ * δ' = ∑ _u ∈ Sᶜ, δ' := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ Sᶜ, (#((G.neighborFinset u).filter (· ∈ S)) + (#Sᶜ - 1)) :=
          sum_le_sum fun u hu => (hmin u).trans (le_card_filter_mem G hu)
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have hlo2 : #S * δ' ≤ cob G S + #S * (#S - 1) := by
    rw [cob]
    calc #S * δ' = ∑ _v ∈ S, δ' := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ S, (#((G.neighborFinset v).filter (· ∉ S)) + (#S - 1)) :=
          sum_le_sum fun v hv => (hmin v).trans (le_card_filter_not_mem G hv)
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  -- the complement has odd size
  have hoddc : Odd #Sᶜ := by
    rcases hev with ⟨t, ht⟩
    rcases hodd with ⟨r, hr⟩
    exact ⟨t - r - 1, by omega⟩
  by_contra hne
  have hk3 : 3 ≤ #Sᶜ := by
    rcases hoddc with ⟨r, hr⟩
    omega
  exact lemma21_arith (n := Fintype.card V) (by omega) hk3 hs3 hδ (by omega) hlo1 hlo2

end Plantholt
