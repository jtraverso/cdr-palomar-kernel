/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Plantholt.Tools
public import Mathlib.Tactic.Linarith

/-!
# Plantholt 2004: degree sums, deficiencies, and the absence of overfull sets

With `Σ = Σ_v deg v`, the set `V − w` spans `(Σ − 2 deg w)/2` edges, so for an even order `n` with
minimum degree above `n/2` (Lemma 2.1) the absence of `D`-overfull sets reduces to
`Σ ≤ 2 deg w + D (n − 2)` for every `w` (`noOverfull_of_erase`). Three vertices of minimum
degree force this (`erase_bound_of_three`).
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The degree sum. -/
noncomputable def dsum : ℕ := ∑ v, G.degree v

/-- The deficiency `Σ_v (D − deg v)`. -/
noncomputable def dfc (D : ℕ) : ℕ := ∑ v, (D - G.degree v)

theorem dsum_eq_two_mul : dsum G = 2 * #G.edgeFinset := sum_degrees_eq_twice_card_edges G

theorem two_mul_eIn_erase (w : V) : 2 * eIn G (univ.erase w) + 2 * G.degree w = dsum G := by
  have h := eIn_erase_add G w
  rw [dsum_eq_two_mul]
  omega

theorem dfc_add_dsum {D : ℕ} (hmax : ∀ v, G.degree v ≤ D) :
    dfc G D + dsum G = D * Fintype.card V := by
  rw [dfc, dsum, ← sum_add_distrib, sum_congr rfl fun v _ => Nat.sub_add_cancel (hmax v),
    sum_const, card_univ, smul_eq_mul, mul_comm]

theorem dfc_ge_three {D : ℕ} {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (D - G.degree a) + (D - G.degree b) + (D - G.degree c) ≤ dfc G D := by
  have hsub : ({a, b, c} : Finset V) ⊆ univ := subset_univ _
  have := sum_le_sum_of_subset (f := fun v => D - G.degree v) hsub
  rw [sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton] at this
  rw [dfc]
  omega

theorem dfc_erase {D : ℕ} (x : V) :
    ∑ v ∈ univ.erase x, (D - G.degree v) + (D - G.degree x) = dfc G D :=
  sum_erase_add _ _ (mem_univ x)

/-- Some vertex other than `x` is below `D`, when the deficiency away from `x` is positive. -/
theorem exists_lt_of_dfc {D : ℕ} (x : V) (h : 0 < ∑ v ∈ univ.erase x, (D - G.degree v)) :
    ∃ v, v ≠ x ∧ G.degree v < D := by
  by_contra hne
  push_neg at hne
  have : ∑ v ∈ univ.erase x, (D - G.degree v) = 0 :=
    sum_eq_zero fun v hv => by have := hne v (ne_of_mem_erase hv); omega
  omega

theorem two_mul_eIn_le_card (S : Finset V) : 2 * eIn G S ≤ #S * (#S - 1) := by
  rw [two_mul_eIn]
  calc ∑ v ∈ S, #(nbIn G S v) ≤ ∑ _v ∈ S, (#S - 1) := sum_le_sum fun v hv => by
        rw [← card_erase_of_mem hv]
        apply card_le_card
        intro u hu
        simp only [nbIn, mem_filter, mem_neighborFinset] at hu
        exact mem_erase.2 ⟨hu.1.ne', hu.2⟩
    _ = #S * (#S - 1) := by rw [sum_const, smul_eq_mul]

theorem deg_le_nbIn_add (W : Finset V) (v : V) : G.degree v ≤ #(nbIn G W v) + #Wᶜ := by
  rw [← card_neighborFinset_eq_degree, ← card_filter_add_card_filter_not (p := (· ∈ W))]
  have : #((G.neighborFinset v).filter (· ∉ W)) ≤ #Wᶜ :=
    card_le_card fun u hu => mem_compl.2 (mem_filter.1 hu).2
  rw [nbIn]
  omega

theorem mul_sub_two {D n : ℕ} (h : 2 ≤ n) : D * (n - 2) + 2 * D = D * n := by
  rw [mul_comm 2 D, ← Nat.mul_add, Nat.sub_add_cancel h]

/-- **Absence of overfull sets from the vertex-deleted bound** (via Lemma 2.1). -/
theorem noOverfull_of_erase {D δ' : ℕ} (hev : Even (Fintype.card V))
    (hmax : ∀ v, G.degree v ≤ D) (hmin : ∀ v, δ' ≤ G.degree v)
    (hD : D + 1 ≤ Fintype.card V) (hδ : Fintype.card V + 2 ≤ 2 * δ')
    (h : ∀ w, dsum G ≤ 2 * G.degree w + D * (Fintype.card V - 2)) : NoOverfull G D := by
  intro S hS
  by_contra hlt
  push_neg at hlt
  have hle := two_mul_eIn_le_card G S
  have hS3 : 3 ≤ #S := by
    rcases hS with ⟨r, hr⟩
    rcases r with _ | r
    · simp at hr; rw [hr] at hle hlt; simp at hle hlt; omega
    · omega
  have hfull : IsFull G D S := ⟨hS3, hS, hlt.le⟩
  have hcard := card_add_one_of_full G hev hmax hmin hD hδ hfull
  obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
    by_contra hall
    push_neg at hall
    have : #S = Fintype.card V := by rw [← card_univ]; congr 1; exact eq_univ_of_forall hall
    omega
  have hSeq : S = univ.erase w := by
    apply eq_of_subset_of_card_le
    · intro v hv; exact mem_erase.2 ⟨fun h => hw (h ▸ hv), mem_univ v⟩
    · rw [card_erase_of_mem (mem_univ w), card_univ]; omega
  subst hSeq
  have h1 := two_mul_eIn_erase G w
  have h2 := h w
  rw [card_erase_of_mem (mem_univ w), card_univ] at hlt
  have : Fintype.card V - 1 - 1 = Fintype.card V - 2 := by omega
  rw [this] at hlt
  omega

/-- **Three vertices of minimum degree** give the vertex-deleted bound. -/
theorem erase_bound_of_three {D t : ℕ} (hmax : ∀ v, G.degree v ≤ D) {a b c : V} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : G.degree a ≤ t) (hb : G.degree b ≤ t)
    (hc : G.degree c ≤ t) (ht : ∀ v, t ≤ G.degree v) (hn : 2 ≤ Fintype.card V) (w : V) :
    dsum G ≤ 2 * G.degree w + D * (Fintype.card V - 2) := by
  have h1 := dfc_add_dsum G hmax
  have h2 := dfc_ge_three G (D := D) hab hac hbc
  have h3 := mul_sub_two (D := D) hn
  have := ht w
  have := ht a
  have := hmax a
  omega

/-! ### Removing a matching -/

variable {G}

theorem dsum_sdiff {M : SimpleGraph V} {W : Finset V} (hM : IsMatchingOn G M W) :
    dsum (G \ M) + #W = dsum G := by
  have hdeg : ∑ v, M.degree v = #W := by
    rw [← sum_filter_add_sum_filter_not univ (· ∈ W)]
    rw [sum_congr rfl (g := fun _ => 1) fun v hv => hM.2.1 v (mem_filter.1 hv).2,
      sum_congr rfl (g := fun _ => 0) fun v hv => hM.2.2 v (mem_filter.1 hv).2]
    simp [filter_mem_eq_inter]
  rw [dsum, dsum, ← hdeg, ← sum_add_distrib]
  exact sum_congr rfl fun v _ => degree_sdiff_add G hM.1 v

theorem deg_sdiff_mem {M : SimpleGraph V} {W : Finset V} (hM : IsMatchingOn G M W) {v : V}
    (hv : v ∈ W) : (G \ M).degree v + 1 = G.degree v := by
  have := degree_sdiff_add G hM.1 v
  rw [hM.2.1 v hv] at this
  exact this

theorem deg_sdiff_not_mem {M : SimpleGraph V} {W : Finset V} (hM : IsMatchingOn G M W) {v : V}
    (hv : v ∉ W) : (G \ M).degree v = G.degree v := by
  have := degree_sdiff_add G hM.1 v
  rw [hM.2.2 v hv] at this
  exact this

theorem IsMatchingOn.degree_le_one {M : SimpleGraph V} {W : Finset V} (hM : IsMatchingOn G M W)
    (v : V) : M.degree v ≤ 1 := by
  by_cases hv : v ∈ W
  · rw [hM.2.1 v hv]
  · rw [hM.2.2 v hv]; exact zero_le_one

end Plantholt
