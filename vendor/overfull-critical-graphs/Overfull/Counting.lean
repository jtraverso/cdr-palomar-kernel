/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Lemma25
public import Mathlib.Data.ZMod.Basic

/-!
# Counting tools for CCJS Theorem 1.2

* `exists_good_common₄`: a common neighbour of four vertices with all four edges coloured in `A`.
* `even_card_not_free`: for each colour, the vertices *not* missing it come in pairs.
* `sum_card_missing`: `Σ_v |φ̄(v)| + 2|E(G)| = nΔ + 2` for a colouring of `G − ab`.
* `exists_colour_missing_three`: if `n` is odd and `G` is not overfull, some colour is missing at
  three vertices (Parity Lemma).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : PEC G (Fin G.maxDegree)} {a b : V}

theorem card_inter_ge (s t : Finset V) : #s + #t ≤ #(s ∩ t) + Fintype.card V := by
  have := card_union_add_card_inter s t
  have := card_le_univ (s ∪ t)
  omega

/-- **Four-centre count.** For four distinct vertices `p₁, p₂, q₁, q₂` different from `a`, if
`3n + 4(|nonA| + 2) ≤ Σ d + 6`, some `u ∉ {a, p₁, p₂, q₁, q₂}` is adjacent to all four, with all
four edges coloured in `A`. -/
theorem exists_good_common₄ (hcm : IsColMinus c a b) {p₁ p₂ q₁ q₂ : V}
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ q₁) (h14 : p₁ ≠ q₂) (h23 : p₂ ≠ q₁) (h24 : p₂ ≠ q₂)
    (h34 : q₁ ≠ q₂) (ha1 : p₁ ≠ a) (ha2 : p₂ ≠ a) (ha3 : q₁ ≠ a) (ha4 : q₂ ≠ a)
    (hcnt : 3 * Fintype.card V + 4 * (#(nonA c a b) + 2) ≤
      G.degree p₁ + G.degree p₂ + G.degree q₁ + G.degree q₂ + 6) :
    ∃ u, u ≠ a ∧ u ≠ p₁ ∧ u ≠ p₂ ∧ u ≠ q₁ ∧ u ≠ q₂ ∧
      G.Adj p₁ u ∧ G.Adj p₂ u ∧ G.Adj q₁ u ∧ G.Adj q₂ u ∧
      Good c a b p₁ u ∧ Good c a b p₂ u ∧ Good c a b q₁ u ∧ Good c a b q₂ u := by
  classical
  set N₁ := G.neighborFinset p₁
  set N₂ := G.neighborFinset p₂
  set N₃ := G.neighborFinset q₁
  set N₄ := G.neighborFinset q₂
  set X := ((N₁ ∩ N₂).erase q₁).erase q₂ with hX
  set Y := ((N₃ ∩ N₄).erase p₁).erase p₂ with hY
  set U := (((univ.erase p₁).erase p₂).erase q₁).erase q₂ with hU
  have hcU : #U + 4 = Fintype.card V := by
    rw [hU, card_erase_of_mem (by simp [Ne.symm h14, Ne.symm h24, Ne.symm h34]),
      card_erase_of_mem (by simp [Ne.symm h13, Ne.symm h23]),
      card_erase_of_mem (by simp [Ne.symm h12]), card_erase_of_mem (mem_univ _), card_univ]
    have : 4 ≤ Fintype.card V := by
      have := card_le_univ ({p₁, p₂, q₁, q₂} : Finset V)
      rwa [card_insert_of_notMem (by simp [h12, h13, h14]),
        card_insert_of_notMem (by simp [h23, h24]), card_insert_of_notMem (by simp [h34]),
        card_singleton] at this
    omega
  have hXU : X ∪ Y ⊆ U := by
    intro w hw
    simp only [hX, hY, hU, mem_union, mem_erase, mem_inter, mem_univ, and_true, N₁, N₂, N₃, N₄,
      mem_neighborFinset] at hw ⊢
    rcases hw with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h1, h2, fun e => (e ▸ h4).ne rfl, fun e => (e ▸ h3).ne rfl⟩
    · exact ⟨fun e => (e ▸ h4).ne rfl, fun e => (e ▸ h3).ne rfl, h1, h2⟩
  have hX' : #(N₁ ∩ N₂) ≤ #X + 2 := by
    have : #X + (if q₂ ∈ (N₁ ∩ N₂).erase q₁ then 1 else 0) = #((N₁ ∩ N₂).erase q₁) :=
      card_erase_add _ q₂
    have := card_erase_add (N₁ ∩ N₂) q₁
    split_ifs at * <;> omega
  have hY' : #(N₃ ∩ N₄) ≤ #Y + 2 := by
    have : #Y + (if p₂ ∈ (N₃ ∩ N₄).erase p₁ then 1 else 0) = #((N₃ ∩ N₄).erase p₁) :=
      card_erase_add _ p₂
    have := card_erase_add (N₃ ∩ N₄) p₁
    split_ifs at * <;> omega
  have i12 := card_inter_ge N₁ N₂
  have i34 := card_inter_ge N₃ N₄
  have iXY := card_union_add_card_inter X Y
  have hXYU := card_le_card hXU
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at i12 i34
  -- remove `a` and the bad vertices
  set B := badNbrs c a b p₁ ∪ badNbrs c a b p₂ ∪ badNbrs c a b q₁ ∪ badNbrs c a b q₂ with hB
  have hBc : #B ≤ 4 * #(nonA c a b) := by
    have e1 := card_badNbrs_le (c := c) (a := a) (b := b) p₁
    have e2 := card_badNbrs_le (c := c) (a := a) (b := b) p₂
    have e3 := card_badNbrs_le (c := c) (a := a) (b := b) q₁
    have e4 := card_badNbrs_le (c := c) (a := a) (b := b) q₂
    have f1 := card_union_le (badNbrs c a b p₁ ∪ badNbrs c a b p₂ ∪ badNbrs c a b q₁)
      (badNbrs c a b q₂)
    have f2 := card_union_le (badNbrs c a b p₁ ∪ badNbrs c a b p₂) (badNbrs c a b q₁)
    have f3 := card_union_le (badNbrs c a b p₁) (badNbrs c a b p₂)
    rw [hB]
    omega
  set Gd := ((X ∩ Y).erase a) \ B with hGd
  have hcov : X ∩ Y ⊆ Gd ∪ B ∪ {a} := by
    intro w hw
    by_cases h1 : w = a
    · exact mem_union_right _ (mem_singleton.2 h1)
    by_cases h2 : w ∈ B
    · exact mem_union_left _ (mem_union_right _ h2)
    exact mem_union_left _ (mem_union_left _ (mem_sdiff.2 ⟨mem_erase.2 ⟨h1, hw⟩, h2⟩))
  have hc1 := card_le_card hcov
  have hc2 := card_union_le (Gd ∪ B) {a}
  have hc3 := card_union_le Gd B
  rw [card_singleton] at hc2
  have hpos : 0 < #Gd := by omega
  obtain ⟨u, hu⟩ := card_pos.1 hpos
  simp only [hGd, hX, hY, hB, mem_sdiff, mem_erase, mem_inter, mem_union, not_or, N₁, N₂, N₃, N₄,
    mem_neighborFinset] at hu
  obtain ⟨⟨hua, ⟨huq₂, huq₁, hp₁u, hp₂u⟩, hup₂, hup₁, hq₁u, hq₂u⟩, ⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩ := hu
  have hgood : ∀ {x}, x ≠ a → G.Adj x u → u ∉ badNbrs c a b x → Good c a b x u := by
    intro x hxa hxu hbad
    by_contra hn
    exact hbad (not_good_mem_bad hcm hxu (fun he => by
      rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hxa rfl
      · exact hua rfl) hn)
  exact ⟨u, hua, hup₁, hup₂, huq₁, huq₂, hp₁u, hp₂u, hq₁u, hq₂u, hgood ha1 hp₁u hb1,
    hgood ha2 hp₂u hb2, hgood ha3 hq₁u hb3, hgood ha4 hq₂u hb4⟩

/-! ### Parity and edge counting -/

section Parity

open Classical

/-- For each colour, the vertices on an edge of that colour come in pairs. -/
theorem even_card_not_free {k : ℕ} (c : PEC G (Fin k)) (θ : Fin k) :
    Even #(univ.filter fun v => ¬ c.IsFree v θ) := by
  classical
  set S := univ.filter fun v => ¬ c.IsFree v θ with hS
  have hex : ∀ v ∈ S, ∃ w, c.col v w = some θ := by
    intro v hv
    simp only [hS, mem_filter, mem_univ, true_and, IsFree, not_forall, not_not] at hv
    exact hv
  choose g hg using hex
  have hmem : ∀ v hv, g v hv ∈ S := by
    intro v hv
    simp only [hS, mem_filter, mem_univ, true_and, IsFree, not_forall, not_not]
    exact ⟨v, by rw [c.col_symm]; exact hg v hv⟩
  have key : ∑ v ∈ S, (1 : ZMod 2) = 0 := by
    refine sum_involution g (fun _ _ => rfl) (fun v hv _ he => ?_) hmem (fun v hv => ?_)
    · have := hg v hv
      rw [he, c.col_self] at this
      cases this
    · have h1 := hg (g v hv) (hmem v hv)
      have h2 : c.col (g v hv) v = some θ := by rw [c.col_symm]; exact hg v hv
      exact c.col_proper h1 h2
  rw [sum_const, nsmul_eq_mul, mul_one] at key
  exact (ZMod.natCast_eq_zero_iff_even).1 key

theorem card_missing_eq_filter {k : ℕ} (c : PEC G (Fin k)) (v : V) :
    #(missing c v) = #(univ.filter fun θ => c.IsFree v θ) := by
  congr 1

/-- `Σ_v |φ̄(v)| + 2|E(G)| = nΔ + 2` for a colouring of `G − ab`. -/
theorem IsColMinus.sum_card_missing (hcm : IsColMinus c a b) :
    ∑ v, #(missing c v) + 2 * #G.edgeFinset = Fintype.card V * G.maxDegree + 2 := by
  classical
  have h1 : ∑ v, (#(missing c v) + #(colNbrs c v)) = Fintype.card V * G.maxDegree := by
    rw [sum_congr rfl fun v _ => card_missing_add_colNbrs c v, sum_const, card_univ, smul_eq_mul]
  have h2 : ∑ v, (#(colNbrs c v) + (if v = a ∨ v = b then 1 else 0)) = 2 * #G.edgeFinset := by
    rw [sum_congr rfl fun v _ => hcm.card_colNbrs v, sum_degrees_eq_twice_card_edges]
  have h3 : ∑ v : V, (if v = a ∨ v = b then 1 else 0) = 2 := by
    rw [sum_boole]
    have : (univ.filter fun v => v = a ∨ v = b) = {a, b} := by
      ext v; simp
    rw [this, card_insert_of_notMem (by simp [hcm.adj.ne]), card_singleton]
    rfl
  rw [sum_add_distrib] at h1 h2
  omega

/-- Double counting the missing colours. -/
theorem sum_card_missing_eq {k : ℕ} (c : PEC G (Fin k)) :
    ∑ v, #(missing c v) = ∑ θ, #(univ.filter fun v => c.IsFree v θ) := by
  classical
  simp only [card_missing_eq_filter, card_filter]
  exact sum_comm

theorem card_free_add_not_free {k : ℕ} (c : PEC G (Fin k)) (θ : Fin k) :
    #(univ.filter fun v => c.IsFree v θ) + #(univ.filter fun v => ¬ c.IsFree v θ) =
      Fintype.card V := by
  rw [card_filter_add_card_filter_not, card_univ]

/-- **Parity Lemma, odd order.** If `n` is odd and `G` is not overfull, some colour is missing at
three vertices. -/
theorem exists_colour_missing_three (hcm : IsColMinus c a b) (hodd : Odd (Fintype.card V))
    (hnot : ¬ IsOverfull G) : ∃ θ, 3 ≤ #(univ.filter fun v => c.IsFree v θ) := by
  classical
  unfold IsOverfull at hnot
  push Not at hnot
  have hsum := hcm.sum_card_missing
  rw [sum_card_missing_eq] at hsum
  obtain ⟨m, hm⟩ := hodd
  have hdiv : Fintype.card V / 2 = m := by omega
  rw [hdiv] at hnot
  have hbig : ∃ θ, 2 ≤ #(univ.filter fun v => c.IsFree v θ) := by
    by_contra hn
    push Not at hn
    have : ∑ θ : Fin G.maxDegree, #(univ.filter fun v => c.IsFree v θ) ≤
        ∑ _θ : Fin G.maxDegree, 1 := sum_le_sum fun θ _ => by have := hn θ; omega
    rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    have e : Fintype.card V * G.maxDegree = 2 * (G.maxDegree * m) + G.maxDegree := by
      rw [hm, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm m]
    omega
  obtain ⟨θ, hθ⟩ := hbig
  refine ⟨θ, ?_⟩
  obtain ⟨r, hr⟩ := even_card_not_free c θ
  have := card_free_add_not_free c θ
  omega

/-- **Parity Lemma, even order.** If `n` is even, every colour is missing at an even number of
vertices. -/
theorem even_card_free_of_even {k : ℕ} (c : PEC G (Fin k)) (heven : Even (Fintype.card V))
    (θ : Fin k) : Even #(univ.filter fun v => c.IsFree v θ) := by
  obtain ⟨r, hr⟩ := even_card_not_free c θ
  obtain ⟨m, hm⟩ := heven
  have := card_free_add_not_free c θ
  exact ⟨m - r, by omega⟩

end Parity

end Overfull
