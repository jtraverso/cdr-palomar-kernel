/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Kite0D

/-!
# The three-centre count (Chen–Cao, inequality (1))

`exists_good_common₃`: for three distinct vertices `p₁, p₂, q` different from `a`, if
`2n + 3|nonA| + 2 ≤ d(p₁) + d(p₂) + d(q)`, some `u ∉ {a, p₁, p₂, q}` is adjacent to all three, with
all three edges coloured in `A`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Three-centre count.** -/
theorem exists_good_common₃ {c : PEC G (Fin G.maxDegree)} {a b : V} (hcm : IsColMinus c a b)
    {p₁ p₂ q : V} (ha1 : p₁ ≠ a) (ha2 : p₂ ≠ a) (ha3 : q ≠ a)
    (hcnt : 2 * Fintype.card V + 3 * #(nonA c a b) + 2 ≤
      G.degree p₁ + G.degree p₂ + G.degree q) :
    ∃ u, u ≠ a ∧ u ≠ p₁ ∧ u ≠ p₂ ∧ u ≠ q ∧
      Good c a b p₁ u ∧ Good c a b p₂ u ∧ Good c a b q u := by
  classical
  set N₁ := G.neighborFinset p₁
  set N₂ := G.neighborFinset p₂
  set N₃ := G.neighborFinset q
  have i12 := card_inter_ge N₁ N₂
  have i123 := card_inter_ge (N₁ ∩ N₂) N₃
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at i12
  rw [card_neighborFinset_eq_degree] at i123
  set B := badNbrs c a b p₁ ∪ badNbrs c a b p₂ ∪ badNbrs c a b q with hB
  have hBc : #B ≤ 3 * #(nonA c a b) := by
    have e1 := card_badNbrs_le (c := c) (a := a) (b := b) p₁
    have e2 := card_badNbrs_le (c := c) (a := a) (b := b) p₂
    have e3 := card_badNbrs_le (c := c) (a := a) (b := b) q
    have f1 := card_union_le (badNbrs c a b p₁ ∪ badNbrs c a b p₂) (badNbrs c a b q)
    have f2 := card_union_le (badNbrs c a b p₁) (badNbrs c a b p₂)
    rw [hB]
    omega
  set X := N₁ ∩ N₂ ∩ N₃ with hX
  set Gd := (X.erase a) \ B with hGd
  have hcov : X ⊆ Gd ∪ B ∪ {a} := by
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
  simp only [hGd, hX, hB, mem_sdiff, mem_erase, mem_inter, mem_union, not_or, N₁, N₂, N₃,
    mem_neighborFinset] at hu
  obtain ⟨⟨hua, ⟨hp₁u, hp₂u⟩, hqu⟩, ⟨hb1, hb2⟩, hb3⟩ := hu
  have hgood : ∀ {x}, x ≠ a → G.Adj x u → u ∉ badNbrs c a b x → Good c a b x u := by
    intro x hxa hxu hbad
    by_contra hn
    exact hbad (not_good_mem_bad hcm hxu (fun he => by
      rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hxa rfl
      · exact hua rfl) hn)
  exact ⟨u, hua, hp₁u.ne.symm, hp₂u.ne.symm, hqu.ne.symm, hgood ha1 hp₁u hb1, hgood ha2 hp₂u hb2,
    hgood ha3 hqu hb3⟩

end Overfull
