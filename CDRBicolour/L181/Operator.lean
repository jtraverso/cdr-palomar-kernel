/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L181.FlipSet

/-!
# L181: the port operator

`Good G W m χ M` collects the invariants of a row system during L181: `χ` is a proper colouring
avoiding the frozen colours `W`, every row carries a partial pairing of its missing set, pairs of
different rows are disjoint, and the multiplicities outside `W` take the two values `m`, `m+2`.

`port_move` (LOCAL OPERATOR PROOF of L181): if the current row `j₀` misses `p` with `p`
unpaired, and `x` is present at `j₀`, then after a legal flip the row misses `x` instead of
`p`, all invariants and the number of high labels are kept, the old pairs of `j₀` are untouched,
every pair avoiding `p` and `x` keeps its status, and at most one new pair `x r` appears into a
set on which `x` was clean.
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]

/-- The invariants of L181. -/
structure Good (G : SimpleGraph Rw) [DecidableRel G.Adj] (W : Finset Cl) (m : ℕ)
    (χ : Sym2 Rw → Cl) (M : Rw → Finset (Sym2 Cl)) : Prop where
  proper : ProperOn G.edgeFinset χ
  avoid : ∀ e ∈ G.edgeFinset, χ e ∉ W
  pairs : ∀ j, IsPartialPairing (M j) (miss G χ j)
  disj : PairDisjoint M
  two : ∀ v, v ∉ W → mult G χ v = m ∨ mult G χ v = m + 2

variable {G : SimpleGraph Rw} [DecidableRel G.Adj] {W : Finset Cl} {m : ℕ}

theorem Good.mem_miss_of_mem {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hg : Good G W m χ M) {w : Cl} (hw : w ∈ W) (j : Rw) : w ∈ miss G χ j := by
  rw [mem_miss]
  intro e he hc
  exact hg.avoid e (SimpleGraph.incidenceFinset_subset _ _ he) (hc ▸ hw)

/-- **The port operator.** -/
theorem port_move {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)} (hg : Good G W m χ M)
    {j₀ : Rw} {p x : Cl} (hp : p ∈ miss G χ j₀) (hpc : p ∉ cover (M j₀))
    (hWc : W ⊆ cover (M j₀)) (hx : x ∉ miss G χ j₀) :
    ∃ (χ' : Sym2 Rw → Cl) (M' : Rw → Finset (Sym2 Cl)),
      Good G W m χ' M' ∧
      (univ.filter fun v => v ∉ W ∧ mult G χ' v = m + 2).card =
        (univ.filter fun v => v ∉ W ∧ mult G χ v = m + 2).card ∧
      (∀ j, IsPerfectPairing (M j) (miss G χ j) → IsPerfectPairing (M' j) (miss G χ' j)) ∧
      (∀ j, W ⊆ cover (M j) → W ⊆ cover (M' j)) ∧
      (∀ j, (cover (M' j)).card = (cover (M j)).card) ∧
      (∀ j, (miss G χ' j).card = (miss G χ j).card) ∧
      M' j₀ = M j₀ ∧
      miss G χ' j₀ = insert x ((miss G χ j₀).erase p) ∧
      (∀ e, p ∉ e → x ∉ e → ((∃ j, e ∈ M' j) ↔ ∃ j, e ∈ M j)) ∧
      (∀ I : Finset Cl, (∀ r ∈ I, ∀ j, s(x, r) ∉ M j) →
        (I.filter fun r => r ≠ p ∧ ∃ j, s(x, r) ∈ M' j).card ≤ 1) := by
  classical
  have hpx : p ≠ x := fun h => hx (h ▸ hp)
  have hpW : p ∉ W := fun h => hpc (hWc h)
  have hxW : x ∉ W := fun h => hx (hg.mem_miss_of_mem h j₀)
  obtain ⟨Z, hK, hL, hj₀Z, hcnt, hroot⟩ :=
    exists_flip_set (x := x) hg.proper hg.pairs hg.disj hp hpc
  have hmp := mult_flip hK p
  have hmx := mult_flip hK x
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hmp hmx
  have hgood : Good G W m (flipCol p x Z χ) (flipM p x Z M) := by
    refine ⟨properOn_flip hg.proper hK, avoid_flip hpW hxW hg.avoid,
      fun j => isPartialPairing_flip hK (hg.pairs j),
      pairDisjoint_flip hpx (fun j e he => (hg.pairs j).1 e he) hg.disj hL, ?_⟩
    intro v hv
    by_cases hvp : v = p
    · subst hvp
      rcases hcnt with h | ⟨h, hlt⟩
      · rw [show mult G (flipCol v x Z χ) v = mult G χ v by omega]; exact hg.two v hv
      · rcases hg.two v hv with h1 | h1 <;> rcases hg.two x hxW with h2 | h2 <;> omega
    · by_cases hvx : v = x
      · subst hvx
        rcases hcnt with h | ⟨h, hlt⟩
        · rw [show mult G (flipCol p v Z χ) v = mult G χ v by omega]; exact hg.two v hv
        · rcases hg.two p hpW with h1 | h1 <;> rcases hg.two v hxW with h2 | h2 <;> omega
      · rw [mult_flip_of_ne hK hvp hvx]; exact hg.two v hv
  refine ⟨flipCol p x Z χ, flipM p x Z M, hgood, ?_, fun j h => isPerfectPairing_flip hK h,
    ?_, ?_, ?_, ?_, ?_, fun e hpe hxe => ?_, ?_⟩
  · -- the number of high labels
    rcases hcnt with h | ⟨h, hlt⟩
    · congr 1; ext v
      simp only [mem_filter, mem_univ, true_and]
      by_cases hvp : v = p
      · subst hvp; rw [show mult G (flipCol v x Z χ) v = mult G χ v by omega]
      · by_cases hvx : v = x
        · subst hvx; rw [show mult G (flipCol p v Z χ) v = mult G χ v by omega]
        · rw [mult_flip_of_ne hK hvp hvx]
    · have hp2 : mult G χ p = m + 2 := by
        rcases hg.two p hpW with h1 | h1 <;> rcases hg.two x hxW with h2 | h2 <;> omega
      have hx0 : mult G χ x = m := by
        rcases hg.two p hpW with h1 | h1 <;> rcases hg.two x hxW with h2 | h2 <;> omega
      have hset : (univ.filter fun v => v ∉ W ∧ mult G (flipCol p x Z χ) v = m + 2) =
          insert x ((univ.filter fun v => v ∉ W ∧ mult G χ v = m + 2).erase p) := by
        ext v
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_erase]
        by_cases hvp : v = p
        · subst hvp; constructor
          · rintro ⟨-, h'⟩; omega
          · rintro (h' | ⟨h', -⟩)
            · exact absurd h' hpx
            · exact absurd rfl h'
        · by_cases hvx : v = x
          · subst hvx
            exact ⟨fun _ => Or.inl rfl, fun _ => ⟨hxW, by omega⟩⟩
          · rw [mult_flip_of_ne hK hvp hvx]
            constructor
            · intro h'; exact Or.inr ⟨hvp, h'⟩
            · rintro (h' | ⟨-, h'⟩)
              · exact absurd h' hvx
              · exact h'
      rw [hset, card_insert_of_notMem, card_erase_of_mem]
      · have : 0 < (univ.filter fun v => v ∉ W ∧ mult G χ v = m + 2).card :=
          card_pos.2 ⟨p, by simp [hpW, hp2]⟩
        omega
      · simp [hpW, hp2]
      · simp [hx0]
  · -- `W` stays covered
    intro j hW w hw
    by_cases hj : j ∈ Z
    · rw [flipM_of_mem hj, cover_image_swap, mem_image_swap,
        Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hpW hw) (by rintro rfl; exact hxW hw)]
      exact hW hw
    · rw [flipM_of_not_mem hj]; exact hW hw
  · -- sizes of the covered sets
    intro j
    by_cases hj : j ∈ Z
    · rw [flipM_of_mem hj, cover_image_swap, card_image_of_injective _ (Equiv.injective _)]
    · rw [flipM_of_not_mem hj]
  · -- sizes of the missing sets
    intro j
    rw [miss_flip hK]
    split_ifs
    · exact card_image_of_injective _ (Equiv.injective _)
    · rfl
  · -- the old pairs of `j₀` are fixed
    rw [flipM_of_mem hj₀Z]
    conv_rhs => rw [← image_id (s := M j₀)]
    refine image_congr fun e he => ?_
    refine map_swap_of_not_mem p x ?_ ?_
    · intro hpe; exact hpc (mem_cover.2 ⟨e, he, hpe⟩)
    · intro hxe; exact hx ((hg.pairs j₀).2.1 e he x hxe)
  · -- the missing set of `j₀`
    rw [miss_flip hK, if_pos hj₀Z]
    ext v
    rw [mem_image_swap, mem_insert, mem_erase]
    by_cases hvp : v = p
    · subst hvp
      rw [Equiv.swap_apply_left]
      simp only [hx, false_iff, not_or, not_and, not_not]
      exact ⟨hpx, fun h => absurd rfl h⟩
    · by_cases hvx : v = x
      · subst hvx; rw [Equiv.swap_apply_right]; simp [hp]
      · rw [Equiv.swap_apply_of_ne_of_ne hvp hvx]; simp [hvp, hvx]
  · -- pairs avoiding `p`, `x`
    simp only [mem_flipM_of_not_mem hpe hxe]
  · -- root loss
    intro I hI
    refine le_trans (card_le_card ?_) hroot
    intro r hr
    rw [mem_filter] at hr
    obtain ⟨hrI, hrp, j, hj⟩ := hr
    have hrx : r ≠ x := by
      rintro rfl
      exact (hgood.pairs j).1 _ hj (Sym2.mk_isDiag_iff.2 rfl)
    rw [mem_flipM_x hrp hrx] at hj
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨hrp, hrx, hI r hrI, ?_⟩
    rcases hj with ⟨hjZ, hjp⟩ | ⟨-, hjx⟩
    · exact ⟨j, hjZ, hjp⟩
    · exact absurd hjx (hI r hrI j)

end CDRBicolour.L181
