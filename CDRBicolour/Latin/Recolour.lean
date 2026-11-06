/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Latin.Ryser
public import LeanPool.Vizing.Corollaries

/-!
# Equalized colouring of a regular bipartite relation (de Werra's step in CDR Lemma 2.3)

Let `E ⊆ Bs × Bs` be `x`-regular (every row and every column of `Bs` meets exactly `x` cells),
`|Bs| = b`, `x ≤ b`.  There is a colouring `κ` of the cells by `b` colours, injective along rows and
columns, using every colour exactly `x` times (counted by rows).

* `x < b`: an equitable proper edge colouring with `b ≥ Δ + 1` colours (Lean Pool, Vizing +
  balancing) of the bipartite graph of `E`; equal total `b·x` forces all classes to have size `x`.
* `x = b`: `E` is all of `Bs × Bs`; colour `(r, g)` by `r + g` in `ℤ/b`.
-/

@[expose] public section

namespace CDRBicolour.Latin

open Finset LeanPool.Vizing LeanPool.Vizing.ColourClasses LeanPool.Vizing.EquitableDefinitions

/-- Equitable sizes with exact total are all equal. -/
theorem eq_of_equitable_sum {ι : Type*} [Fintype ι] (s : ι → ℕ) (heq : ∀ i j, s i ≤ s j + 1)
    (x : ℕ) (hsum : ∑ i, s i = Fintype.card ι * x) : ∀ i, s i = x := by
  intro i
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : ∀ j, s j ≤ x := fun j => by have := heq j i; omega
    have : ∑ j, s j < ∑ _j : ι, x := sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ _, hlt⟩
    rw [sum_const, card_univ, smul_eq_mul] at this; omega
  · have hge : ∀ j, x ≤ s j := fun j => by have := heq i j; omega
    have : ∑ _j : ι, x < ∑ j, s j := sum_lt_sum (fun j _ => hge j) ⟨i, mem_univ _, hgt⟩
    rw [sum_const, card_univ, smul_eq_mul] at this; omega

variable {ρ γ : Type*} [Fintype ρ] [DecidableEq ρ] [DecidableEq γ]

/-- **Equalized colouring.** -/
theorem exists_equalized (Bs : Finset ρ) (E : ρ → ρ → Prop) [DecidableRel E]
    (hE : ∀ r g, E r g → r ∈ Bs ∧ g ∈ Bs) (x : ℕ)
    (hrow : ∀ r ∈ Bs, (Bs.filter fun g => E r g).card = x)
    (hcol : ∀ g ∈ Bs, (Bs.filter fun r => E r g).card = x) (hxb : x ≤ Bs.card)
    (T : Finset γ) (hT : T.card = Bs.card) (dflt : ρ → γ) :
    ∃ κ : ρ → ρ → γ, (∀ r g, E r g → κ r g ∈ T) ∧
      (∀ r g g', E r g → E r g' → κ r g = κ r g' → g = g') ∧
      (∀ g r r', E r g → E r' g → κ r g = κ r' g → r = r') ∧
      ∀ τ ∈ T, (Bs.filter fun r => ∃ g, E r g ∧ κ r g = τ).card = x := by
  classical
  set b := Bs.card with hb
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · -- no rows at all
    have hBs : Bs = ∅ := card_eq_zero.1 hb0
    have hT0 : T = ∅ := card_eq_zero.1 (hT.trans hb0)
    refine ⟨fun r _ => dflt r, fun r g h => absurd (hE r g h).1 (by rw [hBs]; simp),
      fun r g g' h => absurd (hE r g h).1 (by rw [hBs]; simp),
      fun g r r' h => absurd (hE r g h).1 (by rw [hBs]; simp),
      fun τ hτ => absurd hτ (by rw [hT0]; simp)⟩
  let eT : Fin b ≃ T := (T.equivFinOfCardEq hT).symm
  rcases lt_or_eq_of_le hxb with hlt | heqb
  · -- `x < b`: equitable colouring of the bipartite graph
    let H : SimpleGraph (ρ ⊕ ρ) := SimpleGraph.fromRel fun u v =>
      ∃ r g, u = .inl r ∧ v = .inr g ∧ E r g
    have hadj : ∀ r g, H.Adj (.inl r) (.inr g) ↔ E r g := by
      intro r g
      simp only [H, SimpleGraph.fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      constructor
      · rintro (⟨r', g', h1, h2, h3⟩ | ⟨r', g', h1, h2, h3⟩)
        · cases h1; cases h2; exact h3
        · cases h1
      · intro h; exact Or.inl ⟨r, g, rfl, rfl, h⟩
    have hll : ∀ r r', ¬ H.Adj (.inl r) (.inl r') := by
      intro r r'
      simp only [H, SimpleGraph.fromRel_adj]
      rintro ⟨-, ⟨_, _, h1, h2, _⟩ | ⟨_, _, h1, h2, _⟩⟩ <;> simp_all
    have hrr : ∀ g g', ¬ H.Adj (.inr g) (.inr g') := by
      intro g g'
      simp only [H, SimpleGraph.fromRel_adj]
      rintro ⟨-, ⟨_, _, h1, h2, _⟩ | ⟨_, _, h1, h2, _⟩⟩ <;> simp_all
    haveI : DecidableRel H.Adj := Classical.decRel _
    have hdeg : ∀ v, H.degree v ≤ x := by
      intro v
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      cases v with
      | inl r =>
        by_cases hr : r ∈ Bs
        · rw [← hrow r hr]
          refine card_le_card_of_injOn (fun w => Sum.elim (fun _ => r) id w) ?_ ?_
          · intro w hw
            rw [mem_coe, SimpleGraph.mem_neighborFinset] at hw
            cases w with
            | inl r' => exact absurd hw (hll r r')
            | inr g =>
              rw [hadj] at hw
              rw [mem_coe, mem_filter]; exact ⟨(hE r g hw).2, hw⟩
          · intro w hw w' hw' h
            rw [mem_coe, SimpleGraph.mem_neighborFinset] at hw hw'
            cases w with
            | inl r' => exact absurd hw (hll r r')
            | inr g => cases w' with
              | inl r' => exact absurd hw' (hll r r')
              | inr g' => simp only [Sum.elim_inr, id] at h; rw [h]
        · have : H.neighborFinset (.inl r) = ∅ := by
            ext w
            simp only [SimpleGraph.mem_neighborFinset, notMem_empty, iff_false]
            cases w with
            | inl r' => exact hll r r'
            | inr g => rw [hadj]; exact fun h => hr (hE r g h).1
          rw [this, card_empty]; omega
      | inr g =>
        by_cases hg : g ∈ Bs
        · rw [← hcol g hg]
          refine card_le_card_of_injOn (fun w => Sum.elim id (fun _ => g) w) ?_ ?_
          · intro w hw
            rw [mem_coe, SimpleGraph.mem_neighborFinset] at hw
            cases w with
            | inr g' => exact absurd hw (hrr g g')
            | inl r =>
              rw [H.adj_comm, hadj] at hw
              rw [mem_coe, mem_filter]; exact ⟨(hE r g hw).1, hw⟩
          · intro w hw w' hw' h
            rw [mem_coe, SimpleGraph.mem_neighborFinset] at hw hw'
            cases w with
            | inr g' => exact absurd hw (hrr g g')
            | inl r => cases w' with
              | inr g' => exact absurd hw' (hrr g g')
              | inl r' => simp only [Sum.elim_inl, id] at h; rw [h]
        · have : H.neighborFinset (.inr g) = ∅ := by
            ext w
            simp only [SimpleGraph.mem_neighborFinset, notMem_empty, iff_false]
            cases w with
            | inr g' => exact hrr g g'
            | inl r => rw [H.adj_comm, hadj]; exact fun h => hg (hE r g h).2
          rw [this, card_empty]; omega
    have hΔ : H.maxDegree + 1 ≤ b := by
      have := H.maxDegree_le_of_forall_degree_le x hdeg; omega
    obtain ⟨colour, hprop, hequit, -⟩ := exists_equitable_edge_colouring H b hΔ
    -- cells of `E` ↔ edges of `H`
    let cells : Finset (ρ × ρ) := (Bs ×ˢ Bs).filter fun p => E p.1 p.2
    let toEdge : ρ × ρ → Sym2 (ρ ⊕ ρ) := fun p => s(.inl p.1, .inr p.2)
    have htoEdge_inj : Set.InjOn toEdge cells := by
      intro p _ q _ h
      simp only [toEdge] at h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
      · exact absurd h1 Sum.inl_ne_inr
    have hedges : H.edgeFinset = cells.image toEdge := by
      ext e
      constructor
      · intro he
        rw [SimpleGraph.mem_edgeFinset] at he
        revert he
        refine Sym2.ind (fun u v huv => ?_) e
        rw [SimpleGraph.mem_edgeSet] at huv
        cases u with
        | inl r => cases v with
          | inl r' => exact absurd huv (hll r r')
          | inr g =>
            rw [hadj] at huv
            exact mem_image.2 ⟨(r, g), mem_filter.2 ⟨mem_product.2 (hE r g huv), huv⟩, rfl⟩
        | inr g => cases v with
          | inr g' => exact absurd huv (hrr g g')
          | inl r =>
            rw [H.adj_comm, hadj] at huv
            exact mem_image.2 ⟨(r, g), mem_filter.2 ⟨mem_product.2 (hE r g huv), huv⟩,
              Sym2.eq_swap⟩
      · intro he
        obtain ⟨p, hp, rfl⟩ := mem_image.1 he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hadj]
        exact (mem_filter.1 hp).2
    have hcells : cells.card = b * x := by
      rw [card_filter, sum_product]
      rw [sum_congr rfl fun r hr => (card_filter (fun g => E r g) Bs).symm.trans (hrow r hr),
        sum_const, smul_eq_mul]
    -- each class has exactly `x` edges
    have hclass : ∀ τ, (colourClass H.edgeFinset colour τ).card = x := by
      refine eq_of_equitable_sum (fun τ => (colourClass H.edgeFinset colour τ).card)
        (fun i j => hequit i j) x ?_
      rw [sum_card_colourClass_univ, Fintype.card_fin, hedges,
        card_image_of_injOn htoEdge_inj, hcells]
    let κ : ρ → ρ → γ := fun r g => if E r g then (eT (colour (toEdge (r, g)))).1 else dflt r
    have hκ : ∀ r g, E r g → κ r g = (eT (colour (toEdge (r, g)))).1 := fun r g h => if_pos h
    have hκinj : ∀ r g r' g', E r g → E r' g' → κ r g = κ r' g' →
        colour (toEdge (r, g)) = colour (toEdge (r', g')) := by
      intro r g r' g' h h' hk
      rw [hκ r g h, hκ r' g' h'] at hk
      exact eT.injective (Subtype.ext hk)
    have hedge : ∀ r g, E r g → toEdge (r, g) ∈ H.edgeFinset := by
      intro r g h; rw [hedges]
      exact mem_image.2 ⟨(r, g), mem_filter.2 ⟨mem_product.2 (hE r g h), h⟩, rfl⟩
    refine ⟨κ, fun r g h => by rw [hκ r g h]; exact (eT _).2, ?_, ?_, ?_⟩
    · intro r g g' h h' hk
      by_contra hne
      have hd := hprop _ (hedge r g h) _ (hedge r g' h') (fun he => hne (by
        have := htoEdge_inj (mem_filter.2 ⟨mem_product.2 (hE r g h), h⟩)
          (mem_filter.2 ⟨mem_product.2 (hE r g' h'), h'⟩) he
        exact (Prod.ext_iff.1 this).2)) (hκinj r g r g' h h' hk)
      exact Finset.disjoint_left.1 hd (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))
        (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))
    · intro g r r' h h' hk
      by_contra hne
      have hd := hprop _ (hedge r g h) _ (hedge r' g h') (fun he => hne (by
        have := htoEdge_inj (mem_filter.2 ⟨mem_product.2 (hE r g h), h⟩)
          (mem_filter.2 ⟨mem_product.2 (hE r' g h'), h'⟩) he
        exact (Prod.ext_iff.1 this).1)) (hκinj r g r' g h h' hk)
      exact Finset.disjoint_left.1 hd (Sym2.mem_toFinset.2 (Sym2.mem_mk_right _ _))
        (Sym2.mem_toFinset.2 (Sym2.mem_mk_right _ _))
    · intro τ hτ
      set i := eT.symm ⟨τ, hτ⟩
      rw [← hclass i]
      -- rows with a cell of colour `τ` ↔ edges of colour `i`
      have hrowsub : (Bs.filter fun r => ∃ g, E r g ∧ κ r g = τ) =
          ((cells.filter fun p => colour (toEdge p) = i).image Prod.fst) := by
        ext r
        rw [mem_filter, mem_image]
        constructor
        · rintro ⟨hr, g, hg, hk⟩
          refine ⟨(r, g), mem_filter.2 ⟨mem_filter.2 ⟨mem_product.2 (hE r g hg), hg⟩, ?_⟩, rfl⟩
          rw [hκ r g hg] at hk
          have : eT (colour (toEdge (r, g))) = ⟨τ, hτ⟩ := Subtype.ext hk
          apply eT.injective
          rw [this]
          simp [i]
        · rintro ⟨⟨r', g⟩, hp, rfl⟩
          obtain ⟨hp1, hc⟩ := mem_filter.1 hp
          obtain ⟨hp2, hg⟩ := mem_filter.1 hp1
          refine ⟨(mem_product.1 hp2).1, g, hg, ?_⟩
          rw [hκ r' g hg]
          rw [show colour (toEdge (r', g)) = i from hc]
          simp [i]
      rw [hrowsub, card_image_of_injOn]
      · rw [colourClass, hedges, filter_image, card_image_of_injOn]
        exact htoEdge_inj.mono fun p hp => (mem_filter.1 (mem_coe.1 hp)).1
      · intro p hp q hq h
        rw [mem_coe, mem_filter] at hp hq
        have hp2 := (mem_filter.1 hp.1).2
        have hq2 := (mem_filter.1 hq.1).2
        obtain ⟨r, g⟩ := p
        obtain ⟨r', g'⟩ := q
        simp only at h hp2 hq2
        subst h
        by_contra hne
        have hgg : g ≠ g' := fun h' => hne (by rw [h'])
        have hd := hprop _ (hedge r g hp2) _ (hedge r g' hq2) (fun he => hgg (by
          have := htoEdge_inj (mem_filter.2 ⟨mem_product.2 (hE r g hp2), hp2⟩)
            (mem_filter.2 ⟨mem_product.2 (hE r g' hq2), hq2⟩) he
          exact (Prod.ext_iff.1 this).2)) (hp.2.trans hq.2.symm)
        exact Finset.disjoint_left.1 hd (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))
          (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))
  · -- `x = b`: every cell of `Bs × Bs`; cyclic colouring
    have hfull : ∀ r ∈ Bs, ∀ g ∈ Bs, E r g := by
      intro r hr g hg
      have h1 := hrow r hr
      rw [heqb] at h1
      have : Bs.filter (fun g => E r g) = Bs :=
        eq_of_subset_of_card_le (filter_subset _ _) (by rw [h1])
      rw [← this] at hg; exact (mem_filter.1 hg).2
    let eB : Bs ≃ Fin b := Bs.equivFin
    let κ : ρ → ρ → γ := fun r g =>
      if h : r ∈ Bs ∧ g ∈ Bs then (eT (eB ⟨r, h.1⟩ + eB ⟨g, h.2⟩)).1 else dflt r
    have hκ : ∀ r g (h : r ∈ Bs ∧ g ∈ Bs), κ r g = (eT (eB ⟨r, h.1⟩ + eB ⟨g, h.2⟩)).1 :=
      fun r g h => dif_pos h
    refine ⟨κ, fun r g h => by rw [hκ r g (hE r g h)]; exact (eT _).2, ?_, ?_, ?_⟩
    · intro r g g' h h' hk
      rw [hκ r g (hE r g h), hκ r g' (hE r g' h')] at hk
      have := add_left_cancel (eT.injective (Subtype.ext hk))
      exact congrArg Subtype.val (eB.injective this)
    · intro g r r' h h' hk
      rw [hκ r g (hE r g h), hκ r' g (hE r' g h')] at hk
      have := add_right_cancel (eT.injective (Subtype.ext hk))
      exact congrArg Subtype.val (eB.injective this)
    · intro τ hτ
      rw [heqb]
      congr 1
      refine filter_true_of_mem fun r hr => ?_
      set k := eT.symm ⟨τ, hτ⟩ - eB ⟨r, hr⟩
      set g := (eB.symm k).1
      have hg : g ∈ Bs := (eB.symm k).2
      refine ⟨g, hfull r hr g hg, ?_⟩
      rw [hκ r g ⟨hr, hg⟩]
      have hgk : eB ⟨g, hg⟩ = k := by
        show eB (eB.symm k) = k
        exact Equiv.apply_symm_apply _ _
      haveI : NeZero b := ⟨hbpos.ne'⟩
      rw [hgk, show eB ⟨r, hr⟩ + k = eT.symm ⟨τ, hτ⟩ from add_sub_cancel _ _,
        Equiv.apply_symm_apply]

end CDRBicolour.Latin
