/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.RowCover

/-!
# L182: the prefix meets the hypotheses of L184

`prefixP d = (AAB ∪ ABB) ∪ (BBC ∪ BCC)` for valid stage data `d`.  `prefix_cover` gives the
four hypotheses of `L184.l184_assembly` with `μ = d.μ` and residual `F = resid d`.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.L184

variable {V : Type*} [Fintype V] [DecidableEq V] {col : V → Fin 3} (d : PrefixData col)

/-- The prefix: the two row systems (A rows, B colours) and (B rows, C colours). -/
def prefixP : Finset (Finset V) :=
  rsBlocks (GA d.μ) d.χA d.MA ∪ rsBlocks (GB d.MA) d.χB d.MB

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

/-- A block `{z} ∪ p` with `p` a proper pair of another class has 3 points and 2 classes. -/
theorem blk_card {cz cp : Fin 3} (hne : cz ≠ cp) (z : V) (hz : col z = cz)
    (p : Sym2 {v // col v = cp}) (hp : ¬ p.IsDiag) :
    (blk z p).card = 3 ∧ ((blk z p).image col).card = 2 := by
  have hnot : z ∉ p.toFinset.map (Function.Embedding.subtype _) := by
    simp only [mem_map, Sym2.mem_toFinset, Function.Embedding.subtype_apply, not_exists, not_and]
    intro q _ hq
    exact hne (hz ▸ hq ▸ q.2)
  have hc2 : (p.toFinset.map (Function.Embedding.subtype _)).card = 2 := by
    rw [card_map, Sym2.card_toFinset_of_not_isDiag p hp]
  refine ⟨by rw [blk, card_insert_of_notMem hnot, hc2], ?_⟩
  obtain ⟨q, hq⟩ : ∃ q, q ∈ p := ⟨p.out.1, Sym2.out_fst_mem p⟩
  have himg : (blk z p).image col = {cz, cp} := by
    ext t
    simp only [mem_image, mem_insert, mem_singleton, mem_blk]
    constructor
    · rintro ⟨v, hv | ⟨q', -, rfl⟩, rfl⟩
      · exact Or.inl (hv ▸ hz)
      · exact Or.inr q'.2
    · rintro (rfl | rfl)
      · exact ⟨z, Or.inl rfl, hz⟩
      · exact ⟨q.1, Or.inr ⟨q, hq, rfl⟩, q.2⟩
  rw [himg, card_pair hne]

variable {d}

theorem prefix_card (hv : d.Valid) {B : Finset V} (hB : B ∈ prefixP d) :
    B.card = 3 ∧ (B.image col).card = 2 := by
  rcases mem_union.1 hB with hB | hB
  · rcases (mem_rsBlocks _ _ _).1 hB with ⟨e, he, rfl⟩ | ⟨j, p, hp, rfl⟩
    · exact blk_card (by decide) _ (d.χA e).2 e (SimpleGraph.not_isDiag_of_mem_edgeFinset he)
    · exact blk_card (by decide) _ j.2 p ((hv.hMA j).1 p hp)
  · rcases (mem_rsBlocks _ _ _).1 hB with ⟨e, he, rfl⟩ | ⟨j, p, hp, rfl⟩
    · exact blk_card (by decide) _ (d.χB e).2 e (SimpleGraph.not_isDiag_of_mem_edgeFinset he)
    · exact blk_card (by decide) _ j.2 p ((hv.hMB j).1 p hp)

theorem GA_adj_iff (hv : d.Valid) {x y : AType col} :
    (GA d.μ).Adj x y ↔ x ≠ y ∧ y ≠ d.μ x := by
  simp only [GA, SimpleGraph.fromRel_adj, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact h2
    · intro h; apply h2; rw [h, hv.hμ]
  · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl h2⟩

theorem GB_adj_iff {x y : BType col} :
    (GB d.MA).Adj x y ↔ x ≠ y ∧ ∀ i, s(x, y) ∉ d.MA i := by
  simp only [GB, unusedGraph, SimpleGraph.fromRel_adj, ne_eq, Sym2.eq_swap (a := y)]
  tauto

theorem resid_adj_iff {x y : CType col} :
    (resid d.MB).Adj x y ↔ x ≠ y ∧ ∀ j, s(x, y) ∉ d.MB j := by
  simp only [resid, unusedGraph, SimpleGraph.fromRel_adj, ne_eq, Sym2.eq_swap (a := y)]
  tauto

/-- Pair-disjoint perfect pairings: a pair lies in at most one row's pairing. -/
theorem row_of_pair_unique {Cl Rw : Type*} {M : Rw → Finset (Sym2 Cl)} (hd : PairDisjoint M)
    {p : Sym2 Cl} {i i' : Rw} (hi : p ∈ M i) (hi' : p ∈ M i') : i = i' := by
  by_contra h
  exact Finset.disjoint_left.1 (hd i i' h) hi hi'

theorem reserved_symm (hv : d.Valid) {x y : V} (h : Reserved col d.μ (resid d.MB) x y) :
    Reserved col d.μ (resid d.MB) y x := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hx, hy⟩ | ⟨hx, hy, hadj⟩
  · exact Or.inr (Or.inl ⟨h2, h1⟩)
  · exact Or.inl ⟨h2, h1⟩
  · have hy0 : col y = 0 := by rw [hy]; exact (d.μ ⟨x, hx⟩).2
    refine Or.inr (Or.inr (Or.inl ⟨hy0, ?_⟩))
    have : (⟨y, hy0⟩ : AType col) = d.μ ⟨x, hx⟩ := Subtype.ext hy
    rw [this, hv.hμ]
  · exact Or.inr (Or.inr (Or.inr ⟨hy, hx, hadj.symm⟩))

/-- The core case analysis, for `col x ≤ col y`. -/
theorem prefix_pairs_le (hv : d.Valid) {x y : V} (hxy : x ≠ y) (hle : col x ≤ col y) :
    (Reserved col d.μ (resid d.MB) x y → ∀ B ∈ prefixP d, ¬ (x ∈ B ∧ y ∈ B)) ∧
      (¬ Reserved col d.μ (resid d.MB) x y → ∃! B, B ∈ prefixP d ∧ x ∈ B ∧ y ∈ B) := by
  have hA2 : ∀ {z : V} {B : Finset V}, col z = 0 → B ∈ rsBlocks (GB d.MA) d.χB d.MB → z ∉ B :=
    fun hz hB => not_mem_rsBlocks (by rw [hz]; decide) (by rw [hz]; decide) hB
  have hC1 : ∀ {z : V} {B : Finset V}, col z = 2 → B ∈ rsBlocks (GA d.μ) d.χA d.MA → z ∉ B :=
    fun hz hB => not_mem_rsBlocks (by rw [hz]; decide) (by rw [hz]; decide) hB
  rcases fin3_cases (col x) with hx | hx | hx <;> rcases fin3_cases (col y) with hy | hy | hy
  -- (0,0)
  · set a₁ : AType col := ⟨x, hx⟩
    set a₂ : AType col := ⟨y, hy⟩
    have ha : a₁ ≠ a₂ := fun h => hxy (congrArg Subtype.val h)
    have hres : Reserved col d.μ (resid d.MB) x y ↔ a₂ = d.μ a₁ := by
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨hx', hy'⟩ | ⟨h, -⟩)
        · rw [hy] at h; exact absurd h (by decide)
        · rw [hx] at h; exact absurd h (by decide)
        · exact Subtype.ext hy'
        · rw [hx] at h; exact absurd h (by decide)
      · intro h; exact Or.inr (Or.inr (Or.inl ⟨hx, congrArg Subtype.val h⟩))
    refine ⟨fun hr B hB ⟨hxB, hyB⟩ => ?_, fun hr => ?_⟩
    · rcases mem_union.1 hB with hB | hB
      · have := (rowrow_cover (by decide) ha hB hxB hyB).1
        exact ((GA_adj_iff hv).1 this).2 (hres.1 hr)
      · exact hA2 hx hB hxB
    · have hadj : (GA d.μ).Adj a₁ a₂ := (GA_adj_iff hv).2 ⟨ha, fun h => hr (hres.2 h)⟩
      refine ⟨blk (d.χA s(a₁, a₂)).1 s(a₁, a₂), ⟨mem_union.2 (Or.inl (edge_block_mem
        ((SimpleGraph.mem_edgeFinset).2 hadj))), ?_, ?_⟩, ?_⟩
      · exact (memX_edge (by decide) s(a₁, a₂) a₁).2 (Sym2.mem_mk_left _ _)
      · exact (memX_edge (by decide) s(a₁, a₂) a₂).2 (Sym2.mem_mk_right _ _)
      · rintro B ⟨hB, hxB, hyB⟩
        rcases mem_union.1 hB with hB | hB
        · exact (rowrow_cover (by decide) ha hB hxB hyB).2
        · exact absurd hxB (hA2 hx hB)
  -- (0,1)
  · have hr : ¬ Reserved col d.μ (resid d.MB) x y := by
      rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨hx', hy'⟩ | ⟨h, -⟩)
      · rw [hy] at h; exact absurd h (by decide)
      · rw [hx] at h; exact absurd h (by decide)
      · have := (d.μ ⟨x, hx'⟩).2; rw [← hy', hy] at this; exact absurd this (by decide)
      · rw [hx] at h; exact absurd h (by decide)
    refine ⟨fun h => absurd h hr, fun _ => ?_⟩
    obtain ⟨B, ⟨hB, hxB, hyB⟩, hu⟩ :=
      rowcol_unique (G := GA d.μ) (χ := d.χA) (M := d.MA) (by decide) hv.hχA hv.hMA ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨B, ⟨mem_union.2 (Or.inl hB), hxB, hyB⟩, ?_⟩
    rintro B' ⟨hB', hxB', hyB'⟩
    rcases mem_union.1 hB' with hB' | hB'
    · exact hu B' ⟨hB', hxB', hyB'⟩
    · exact absurd hxB' (hA2 hx hB')
  -- (0,2): reserved
  · have hr : Reserved col d.μ (resid d.MB) x y := Or.inl ⟨hx, hy⟩
    refine ⟨fun _ B hB ⟨hxB, hyB⟩ => ?_, fun h => absurd hr h⟩
    rcases mem_union.1 hB with hB | hB
    · exact hC1 hy hB hyB
    · exact hA2 hx hB hxB
  -- (1,0) impossible by `hle`
  · rw [hx, hy] at hle; exact absurd hle (by decide)
  -- (1,1)
  · set v₁ : BType col := ⟨x, hx⟩
    set v₂ : BType col := ⟨y, hy⟩
    have hvv : v₁ ≠ v₂ := fun h => hxy (congrArg Subtype.val h)
    have hr : ¬ Reserved col d.μ (resid d.MB) x y := by
      rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> rw [hx] at h <;> exact absurd h (by decide)
    refine ⟨fun h => absurd h hr, fun _ => ?_⟩
    by_cases hused : ∃ i, s(v₁, v₂) ∈ d.MA i
    · obtain ⟨i, hi⟩ := hused
      refine ⟨blk i.1 s(v₁, v₂), ⟨mem_union.2 (Or.inl (pair_block_mem hi)),
        (memY_pair (by decide) i _ v₁).2 (Sym2.mem_mk_left _ _),
        (memY_pair (by decide) i _ v₂).2 (Sym2.mem_mk_right _ _)⟩, ?_⟩
      rintro B ⟨hB, hxB, hyB⟩
      rcases mem_union.1 hB with hB | hB
      · obtain ⟨i', hi', rfl⟩ := colcol_cover (by decide) hvv hB hxB hyB
        rw [row_of_pair_unique hv.hMAd hi' hi]
      · have := (rowrow_cover (by decide) hvv hB hxB hyB).1
        exact absurd hi ((GB_adj_iff.1 this).2 i)
    · push_neg at hused
      have hadj : (GB d.MA).Adj v₁ v₂ := GB_adj_iff.2 ⟨hvv, hused⟩
      refine ⟨blk (d.χB s(v₁, v₂)).1 s(v₁, v₂), ⟨mem_union.2 (Or.inr (edge_block_mem
        ((SimpleGraph.mem_edgeFinset).2 hadj))),
        (memX_edge (by decide) _ v₁).2 (Sym2.mem_mk_left _ _),
        (memX_edge (by decide) _ v₂).2 (Sym2.mem_mk_right _ _)⟩, ?_⟩
      rintro B ⟨hB, hxB, hyB⟩
      rcases mem_union.1 hB with hB | hB
      · obtain ⟨i, hi, -⟩ := colcol_cover (by decide) hvv hB hxB hyB
        exact absurd hi (hused i)
      · exact (rowrow_cover (by decide) hvv hB hxB hyB).2
  -- (1,2)
  · have hr : ¬ Reserved col d.μ (resid d.MB) x y := by
      rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> rw [hx] at h <;> exact absurd h (by decide)
    refine ⟨fun h => absurd h hr, fun _ => ?_⟩
    obtain ⟨B, ⟨hB, hxB, hyB⟩, hu⟩ :=
      rowcol_unique (G := GB d.MA) (χ := d.χB) (M := d.MB) (by decide) hv.hχB hv.hMB ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨B, ⟨mem_union.2 (Or.inr hB), hxB, hyB⟩, ?_⟩
    rintro B' ⟨hB', hxB', hyB'⟩
    rcases mem_union.1 hB' with hB' | hB'
    · exact absurd hyB' (hC1 hy hB')
    · exact hu B' ⟨hB', hxB', hyB'⟩
  -- (2,0), (2,1) impossible
  · rw [hx, hy] at hle; exact absurd hle (by decide)
  · rw [hx, hy] at hle; exact absurd hle (by decide)
  -- (2,2)
  · set u₁ : CType col := ⟨x, hx⟩
    set u₂ : CType col := ⟨y, hy⟩
    have huu : u₁ ≠ u₂ := fun h => hxy (congrArg Subtype.val h)
    have hres : Reserved col d.μ (resid d.MB) x y ↔ ∀ j, s(u₁, u₂) ∉ d.MB j := by
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨hx', hy', hadj⟩)
        · rw [hx] at h; exact absurd h (by decide)
        · rw [hy] at h; exact absurd h (by decide)
        · rw [hx] at h; exact absurd h (by decide)
        · exact (resid_adj_iff.1 hadj).2
      · intro h; exact Or.inr (Or.inr (Or.inr ⟨hx, hy, resid_adj_iff.2 ⟨huu, h⟩⟩))
    refine ⟨fun hr B hB ⟨hxB, hyB⟩ => ?_, fun hr => ?_⟩
    · rcases mem_union.1 hB with hB | hB
      · exact hC1 hx hB hxB
      · obtain ⟨j, hj, -⟩ := colcol_cover (by decide) huu hB hxB hyB
        exact hres.1 hr j hj
    · rw [hres] at hr
      push_neg at hr
      obtain ⟨j, hj⟩ := hr
      refine ⟨blk j.1 s(u₁, u₂), ⟨mem_union.2 (Or.inr (pair_block_mem hj)),
        (memY_pair (by decide) j _ u₁).2 (Sym2.mem_mk_left _ _),
        (memY_pair (by decide) j _ u₂).2 (Sym2.mem_mk_right _ _)⟩, ?_⟩
      rintro B ⟨hB, hxB, hyB⟩
      rcases mem_union.1 hB with hB | hB
      · exact absurd hxB (hC1 hx hB)
      · obtain ⟨j', hj', rfl⟩ := colcol_cover (by decide) huu hB hxB hyB
        rw [row_of_pair_unique hv.hMBd hj' hj]

/-- **L182 coverage**: the prefix satisfies the hypotheses of L184. -/
theorem prefix_cover (hv : d.Valid) :
    (∀ B ∈ prefixP d, B.card = 3) ∧ (∀ B ∈ prefixP d, (B.image col).card = 2) ∧
    (∀ x y, x ≠ y → Reserved col d.μ (resid d.MB) x y → ∀ B ∈ prefixP d, ¬ (x ∈ B ∧ y ∈ B)) ∧
    (∀ x y, x ≠ y → ¬ Reserved col d.μ (resid d.MB) x y →
      ∃! B, B ∈ prefixP d ∧ x ∈ B ∧ y ∈ B) := by
  refine ⟨fun B hB => (prefix_card hv hB).1, fun B hB => (prefix_card hv hB).2, ?_, ?_⟩
  · intro x y hxy hr B hB hxyB
    rcases le_total (col x) (col y) with hle | hle
    · exact (prefix_pairs_le hv hxy hle).1 hr B hB hxyB
    · exact (prefix_pairs_le hv (Ne.symm hxy) hle).1 (reserved_symm hv hr) B hB ⟨hxyB.2, hxyB.1⟩
  · intro x y hxy hr
    rcases le_total (col x) (col y) with hle | hle
    · exact (prefix_pairs_le hv hxy hle).2 hr
    · obtain ⟨B, ⟨hB, hyB, hxB⟩, hu⟩ := (prefix_pairs_le hv (Ne.symm hxy) hle).2
        (fun h => hr (reserved_symm hv h))
      exact ⟨B, ⟨hB, hxB, hyB⟩, fun B' ⟨h1, h2, h3⟩ => hu B' ⟨h1, h3, h2⟩⟩

end CDRBicolour.Prefix
