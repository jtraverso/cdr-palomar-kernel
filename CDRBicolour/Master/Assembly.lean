/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.Prefix
public import CDRBicolour.Prefix.Residual

/-!
# L159: assembly of the AAC-free master construction

Three row systems on the classes `A = col⁻¹ 0`, `B = col⁻¹ 1`, `C = col⁻¹ 2`:

1. rows `A`, colours `B`, row graph `K_A` (`⊤`): blocks `AAB = {χ₁ e} ∪ e` and `ABB = {i} ∪ p`;
2. rows `B`, colours `C`, row graph `G₂ =` BB pairs unused by ABB: blocks `BBC`, `BCC`;
3. rows `C`, colours `A`, row graph `G₃ =` CC pairs unused by BCC, whose colouring misses no
   colour at any row (a 1-factorization by `A`): blocks `ACC`, and no pair blocks.

`master_assembly`: the union of the three block families is a Steiner triple system all of whose
blocks see exactly two classes (there are no AAC blocks).
-/

@[expose] public section

namespace CDRBicolour.Master

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix CDRBicolour.L184

variable {V : Type*} [Fintype V] [DecidableEq V] {col : V → Fin 3}

/-- The empty pairing is a perfect pairing of the empty set. -/
theorem isPerfectPairing_empty {Cl : Type*} : IsPerfectPairing (∅ : Finset (Sym2 Cl)) ∅ :=
  ⟨fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _),
    fun _ h => absurd h (notMem_empty _)⟩

theorem pairDisjoint_empty {Rw Cl : Type*} : PairDisjoint (fun _ : Rw => (∅ : Finset (Sym2 Cl))) :=
  fun _ _ _ => disjoint_empty_left _

/-- **Master assembly (L159).** -/
theorem master_assembly
    (χ₁ : Sym2 (AType col) → BType col) (M₁ : AType col → Finset (Sym2 (BType col)))
    (hχ₁ : ProperOn (⊤ : SimpleGraph (AType col)).edgeFinset χ₁)
    (hM₁ : ∀ i, IsPerfectPairing (M₁ i) (miss ⊤ χ₁ i)) (hM₁d : PairDisjoint M₁)
    (χ₂ : Sym2 (BType col) → CType col) (M₂ : BType col → Finset (Sym2 (CType col)))
    (hχ₂ : ProperOn (unusedGraph M₁).edgeFinset χ₂)
    (hM₂ : ∀ j, IsPerfectPairing (M₂ j) (miss (unusedGraph M₁) χ₂ j)) (hM₂d : PairDisjoint M₂)
    (χ₃ : Sym2 (CType col) → AType col)
    (hχ₃ : ProperOn (unusedGraph M₂).edgeFinset χ₃)
    (hM₃ : ∀ c, miss (unusedGraph M₂) χ₃ c = ∅) :
    ∃ S : STS V, IsStrictBicolouring S col := by
  classical
  set M₃ : CType col → Finset (Sym2 (AType col)) := fun _ => ∅ with hM₃def
  have hM₃p : ∀ c, IsPerfectPairing (M₃ c) (miss (unusedGraph M₂) χ₃ c) := by
    intro c; rw [hM₃ c]; exact isPerfectPairing_empty
  set R₁ : Finset (Finset V) := rsBlocks (⊤ : SimpleGraph (AType col)) χ₁ M₁ with hR₁
  set R₂ : Finset (Finset V) := rsBlocks (unusedGraph M₁) χ₂ M₂ with hR₂
  set R₃ : Finset (Finset V) := rsBlocks (unusedGraph M₂) χ₃ M₃ with hR₃
  set P : Finset (Finset V) := R₁ ∪ R₂ ∪ R₃ with hP
  -- points outside the classes of a row system
  have hA2 : ∀ {z : V} {B : Finset V}, col z = 0 → B ∈ R₂ → z ∉ B :=
    fun hz hB => not_mem_rsBlocks (by rw [hz]; decide) (by rw [hz]; decide) hB
  have hB3 : ∀ {z : V} {B : Finset V}, col z = 1 → B ∈ R₃ → z ∉ B :=
    fun hz hB => not_mem_rsBlocks (by rw [hz]; decide) (by rw [hz]; decide) hB
  have hC1 : ∀ {z : V} {B : Finset V}, col z = 2 → B ∈ R₁ → z ∉ B :=
    fun hz hB => not_mem_rsBlocks (by rw [hz]; decide) (by rw [hz]; decide) hB
  -- shapes of blocks
  have hshape : ∀ B ∈ P, B.card = 3 ∧ (B.image col).card = 2 := by
    intro B hB
    rcases mem_union.1 hB with hB | hB
    · rcases mem_union.1 hB with hB | hB
      · rcases (mem_rsBlocks _ _ _).1 hB with ⟨e, he, rfl⟩ | ⟨j, p, hp, rfl⟩
        · exact blk_card (by decide) _ (χ₁ e).2 e (SimpleGraph.not_isDiag_of_mem_edgeFinset he)
        · exact blk_card (by decide) _ j.2 p ((hM₁ j).1 p hp)
      · rcases (mem_rsBlocks _ _ _).1 hB with ⟨e, he, rfl⟩ | ⟨j, p, hp, rfl⟩
        · exact blk_card (by decide) _ (χ₂ e).2 e (SimpleGraph.not_isDiag_of_mem_edgeFinset he)
        · exact blk_card (by decide) _ j.2 p ((hM₂ j).1 p hp)
    · rcases (mem_rsBlocks _ _ _).1 hB with ⟨e, he, rfl⟩ | ⟨j, p, hp, rfl⟩
      · exact blk_card (by decide) _ (χ₃ e).2 e (SimpleGraph.not_isDiag_of_mem_edgeFinset he)
      · exact absurd hp (notMem_empty _)
  -- the coverage, for `col x ≤ col y`
  have hcov : ∀ x y : V, x ≠ y → col x ≤ col y → ∃! B, B ∈ P ∧ x ∈ B ∧ y ∈ B := by
    intro x y hxy hle
    rcases fin3_cases (col x) with hx | hx | hx <;> rcases fin3_cases (col y) with hy | hy | hy
    -- (0,0): AAB
    · set a₁ : AType col := ⟨x, hx⟩
      set a₂ : AType col := ⟨y, hy⟩
      have ha : a₁ ≠ a₂ := fun h => hxy (congrArg Subtype.val h)
      have hadj : (⊤ : SimpleGraph (AType col)).Adj a₁ a₂ := ha
      refine ⟨blk (χ₁ s(a₁, a₂)).1 s(a₁, a₂), ⟨mem_union.2 (Or.inl (mem_union.2 (Or.inl
        (edge_block_mem ((SimpleGraph.mem_edgeFinset).2 hadj))))), ?_, ?_⟩, ?_⟩
      · exact (memX_edge (by decide) s(a₁, a₂) a₁).2 (Sym2.mem_mk_left _ _)
      · exact (memX_edge (by decide) s(a₁, a₂) a₂).2 (Sym2.mem_mk_right _ _)
      · rintro B ⟨hB, hxB, hyB⟩
        rcases mem_union.1 hB with hB | hB
        · rcases mem_union.1 hB with hB | hB
          · exact (rowrow_cover (by decide) ha hB hxB hyB).2
          · exact absurd hxB (hA2 hx hB)
        · obtain ⟨j, hj, -⟩ := colcol_cover (by decide) ha hB hxB hyB
          exact absurd hj (notMem_empty _)
    -- (0,1): AAB or ABB
    · obtain ⟨B, ⟨hB, hxB, hyB⟩, hu⟩ := rowcol_unique (G := (⊤ : SimpleGraph (AType col)))
        (χ := χ₁) (M := M₁) (by decide) hχ₁ hM₁ ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨B, ⟨mem_union.2 (Or.inl (mem_union.2 (Or.inl hB))), hxB, hyB⟩, ?_⟩
      rintro B' ⟨hB', hxB', hyB'⟩
      rcases mem_union.1 hB' with hB' | hB'
      · rcases mem_union.1 hB' with hB' | hB'
        · exact hu B' ⟨hB', hxB', hyB'⟩
        · exact absurd hxB' (hA2 hx hB')
      · exact absurd hyB' (hB3 hy hB')
    -- (0,2): ACC
    · obtain ⟨B, ⟨hB, hyB, hxB⟩, hu⟩ := rowcol_unique (G := unusedGraph M₂) (χ := χ₃) (M := M₃)
        (by decide) hχ₃ hM₃p ⟨y, hy⟩ ⟨x, hx⟩
      refine ⟨B, ⟨mem_union.2 (Or.inr hB), hxB, hyB⟩, ?_⟩
      rintro B' ⟨hB', hxB', hyB'⟩
      rcases mem_union.1 hB' with hB' | hB'
      · rcases mem_union.1 hB' with hB' | hB'
        · exact absurd hyB' (hC1 hy hB')
        · exact absurd hxB' (hA2 hx hB')
      · exact hu B' ⟨hB', hyB', hxB'⟩
    -- (1,0) impossible
    · rw [hx, hy] at hle; exact absurd hle (by decide)
    -- (1,1): ABB or BBC
    · set v₁ : BType col := ⟨x, hx⟩
      set v₂ : BType col := ⟨y, hy⟩
      have hvv : v₁ ≠ v₂ := fun h => hxy (congrArg Subtype.val h)
      by_cases hused : ∃ i, s(v₁, v₂) ∈ M₁ i
      · obtain ⟨i, hi⟩ := hused
        refine ⟨blk i.1 s(v₁, v₂), ⟨mem_union.2 (Or.inl (mem_union.2 (Or.inl
          (pair_block_mem hi)))),
          (memY_pair (by decide) i _ v₁).2 (Sym2.mem_mk_left _ _),
          (memY_pair (by decide) i _ v₂).2 (Sym2.mem_mk_right _ _)⟩, ?_⟩
        rintro B ⟨hB, hxB, hyB⟩
        rcases mem_union.1 hB with hB | hB
        · rcases mem_union.1 hB with hB | hB
          · obtain ⟨i', hi', rfl⟩ := colcol_cover (by decide) hvv hB hxB hyB
            rw [row_of_pair_unique hM₁d hi' hi]
          · have := (rowrow_cover (by decide) hvv hB hxB hyB).1
            exact absurd hi (((unusedGraph_adj_iff (M := M₁)).1 this).2 i)
        · exact absurd hxB (hB3 hx hB)
      · push Not at hused
        have hadj : (unusedGraph M₁).Adj v₁ v₂ := (unusedGraph_adj_iff (M := M₁)).2 ⟨hvv, hused⟩
        refine ⟨blk (χ₂ s(v₁, v₂)).1 s(v₁, v₂), ⟨mem_union.2 (Or.inl (mem_union.2 (Or.inr
          (edge_block_mem ((SimpleGraph.mem_edgeFinset).2 hadj))))),
          (memX_edge (by decide) _ v₁).2 (Sym2.mem_mk_left _ _),
          (memX_edge (by decide) _ v₂).2 (Sym2.mem_mk_right _ _)⟩, ?_⟩
        rintro B ⟨hB, hxB, hyB⟩
        rcases mem_union.1 hB with hB | hB
        · rcases mem_union.1 hB with hB | hB
          · obtain ⟨i, hi, -⟩ := colcol_cover (by decide) hvv hB hxB hyB
            exact absurd hi (hused i)
          · exact (rowrow_cover (by decide) hvv hB hxB hyB).2
        · exact absurd hxB (hB3 hx hB)
    -- (1,2): BBC or BCC
    · obtain ⟨B, ⟨hB, hxB, hyB⟩, hu⟩ := rowcol_unique (G := unusedGraph M₁) (χ := χ₂) (M := M₂)
        (by decide) hχ₂ hM₂ ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨B, ⟨mem_union.2 (Or.inl (mem_union.2 (Or.inr hB))), hxB, hyB⟩, ?_⟩
      rintro B' ⟨hB', hxB', hyB'⟩
      rcases mem_union.1 hB' with hB' | hB'
      · rcases mem_union.1 hB' with hB' | hB'
        · exact absurd hyB' (hC1 hy hB')
        · exact hu B' ⟨hB', hxB', hyB'⟩
      · exact absurd hxB' (hB3 hx hB')
    -- (2,0), (2,1) impossible
    · rw [hx, hy] at hle; exact absurd hle (by decide)
    · rw [hx, hy] at hle; exact absurd hle (by decide)
    -- (2,2): BCC or ACC
    · set u₁ : CType col := ⟨x, hx⟩
      set u₂ : CType col := ⟨y, hy⟩
      have huu : u₁ ≠ u₂ := fun h => hxy (congrArg Subtype.val h)
      by_cases hused : ∃ j, s(u₁, u₂) ∈ M₂ j
      · obtain ⟨j, hj⟩ := hused
        refine ⟨blk j.1 s(u₁, u₂), ⟨mem_union.2 (Or.inl (mem_union.2 (Or.inr
          (pair_block_mem hj)))),
          (memY_pair (by decide) j _ u₁).2 (Sym2.mem_mk_left _ _),
          (memY_pair (by decide) j _ u₂).2 (Sym2.mem_mk_right _ _)⟩, ?_⟩
        rintro B ⟨hB, hxB, hyB⟩
        rcases mem_union.1 hB with hB | hB
        · rcases mem_union.1 hB with hB | hB
          · exact absurd hxB (hC1 hx hB)
          · obtain ⟨j', hj', rfl⟩ := colcol_cover (by decide) huu hB hxB hyB
            rw [row_of_pair_unique hM₂d hj' hj]
        · have := (rowrow_cover (by decide) huu hB hxB hyB).1
          exact absurd hj (((unusedGraph_adj_iff (M := M₂)).1 this).2 j)
      · push Not at hused
        have hadj : (unusedGraph M₂).Adj u₁ u₂ := (unusedGraph_adj_iff (M := M₂)).2 ⟨huu, hused⟩
        refine ⟨blk (χ₃ s(u₁, u₂)).1 s(u₁, u₂), ⟨mem_union.2 (Or.inr
          (edge_block_mem ((SimpleGraph.mem_edgeFinset).2 hadj))),
          (memX_edge (by decide) _ u₁).2 (Sym2.mem_mk_left _ _),
          (memX_edge (by decide) _ u₂).2 (Sym2.mem_mk_right _ _)⟩, ?_⟩
        rintro B ⟨hB, hxB, hyB⟩
        rcases mem_union.1 hB with hB | hB
        · rcases mem_union.1 hB with hB | hB
          · exact absurd hxB (hC1 hx hB)
          · obtain ⟨j, hj, -⟩ := colcol_cover (by decide) huu hB hxB hyB
            exact absurd hj (hused j)
        · exact (rowrow_cover (by decide) huu hB hxB hyB).2
  refine ⟨⟨P, fun B hB => (hshape B hB).1, fun x y hxy => ?_⟩, fun B hB => (hshape B hB).2⟩
  rcases le_total (col x) (col y) with hle | hle
  · exact hcov x y hxy hle
  · obtain ⟨B, ⟨hB, hyB, hxB⟩, hu⟩ := hcov y x (Ne.symm hxy) hle
    exact ⟨B, ⟨hB, hxB, hyB⟩, fun B' ⟨h1, h2, h3⟩ => hu B' ⟨h1, h3, h2⟩⟩

end CDRBicolour.Master
