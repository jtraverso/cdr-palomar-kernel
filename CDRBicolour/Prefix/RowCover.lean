/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.Cover

/-!
# Block coverage inside one row system

Rows are the points of colour class `cx`, colours the points of class `cy ≠ cx`.
Edge blocks `{χ e} ∪ e` (`e` an edge of the row graph) and pair blocks `{j} ∪ p`
(`p ∈ M j`) cover:

* every row–colour pair exactly once (`rowcol_unique`);
* a row–row pair only through the edge block of that edge (`rowrow_cover`);
* a colour–colour pair only through a pair block containing it (`colcol_cover`).
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing.ColourClasses

variable {V : Type*} [Fintype V] [DecidableEq V] {col : V → Fin 3} {cx cy : Fin 3}
  (G : SimpleGraph {v // col v = cx}) [DecidableRel G.Adj]
  (χ : Sym2 {v // col v = cx} → {v // col v = cy})
  (M : {v // col v = cx} → Finset (Sym2 {v // col v = cy}))

/-- Edge blocks and pair blocks of a row system. -/
def rsBlocks : Finset (Finset V) :=
  (G.edgeFinset.image fun e => blk (χ e).1 e) ∪
    (univ.biUnion fun j => (M j).image fun p => blk j.1 p)

theorem mem_rsBlocks {B : Finset V} :
    B ∈ rsBlocks G χ M ↔ (∃ e ∈ G.edgeFinset, B = blk (χ e).1 e) ∨
      ∃ j, ∃ p ∈ M j, B = blk j.1 p := by
  simp only [rsBlocks, mem_union, mem_image, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨j, p, hp, rfl⟩)
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨j, p, hp, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨j, p, hp, rfl⟩)
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨j, p, hp, rfl⟩

variable {G χ M}

/-- A point of class `cx` in an edge block lies on the edge. -/
theorem memX_edge (hne : cx ≠ cy) (e : Sym2 {v // col v = cx}) (x : {v // col v = cx}) :
    x.1 ∈ blk (χ e).1 e ↔ x ∈ e := by
  rw [mem_blk]
  constructor
  · rintro (h | ⟨q, hq, hqx⟩)
    · exact absurd ((x.2.symm.trans (congrArg col h)).trans (χ e).2) hne
    · rwa [← Subtype.ext hqx]
  · intro h; exact Or.inr ⟨x, h, rfl⟩

/-- A point of class `cy` in an edge block is the colour of the edge. -/
theorem memY_edge (hne : cx ≠ cy) (e : Sym2 {v // col v = cx}) (y : {v // col v = cy}) :
    y.1 ∈ blk (χ e).1 e ↔ y = χ e := by
  rw [mem_blk]
  constructor
  · rintro (h | ⟨q, -, hqy⟩)
    · exact Subtype.ext h
    · exact absurd ((q.2.symm.trans (congrArg col hqy)).trans y.2) hne
  · intro h; exact Or.inl (by rw [h])

theorem memX_pair (hne : cx ≠ cy) (j : {v // col v = cx}) (p : Sym2 {v // col v = cy})
    (x : {v // col v = cx}) : x.1 ∈ blk j.1 p ↔ x = j := by
  rw [mem_blk]
  constructor
  · rintro (h | ⟨q, -, hqx⟩)
    · exact Subtype.ext h
    · exact absurd ((q.2.symm.trans (congrArg col hqx)).trans x.2) hne.symm
  · intro h; exact Or.inl (by rw [h])

theorem memY_pair (hne : cx ≠ cy) (j : {v // col v = cx}) (p : Sym2 {v // col v = cy})
    (y : {v // col v = cy}) : y.1 ∈ blk j.1 p ↔ y ∈ p := by
  rw [mem_blk]
  constructor
  · rintro (h | ⟨q, hq, hqy⟩)
    · exact absurd ((y.2.symm.trans (congrArg col h)).trans j.2) hne.symm
    · rwa [← Subtype.ext hqy]
  · intro h; exact Or.inr ⟨y, h, rfl⟩

/-- A point of a third class lies in no block. -/
theorem not_mem_rsBlocks {z : V} (hzx : col z ≠ cx) (hzy : col z ≠ cy) {B : Finset V}
    (hB : B ∈ rsBlocks G χ M) : z ∉ B := by
  rw [mem_rsBlocks] at hB
  rcases hB with ⟨e, -, rfl⟩ | ⟨j, p, -, rfl⟩
  · rw [mem_blk]
    rintro (h | ⟨q, -, hq⟩)
    · exact hzy (h ▸ (χ e).2)
    · exact hzx (hq ▸ q.2)
  · rw [mem_blk]
    rintro (h | ⟨q, -, hq⟩)
    · exact hzx (h ▸ j.2)
    · exact hzy (hq ▸ q.2)

/-- **Row–colour pairs are covered exactly once.** -/
theorem rowcol_unique (hne : cx ≠ cy) (hχ : ProperOn G.edgeFinset χ)
    (hM : ∀ j, IsPerfectPairing (M j) (miss G χ j))
    (j : {v // col v = cx}) (v : {v // col v = cy}) :
    ∃! B, B ∈ rsBlocks G χ M ∧ j.1 ∈ B ∧ v.1 ∈ B := by
  by_cases hv : v ∈ present G χ j
  · obtain ⟨e, he, hev⟩ := mem_present.1 hv
    have heE : e ∈ G.edgeFinset := SimpleGraph.incidenceFinset_subset G j he
    have hje : j ∈ e := (SimpleGraph.mem_incidenceFinset.1 he).2
    refine ⟨blk (χ e).1 e, ⟨(mem_rsBlocks G χ M).2 (Or.inl ⟨e, heE, rfl⟩),
      (memX_edge hne e j).2 hje, (memY_edge hne e v).2 hev.symm⟩, ?_⟩
    rintro B ⟨hB, hjB, hvB⟩
    rcases (mem_rsBlocks G χ M).1 hB with ⟨e', he', rfl⟩ | ⟨j', p, hp, rfl⟩
    · have hje' := (memX_edge hne e' j).1 hjB
      have hve' := (memY_edge hne e' v).1 hvB
      by_contra hneq
      have hee : e' ≠ e := fun h => hneq (by rw [h])
      have hd := hχ e' he' e heE hee (by rw [← hve', hev])
      exact Finset.disjoint_left.1 hd (Sym2.mem_toFinset.2 hje') (Sym2.mem_toFinset.2 hje)
    · have hjj := (memX_pair hne j' p j).1 hjB
      have hvp := (memY_pair hne j' p v).1 hvB
      subst hjj
      have := (hM j).2.1 p hp v hvp
      rw [miss, mem_sdiff] at this
      exact absurd hv this.2
  · have hvm : v ∈ miss G χ j := by rw [miss, mem_sdiff]; exact ⟨mem_univ _, hv⟩
    obtain ⟨p, ⟨hp, hvp⟩, hpu⟩ := (hM j).2.2 v hvm
    refine ⟨blk j.1 p, ⟨(mem_rsBlocks G χ M).2 (Or.inr ⟨j, p, hp, rfl⟩),
      (memX_pair hne j p j).2 rfl, (memY_pair hne j p v).2 hvp⟩, ?_⟩
    rintro B ⟨hB, hjB, hvB⟩
    rcases (mem_rsBlocks G χ M).1 hB with ⟨e', he', rfl⟩ | ⟨j', p', hp', rfl⟩
    · have hje' := (memX_edge hne e' j).1 hjB
      have hve' := (memY_edge hne e' v).1 hvB
      exact absurd (mem_present.2 ⟨e', SimpleGraph.mem_incidenceFinset.2
        ⟨(SimpleGraph.mem_edgeFinset).1 he', hje'⟩,
        hve'.symm⟩) hv
    · have hjj := (memX_pair hne j' p' j).1 hjB
      have hvp' := (memY_pair hne j' p' v).1 hvB
      subst hjj
      rw [hpu p' ⟨hp', hvp'⟩]

/-- **Row–row pairs**: only the edge block of `s(j, j')`. -/
theorem rowrow_cover (hne : cx ≠ cy) {j j' : {v // col v = cx}} (hjj : j ≠ j') {B : Finset V}
    (hB : B ∈ rsBlocks G χ M) (hj : j.1 ∈ B) (hj' : j'.1 ∈ B) :
    G.Adj j j' ∧ B = blk (χ s(j, j')).1 s(j, j') := by
  rcases (mem_rsBlocks G χ M).1 hB with ⟨e, he, rfl⟩ | ⟨i, p, -, rfl⟩
  · have h1 := (memX_edge hne e j).1 hj
    have h2 := (memX_edge hne e j').1 hj'
    have hes : e = s(j, j') := (Sym2.mem_and_mem_iff hjj).1 ⟨h1, h2⟩
    subst hes
    exact ⟨(SimpleGraph.mem_edgeFinset).1 he, rfl⟩
  · have h1 := (memX_pair hne i p j).1 hj
    have h2 := (memX_pair hne i p j').1 hj'
    exact absurd (h1.trans h2.symm) hjj

/-- **Colour–colour pairs**: only a pair block containing that pair. -/
theorem colcol_cover (hne : cx ≠ cy) {v v' : {v // col v = cy}} (hvv : v ≠ v') {B : Finset V}
    (hB : B ∈ rsBlocks G χ M) (hv : v.1 ∈ B) (hv' : v'.1 ∈ B) :
    ∃ j, s(v, v') ∈ M j ∧ B = blk j.1 s(v, v') := by
  rcases (mem_rsBlocks G χ M).1 hB with ⟨e, -, rfl⟩ | ⟨j, p, hp, rfl⟩
  · have h1 := (memY_edge hne e v).1 hv
    have h2 := (memY_edge hne e v').1 hv'
    exact absurd (h1.trans h2.symm) hvv
  · have h1 := (memY_pair hne j p v).1 hv
    have h2 := (memY_pair hne j p v').1 hv'
    have hps : p = s(v, v') := (Sym2.mem_and_mem_iff hvv).1 ⟨h1, h2⟩
    subst hps
    exact ⟨j, hp, rfl⟩

theorem pair_block_mem {j : {v // col v = cx}} {p : Sym2 {v // col v = cy}} (hp : p ∈ M j) :
    blk j.1 p ∈ rsBlocks G χ M :=
  (mem_rsBlocks G χ M).2 (Or.inr ⟨j, p, hp, rfl⟩)

theorem edge_block_mem {e : Sym2 {v // col v = cx}} (he : e ∈ G.edgeFinset) :
    blk (χ e).1 e ∈ rsBlocks G χ M :=
  (mem_rsBlocks G χ M).2 (Or.inl ⟨e, he, rfl⟩)

end CDRBicolour.Prefix
