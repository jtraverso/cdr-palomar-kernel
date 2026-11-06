/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Graphs
public import LeanPool.Vizing.Equitable
public import LeanPool.Vizing.Main
public import LeanPool.Vizing.LineGraphColouring

/-!
# The planted minority structure (item 3, corners)

Ingredients for one class `X` (palette class `W = X + 2`):

* `exists_cls_emb`: an embedding `ℤ/|X| ↪ V` onto the class `X`;
* `exists_equitable_proper`: a proper edge colouring of a graph with `maxDegree < p` by `p`
  colours whose classes differ by at most one (Vizing + equitable rebalancing);
* `exists_sizes_equiv`: two-valued class sizes `q, q+1` with exactly `r` large ones can be
  matched to the positions `< r` of `ℤ/p`.
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset SimpleGraph TypedTriangle LeanPool.Vizing.ColourClasses LeanPool.Vizing.Equitable
  LeanPool.Vizing.EquitableDefinitions LeanPool.Vizing.LineGraphColouring

/-! ### Embedding a class -/

theorem exists_cls_emb {V : Type*} [Fintype V] (lab : V → Fin 3) (X : Fin 3) {s : ℕ} [NeZero s]
    (hs : csz lab X = s) :
    ∃ f : ZMod s ↪ V, (∀ z, lab (f z) = X) ∧ ∀ v, lab v = X → ∃ z, f z = v := by
  have hc : Fintype.card {v // lab v = X} = s := by
    rw [Fintype.card_subtype]; exact hs
  let e : {v // lab v = X} ≃ ZMod s := (Fintype.equivFinOfCardEq hc).trans (ZMod.finEquiv s).toEquiv
  refine ⟨⟨fun z => (e.symm z).1, fun z z' h => e.symm.injective (Subtype.ext h)⟩,
    fun z => (e.symm z).2, fun v hv => ⟨e ⟨v, hv⟩, by
    show (e.symm (e ⟨v, hv⟩)).1 = v; rw [Equiv.symm_apply_apply]⟩⟩

/-! ### Equitable proper colourings -/

theorem exists_equitable_proper {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {p : ℕ} (hp : 0 < p)
    (hdeg : G.maxDegree + 1 ≤ p) :
    ∃ colour : Sym2 V → Fin p, ProperOn G.edgeFinset colour ∧ IsEquitable G.edgeFinset colour := by
  have : Inhabited (Fin p) := ⟨⟨0, hp⟩⟩
  have hcol : G.lineGraph.Colorable p := (LeanPool.Vizing.lineGraph_colorable G).mono hdeg
  obtain ⟨C⟩ := hcol
  exact exists_equitable_colouring (G := G) (edgeColourOfLineGraph C)
    (properOn_of_lineGraph_colouring C)

/-- Equitable class sizes with total `p q + r` (`r < p`) are `q` or `q + 1`, with `r` large ones. -/
theorem equitable_sizes {p q r : ℕ} (hr : r < p) (f : Fin p → ℕ) (hf : ∀ i j, f i ≤ f j + 1)
    (hsum : ∑ i, f i = p * q + r) :
    (∀ i, f i = q ∨ f i = q + 1) ∧ #(univ.filter fun i => f i = q + 1) = r := by
  have hp : 0 < p := by omega
  -- all values lie in `{m, m+1}` for `m = min`
  obtain ⟨i0, -, hi0⟩ := exists_min_image univ f ⟨⟨0, hp⟩, mem_univ _⟩
  set m := f i0
  have hlo : ∀ i, m ≤ f i := fun i => hi0 i (mem_univ _)
  have hhi : ∀ i, f i ≤ m + 1 := fun i => hf i i0
  set A := univ.filter fun i => f i = m + 1
  have hsplit : ∑ i, f i = p * m + #A := by
    have : ∀ i, f i = m + if f i = m + 1 then 1 else 0 := by
      intro i; have := hlo i; have := hhi i; split_ifs <;> omega
    rw [sum_congr rfl fun i _ => this i, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, sum_boole]
    simp [A]
  have hA : #A ≤ p := by
    calc #A ≤ #(univ : Finset (Fin p)) := card_le_univ _
      _ = p := by simp
  have hA' : #A < p := by
    rcases Nat.lt_or_ge #A p with h | h
    · exact h
    · exfalso
      have hAp : #A = p := le_antisymm hA h
      have : A = univ := eq_univ_of_card _ (by simpa using hAp)
      have := (mem_filter.1 (this ▸ mem_univ i0 : i0 ∈ A)).2
      simp [m] at this
  have hm : m = q ∧ #A = r := by
    rw [hsplit] at hsum
    have h1 : p * m + #A = p * q + r := hsum
    rcases Nat.lt_trichotomy m q with h | h | h
    · exfalso
      have : p * m + p ≤ p * q := by nlinarith
      omega
    · subst h; omega
    · exfalso
      have : p * q + p ≤ p * m := by nlinarith
      omega
  obtain ⟨hmq, hAr⟩ := hm
  refine ⟨fun i => ?_, ?_⟩
  · have := hlo i; have := hhi i; omega
  · rw [← hAr]; simp only [A, hmq]

/-- The positions `< r` of `Fin p`. -/
theorem card_fin_lt {p r : ℕ} (hr : r ≤ p) : #(univ.filter fun j : Fin p => j.val < r) = r := by
  have : (univ.filter fun j : Fin p => j.val < r).map Fin.valEmbedding = range r := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map, this, card_range]

/-- **Matching the large classes to the first positions.** -/
theorem exists_sizes_equiv {p q r : ℕ} (hr : r < p) (f : Fin p → ℕ)
    (hf : ∀ i, f i = q ∨ f i = q + 1) (hcnt : #(univ.filter fun i => f i = q + 1) = r) :
    ∃ σ : Fin p ≃ Fin p, ∀ i, f i = q + if (σ i).val < r then 1 else 0 := by
  have c1 : Fintype.card {i // f i = q + 1} = Fintype.card {j : Fin p // j.val < r} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hcnt, card_fin_lt hr.le]
  have c2 : Fintype.card {i // ¬ f i = q + 1} = Fintype.card {j : Fin p // ¬ j.val < r} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e1 := Fintype.equivOfCardEq c1
  let e2 := Fintype.equivOfCardEq c2
  refine ⟨Equiv.subtypeCongr e1 e2, fun i => ?_⟩
  by_cases hi : f i = q + 1
  · have h1 : (Equiv.subtypeCongr e1 e2 i) = (e1 ⟨i, hi⟩).1 := by simp [Equiv.subtypeCongr, hi]
    rw [h1, if_pos (e1 ⟨i, hi⟩).2, hi]
  · have h1 : (Equiv.subtypeCongr e1 e2 i) = (e2 ⟨i, hi⟩).1 := by simp [Equiv.subtypeCongr, hi]
    rw [h1, if_neg (e2 ⟨i, hi⟩).2]
    rcases hf i with h | h
    · rw [h]; rfl
    · exact absurd h hi

theorem finEquiv_val {p : ℕ} [NeZero p] (j : Fin p) : (ZMod.finEquiv p j).val = j.val := by
  rcases p with _ | p
  · exact absurd rfl (NeZero.ne 0)
  · rfl

theorem card_zmod_lt {p r : ℕ} [NeZero p] (hr : r < p) :
    #(univ.filter fun z : ZMod p => z.val < r) = r := by
  refine Eq.trans ?_ (card_fin_lt (p := p) hr.le)
  refine (card_bij (fun j _ => ZMod.finEquiv p j) (fun j hj => ?_) (fun j _ j' _ h => ?_)
    (fun i hi => ⟨(ZMod.finEquiv p).symm i, ?_, by simp⟩)).symm
  · simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rw [finEquiv_val]; exact hj
  · exact (ZMod.finEquiv p).injective h
  · simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [← finEquiv_val ((ZMod.finEquiv p).symm i)]; simpa using hi

/-- **Matching the large classes to the first positions of `ℤ/p`.** -/
theorem exists_sizes_equiv_zmod {p q r : ℕ} [NeZero p] (hr : r < p) (f : Fin p → ℕ)
    (hf : ∀ i, f i = q ∨ f i = q + 1) (hcnt : #(univ.filter fun i => f i = q + 1) = r) :
    ∃ σ : Fin p ≃ ZMod p, ∀ i, f i = q + if (σ i).val < r then 1 else 0 := by
  obtain ⟨σ, hσ⟩ := exists_sizes_equiv hr f hf hcnt
  refine ⟨σ.trans (ZMod.finEquiv p).toEquiv, fun i => ?_⟩
  rw [hσ i]
  simp only [Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, finEquiv_val]

/-! ### A graph on a class -/

section ClassGraph

variable {V : Type*} [Fintype V] {s : ℕ} [NeZero s] (f : ZMod s ↪ V) (G : SimpleGraph (ZMod s))

omit [Fintype V] [NeZero s] in
theorem map_neighborSet_emb (z : ZMod s) :
    ((G.map f).neighborSet (f z)).ncard = (G.neighborSet z).ncard := by
  rw [neighborSet_map, Set.ncard_image_of_injective _ f.injective]

theorem map_neighborSet_out {v : V} (hv : ∀ z, f z ≠ v) : (G.map f).neighborSet v = ∅ := by
  ext w
  constructor
  · intro h
    rw [mem_neighborSet, map_adj] at h
    obtain ⟨z, z', -, hz, -⟩ := h
    exact absurd hz (hv z)
  · intro h; exact absurd h (Set.notMem_empty _)

/-- The degree sum of a graph pushed into `V`. -/
theorem sum_ncard_map (g : ZMod s → ℕ) (hg : ∀ z, (G.neighborSet z).ncard = g z) :
    ∑ v, ((G.map f).neighborSet v).ncard = ∑ z, g z := by
  rw [← sum_subset (subset_univ (univ.map f)) (fun v _ hv => by
    rw [map_neighborSet_out f G (fun z hz => hv (mem_map.2 ⟨z, mem_univ _, hz⟩)), Set.ncard_empty]),
    sum_map]
  exact sum_congr rfl fun z _ => by rw [map_neighborSet_emb, hg]

end ClassGraph

/-! ### Blocks from a coloured graph -/

section Blocks

variable {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin 3)

/-- Leave neighbours of `u` with label `Y`. -/
def LN (P : Finset (Finset V)) (u : V) (Y : Fin 3) : Finset V :=
  univ.filter fun v => lab v = Y ∧ s(u, v) ∈ P.biUnion triEdges

variable {lab} {X W : Fin 3} (G : SimpleGraph V) {p : ℕ} (col : Sym2 V → Fin p) (apex : Fin p → V)

/-- The block of an edge: the edge and the apex of its colour. -/
def blk (e : Sym2 V) : Finset V := insert (apex (col e)) e.toFinset

/-- The blocks of a coloured graph. -/
def blocks : Finset (Finset V) := G.edgeFinset.image (blk col apex)

variable {G col apex} (hG : ∀ x y, G.Adj x y → lab x = X ∧ lab y = X)
  (hprop : ProperOn G.edgeFinset col) (hapex : Function.Injective apex)
  (hlab : ∀ i, lab (apex i) = W) (hXW : X ≠ W)

include hG hlab hXW in
theorem blk_mk {x y : V} (hxy : G.Adj x y) :
    blk col apex s(x, y) = {x, y, apex (col s(x, y))} := by
  ext v; simp [blk]; tauto

include hG hlab hXW in
theorem blk_shape {x y : V} (hxy : G.Adj x y) :
    x ≠ y ∧ x ≠ apex (col s(x, y)) ∧ y ≠ apex (col s(x, y)) ∧ lab x = X ∧ lab y = X := by
  obtain ⟨hx, hy⟩ := hG x y hxy
  refine ⟨hxy.ne, fun e => hXW ?_, fun e => hXW ?_, hx, hy⟩
  · rw [← hx, e, hlab]
  · rw [← hy, e, hlab]

include hG hlab hXW in
theorem triEdges_blk {x y : V} (hxy : G.Adj x y) :
    triEdges (blk col apex s(x, y)) =
      {s(x, y), s(x, apex (col s(x, y))), s(y, apex (col s(x, y)))} := by
  obtain ⟨h1, h2, h3, -⟩ := blk_shape (col := col) hG hlab hXW hxy
  rw [blk_mk hG hlab hXW hxy, triEdges_triple h1 h2 h3]

include hG hlab hXW in
/-- **Shape of the blocks.** -/
theorem blocks_shape {T : Finset V} (hT : T ∈ blocks G col apex) :
    ∃ u u' w, T = {u, u', w} ∧ u ≠ u' ∧ lab u = X ∧ lab u' = X ∧ lab w = W := by
  obtain ⟨e, he, rfl⟩ := mem_image.1 hT
  induction e using Sym2.ind with
  | _ x y =>
  have hxy : G.Adj x y := by simpa using he
  obtain ⟨h1, -, -, hx, hy⟩ := blk_shape (col := col) hG hlab hXW hxy
  exact ⟨x, y, _, blk_mk hG hlab hXW hxy, h1, hx, hy, hlab _⟩

include hG hlab hXW in
/-- The edge is recovered from the block. -/
theorem blk_inj {e e' : Sym2 V} (he : e ∈ G.edgeFinset) (he' : e' ∈ G.edgeFinset)
    (h : blk col apex e = blk col apex e') : e = e' := by
  have key : ∀ {f : Sym2 V}, f ∈ G.edgeFinset → ∀ v, v ∈ f ↔ v ∈ blk col apex f ∧ lab v = X := by
    intro f hf v
    induction f using Sym2.ind with
    | _ x y =>
    have hxy : G.Adj x y := by simpa using hf
    obtain ⟨-, -, -, hx, hy⟩ := blk_shape (col := col) hG hlab hXW hxy
    rw [blk_mk hG hlab hXW hxy]
    simp only [Sym2.mem_iff, mem_insert, mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hx⟩
      · exact ⟨Or.inr (Or.inl rfl), hy⟩
    · rintro ⟨(rfl | rfl | rfl), hv⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (hv.symm.trans (hlab _)) hXW
  ext v
  rw [key he, key he', h]

include hG hlab hXW in
theorem card_blocks : #(blocks G col apex) = #G.edgeFinset :=
  card_image_of_injOn fun e he e' he' h => blk_inj hG hlab hXW he he' h

include hG hlab hXW hprop hapex in
/-- **The blocks are edge-disjoint.** -/
theorem blocks_disjoint : (blocks G col apex : Set (Finset V)).PairwiseDisjoint triEdges := by
  intro T hT T' hT' hne
  obtain ⟨e, he, rfl⟩ := mem_image.1 hT
  obtain ⟨e', he', rfl⟩ := mem_image.1 hT'
  have hee : e ≠ e' := fun h => hne (by rw [h])
  induction e using Sym2.ind with
  | _ x y =>
  induction e' using Sym2.ind with
  | _ x' y' =>
  have a1 : G.Adj x y := by simpa using he
  have a2 : G.Adj x' y' := by simpa using he'
  obtain ⟨-, -, -, hx, hy⟩ := blk_shape (col := col) hG hlab hXW a1
  obtain ⟨-, -, -, hx', hy'⟩ := blk_shape (col := col) hG hlab hXW a2
  show Disjoint (triEdges (blk col apex s(x, y))) (triEdges (blk col apex s(x', y')))
  rw [triEdges_blk (col := col) hG hlab hXW a1, triEdges_blk (col := col) hG hlab hXW a2,
    Finset.disjoint_left]
  set w := apex (col s(x, y))
  set w' := apex (col s(x', y'))
  have hw : lab w = W := hlab _
  have hw' : lab w' = W := hlab _
  -- two edges at a common vertex with the same apex have the same colour
  have same : ∀ {v : V}, v ∈ s(x, y) → v ∈ s(x', y') → w = w' → False := by
    intro v hv hv' hww
    have hc : col s(x, y) = col s(x', y') := hapex hww
    have := hprop _ he _ he' hee hc
    exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 hv) (Sym2.mem_toFinset.2 hv')
  intro f hf hf'
  simp only [mem_insert, mem_singleton] at hf hf'
  have nXW : ∀ {a b c d : V}, lab a = X → lab b = X → lab c = X → lab d = W →
      s(a, b) ≠ s(c, d) := by
    intro a b c d ha hb hc hd e
    rcases Sym2.eq_iff.1 e with ⟨-, h⟩ | ⟨h, -⟩
    · exact hXW (by rw [← hb, h, hd])
    · exact hXW (by rw [← ha, h, hd])
  rcases hf with rfl | rfl | rfl <;> rcases hf' with e1 | e1 | e1
  · exact hee e1
  · exact nXW hx hy hx' hw' e1
  · exact nXW hx hy hy' hw' e1
  · exact nXW hx' hy' hx hw e1.symm
  · rcases Sym2.eq_iff.1 e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact same (v := x) (by simp) (by rw [h1]; simp) h2
    · exact hXW (by rw [← hx, h1, hw'])
  · rcases Sym2.eq_iff.1 e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact same (v := x) (by simp) (by rw [h1]; simp) h2
    · exact hXW (by rw [← hx, h1, hw'])
  · exact nXW hx' hy' hy hw e1.symm
  · rcases Sym2.eq_iff.1 e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact same (v := y) (by simp) (by rw [h1]; simp) h2
    · exact hXW (by rw [← hy, h1, hw'])
  · rcases Sym2.eq_iff.1 e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact same (v := y) (by simp) (by rw [h1]; simp) h2
    · exact hXW (by rw [← hy, h1, hw'])

end Blocks

/-! ### Leave neighbourhoods of the blocks -/

section Leave

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3} {X W : Fin 3}
  {G : SimpleGraph V} {p : ℕ} {col : Sym2 V → Fin p} {apex : Fin p → V}
  (hG : ∀ x y, G.Adj x y → lab x = X ∧ lab y = X)
  (hprop : ProperOn G.edgeFinset col) (hapex : Function.Injective apex)
  (hlab : ∀ i, lab (apex i) = W) (hXW : X ≠ W)

include hG hlab hXW in
theorem mem_leave {u v : V} :
    s(u, v) ∈ (blocks G col apex).biUnion triEdges ↔ ∃ x y, G.Adj x y ∧
      (s(u, v) = s(x, y) ∨ s(u, v) = s(x, apex (col s(x, y))) ∨
        s(u, v) = s(y, apex (col s(x, y)))) := by
  simp only [mem_biUnion, blocks, mem_image]
  constructor
  · rintro ⟨T, ⟨e, he, rfl⟩, hT⟩
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    rw [triEdges_blk (col := col) hG hlab hXW hxy] at hT
    simp only [mem_insert, mem_singleton] at hT
    exact ⟨x, y, hxy, hT⟩
  · rintro ⟨x, y, hxy, h⟩
    refine ⟨_, ⟨s(x, y), by simpa using hxy, rfl⟩, ?_⟩
    rw [triEdges_blk (col := col) hG hlab hXW hxy]
    simp only [mem_insert, mem_singleton]; exact h

include hG hlab hXW in
/-- Leave edges join `X` to `X` or `X` to `W`. -/
theorem leave_labels {u v : V} (h : s(u, v) ∈ (blocks G col apex).biUnion triEdges) :
    (lab u = X ∧ lab v = X) ∨ (lab u = X ∧ lab v = W) ∨ (lab u = W ∧ lab v = X) := by
  obtain ⟨x, y, hxy, h⟩ := (mem_leave hG hlab hXW).1 h
  obtain ⟨hx, hy⟩ := hG x y hxy
  have ha := hlab (col s(x, y))
  rcases h with e | e | e <;> rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inl ⟨hy, hx⟩
  · exact Or.inr (Or.inl ⟨hx, ha⟩)
  · exact Or.inr (Or.inr ⟨ha, hx⟩)
  · exact Or.inr (Or.inl ⟨hy, ha⟩)
  · exact Or.inr (Or.inr ⟨ha, hy⟩)

include hG hlab hXW in
/-- **`X`-neighbours of an `X`-vertex: its graph neighbours.** -/
theorem LN_XX {u : V} (hu : lab u = X) :
    LN lab (blocks G col apex) u X = univ.filter fun v => G.Adj u v := by
  ext v
  simp only [LN, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hv, h⟩
    obtain ⟨x, y, hxy, h⟩ := (mem_leave hG hlab hXW).1 h
    have ha := hlab (col s(x, y))
    rcases h with e | e | e
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm
    · rcases Sym2.eq_iff.1 e with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact absurd (hv.symm.trans ha) hXW
      · exact absurd (hu.symm.trans ha) hXW
    · rcases Sym2.eq_iff.1 e with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact absurd (hv.symm.trans ha) hXW
      · exact absurd (hu.symm.trans ha) hXW
  · intro h
    exact ⟨(hG u v h).2, (mem_leave hG hlab hXW).2 ⟨u, v, h, Or.inl rfl⟩⟩

include hG hlab hXW in
/-- **`W`-neighbours of an `X`-vertex: the apices of its edges.** -/
theorem LN_XW {u : V} (hu : lab u = X) :
    LN lab (blocks G col apex) u W =
      (G.edgeFinset.filter fun e => u ∈ e).image fun e => apex (col e) := by
  ext v
  simp only [LN, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨hv, h⟩
    obtain ⟨x, y, hxy, h⟩ := (mem_leave hG hlab hXW).1 h
    obtain ⟨hx, hy⟩ := hG x y hxy
    have ha := hlab (col s(x, y))
    rcases h with e | e | e
    · rcases Sym2.eq_iff.1 e with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact absurd (hv.symm.trans hy) (Ne.symm hXW)
      · exact absurd (hv.symm.trans hx) (Ne.symm hXW)
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · exact ⟨s(u, y), ⟨by simpa using hxy, by simp⟩, rfl⟩
      · exact absurd (hu.symm.trans ha) hXW
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · exact ⟨s(x, u), ⟨by simpa using hxy, by simp⟩, rfl⟩
      · exact absurd (hu.symm.trans ha) hXW
  · rintro ⟨e, ⟨he, hue⟩, rfl⟩
    refine ⟨hlab _, ?_⟩
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    rcases Sym2.mem_iff.1 hue with rfl | rfl
    · exact (mem_leave hG hlab hXW).2 ⟨u, y, hxy, Or.inr (Or.inl rfl)⟩
    · exact (mem_leave hG hlab hXW).2 ⟨x, u, hxy, Or.inr (Or.inr rfl)⟩

include hG hlab hXW hprop hapex in
theorem card_LN_XW {u : V} (hu : lab u = X) :
    #(LN lab (blocks G col apex) u W) = (G.neighborSet u).ncard := by
  rw [LN_XW hG hlab hXW hu, card_image_of_injOn]
  · rw [ncard_neighborSet, ← ncard_incidenceSet, ← Set.ncard_coe_finset]
    congr 1
    ext e
    simp [incidenceSet]
  · intro e he e' he' h
    simp only [coe_filter, Set.mem_setOf_eq] at he he'
    by_contra hne
    have hc : col e = col e' := hapex h
    exact Finset.disjoint_left.1 (hprop e he.1 e' he'.1 hne hc) (Sym2.mem_toFinset.2 he.2)
      (Sym2.mem_toFinset.2 he'.2)

include hG hlab hXW in
theorem card_LN_XX {u : V} (hu : lab u = X) :
    #(LN lab (blocks G col apex) u X) = (G.neighborSet u).ncard := by
  rw [LN_XX hG hlab hXW hu, ← Set.ncard_coe_finset]
  congr 1; ext v; simp

include hG hlab hXW hapex in
/-- **`X`-neighbours of an apex: the endpoints of its colour class.** -/
theorem LN_WX (i : Fin p) :
    LN lab (blocks G col apex) (apex i) X =
      (colourClass G.edgeFinset col i).biUnion Sym2.toFinset := by
  ext v
  constructor
  · intro hvm
    obtain ⟨-, hv, h⟩ := mem_filter.1 hvm
    obtain ⟨x, y, hxy, h⟩ := (mem_leave hG hlab hXW).1 h
    obtain ⟨hx, hy⟩ := hG x y hxy
    have hai := hlab i
    have he : s(x, y) ∈ G.edgeFinset := by simpa using hxy
    rcases h with e | e | e
    · rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (hai.symm.trans (by rw [h1]; exact hx)) (Ne.symm hXW)
      · exact absurd (hai.symm.trans (by rw [h1]; exact hy)) (Ne.symm hXW)
    · rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact absurd (hai.symm.trans (by rw [h1]; exact hx)) (Ne.symm hXW)
      · exact mem_biUnion.2 ⟨s(x, y), mem_colourClass.2 ⟨he, (hapex h1).symm⟩,
          Sym2.mem_toFinset.2 (by rw [h2]; simp)⟩
    · rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact absurd (hai.symm.trans (by rw [h1]; exact hy)) (Ne.symm hXW)
      · exact mem_biUnion.2 ⟨s(x, y), mem_colourClass.2 ⟨he, (hapex h1).symm⟩,
          Sym2.mem_toFinset.2 (by rw [h2]; simp)⟩
  · intro hvm
    obtain ⟨e, he, hve⟩ := mem_biUnion.1 hvm
    obtain ⟨he, hc⟩ := mem_colourClass.1 he
    rw [Sym2.mem_toFinset] at hve
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    obtain ⟨hx, hy⟩ := hG x y hxy
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · refine ⟨hx, (mem_leave hG hlab hXW).2 ⟨v, y, hxy, Or.inr (Or.inl ?_)⟩⟩
      rw [hc, Sym2.eq_swap]
    · refine ⟨hy, (mem_leave hG hlab hXW).2 ⟨x, v, hxy, Or.inr (Or.inr ?_)⟩⟩
      rw [hc, Sym2.eq_swap]

include hG hlab hXW hapex hprop in
theorem card_LN_WX (i : Fin p) :
    #(LN lab (blocks G col apex) (apex i) X) = 2 * #(colourClass G.edgeFinset col i) := by
  rw [LN_WX hG hapex hlab hXW, card_biUnion (colourClass_pairwiseDisjoint_toFinset hprop i)]
  rw [sum_congr rfl fun e he => Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet
    (mem_edgeFinset.1 (mem_colourClass.1 he).1)), sum_const, smul_eq_mul, mul_comm]

include hG hlab hXW in
theorem LN_other {u : V} {Y : Fin 3} (h : ¬ ((lab u = X ∧ Y = X) ∨ (lab u = X ∧ Y = W) ∨
    (lab u = W ∧ Y = X))) : LN lab (blocks G col apex) u Y = ∅ := by
  ext v
  simp only [LN, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
  intro hv hl
  rcases leave_labels hG hlab hXW hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h (Or.inl ⟨h1, hv ▸ h2⟩)
  · exact h (Or.inr (Or.inl ⟨h1, hv ▸ h2⟩))
  · exact h (Or.inr (Or.inr ⟨h1, hv ▸ h2⟩))

end Leave

/-! ### One part of the planted structure -/

set_option maxHeartbeats 800000 in
/-- **The blocks `XX(X+2)` of one class**, with prescribed leave degrees. -/
theorem exists_part {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin 3) {X W : Fin 3}
    (hXW : X ≠ W) {sX sW dX rX qW rW : ℕ} [NeZero sX] [NeZero sW]
    (fX : ZMod sX ↪ V) (hfX : ∀ z, lab (fX z) = X)
    (fW : ZMod sW ↪ V) (hfW : ∀ z, lab (fW z) = W)
    (hG : 4 * dX + 64 ≤ sX) (hrX : rX < sX) (hodd : dX % 2 = 1 → sX % 2 = 0)
    (hex : ¬ (dX = 0 ∧ (rX = 1 ∨ rX = 2))) (hpal : dX + 3 ≤ sW) (hrW : rW < sW)
    (hE : sX * dX + 2 * rX = 2 * (sW * qW + rW)) :
    ∃ P : Finset (Finset V),
      (∀ T ∈ P, ∃ u u' w, T = {u, u', w} ∧ u ≠ u' ∧ lab u = X ∧ lab u' = X ∧ lab w = W) ∧
      (P : Set (Finset V)).PairwiseDisjoint triEdges ∧ #P = sW * qW + rW ∧
      (∀ z, #(LN lab P (fX z) X) = dX + (if z.val < rX then 2 else 0)) ∧
      (∀ z, #(LN lab P (fX z) W) = dX + (if z.val < rX then 2 else 0)) ∧
      (∀ z, #(LN lab P (fW z) X) = 2 * (qW + if z.val < rW then 1 else 0)) ∧
      (∀ u Y, ¬ ((lab u = X ∧ Y = X) ∨ (lab u = X ∧ Y = W) ∨ (lab u = W ∧ Y = X)) →
        LN lab P u Y = ∅) := by
  obtain ⟨G0, hG0⟩ := exists_graph (s := sX) hG hrX hodd hex
  obtain ⟨GX, hGX⟩ : ∃ G : SimpleGraph V, G = G0.map fX := ⟨_, rfl⟩
  have hadjX : ∀ x y, GX.Adj x y → lab x = X ∧ lab y = X := by
    intro x y h
    rw [hGX, map_adj] at h
    obtain ⟨z, z', -, rfl, rfl⟩ := h
    exact ⟨hfX z, hfX z'⟩
  have hdegX : ∀ v, (GX.neighborSet v).ncard ≤ dX + 2 := by
    intro v
    by_cases hv : ∃ z, fX z = v
    · obtain ⟨z, rfl⟩ := hv
      rw [hGX, map_neighborSet_emb, hG0]; split_ifs <;> omega
    · push Not at hv
      rw [hGX, map_neighborSet_out fX G0 hv, Set.ncard_empty]; omega
  have hmax : GX.maxDegree + 1 ≤ sW := by
    have : GX.maxDegree ≤ dX + 2 :=
      maxDegree_le_of_forall_degree_le GX (dX + 2) fun v => by
        rw [← ncard_neighborSet]; exact hdegX v
    omega
  obtain ⟨col, hprop, heq⟩ := exists_equitable_proper GX (NeZero.pos sW) hmax
  obtain ⟨f, hf⟩ : ∃ f : Fin sW → ℕ, f = fun i => #(colourClass GX.edgeFinset col i) :=
    ⟨_, rfl⟩
  have hsum : ∑ i, f i = sW * qW + rW := by
    rw [hf, sum_card_colourClass_univ]
    have h2 := sum_degrees_eq_twice_card_edges GX
    have h3 : ∑ v, GX.degree v = sX * dX + 2 * rX := by
      rw [show (∑ v, GX.degree v) = ∑ v, (GX.neighborSet v).ncard from
        sum_congr rfl fun v _ => (ncard_neighborSet GX v).symm]
      rw [hGX, sum_ncard_map fX G0 _ hG0, sum_add_distrib, sum_const, card_univ, ZMod.card,
        smul_eq_mul]
      congr 1
      rw [← sum_filter, sum_const, card_zmod_lt hrX, smul_eq_mul, mul_comm]
    omega
  obtain ⟨hvals, hcnt⟩ := equitable_sizes hrW f (fun i j => by rw [hf]; exact heq i j) hsum
  obtain ⟨σ, hσ⟩ := exists_sizes_equiv_zmod hrW f hvals hcnt
  obtain ⟨apex, hapexd⟩ : ∃ apex : Fin sW → V, apex = fun i => fW (σ i) := ⟨_, rfl⟩
  have hapex : Function.Injective apex := fun i j h => by
    rw [hapexd] at h; exact σ.injective (fW.injective h)
  have hlab : ∀ i, lab (apex i) = W := fun i => by rw [hapexd]; exact hfW _
  refine ⟨blocks GX col apex, fun T hT => blocks_shape hadjX hlab hXW hT,
    blocks_disjoint hadjX hprop hapex hlab hXW, ?_, fun z => ?_, fun z => ?_, fun z => ?_,
    fun u Y h => LN_other hadjX hlab hXW h⟩
  · rw [card_blocks hadjX hlab hXW, ← sum_card_colourClass_univ (colour := col)]
    rw [hf] at hsum; exact hsum
  · rw [card_LN_XX hadjX hlab hXW (hfX z), hGX, map_neighborSet_emb, hG0]
  · rw [card_LN_XW hadjX hprop hapex hlab hXW (hfX z), hGX, map_neighborSet_emb, hG0]
  · have hz : fW z = apex (σ.symm z) := by simp [hapexd]
    rw [hz, card_LN_WX hadjX hprop hapex hlab hXW]
    have := hσ (σ.symm z)
    simp only [hf, Equiv.apply_symm_apply] at this
    rw [this]

end CDRBicolour.Absorption.Corners
