/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Transfer to a support

The external theorems (Cao–Chen–Jing–Shan, Plantholt) are stated for graphs of a given order.
In L183 they are applied to graphs living on a vertex subset `U` (the support of a critical
subgraph, and `C - w`).  `restrict G U` is `G` seen on the type `↥U`; when every edge of `G`
lies inside `U` (`Supported G U`) degrees, maximum degree, edge count and edge-colourability are
transferred exactly.  This lets us use the literal statements.
-/

@[expose] public section

namespace CDRBicolour

open Finset LeanPool.Vizing.ColourClasses

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `G` on the vertex subset `U`. -/
def restrict (G : SimpleGraph W) (U : Finset W) : SimpleGraph {x // x ∈ U} :=
  G.comap Subtype.val

instance (G : SimpleGraph W) [DecidableRel G.Adj] (U : Finset W) :
    DecidableRel (restrict G U).Adj := fun x y => inferInstanceAs (Decidable (G.Adj x.1 y.1))

/-- Every edge of `G` lies inside `U`. -/
def Supported (G : SimpleGraph W) (U : Finset W) : Prop := ∀ x y, G.Adj x y → x ∈ U

variable {G : SimpleGraph W} [DecidableRel G.Adj] {U : Finset W}

theorem degree_eq_zero_of_not_mem (hU : Supported G U) {v : W} (hv : v ∉ U) :
    G.degree v = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_zero]
  ext y
  simp only [SimpleGraph.mem_neighborFinset, notMem_empty, iff_false]
  exact fun h => hv (hU v y h)

theorem degree_restrict (hU : Supported G U) (x : {x // x ∈ U}) :
    (restrict G U).degree x = G.degree x.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    ← card_map (Function.Embedding.subtype _)]
  congr 1
  ext v
  simp only [mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro h; exact ⟨⟨v, hU v x.1 h.symm⟩, h, rfl⟩

theorem maxDegree_restrict (hU : Supported G U) :
    (restrict G U).maxDegree = G.maxDegree := by
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro x; rw [degree_restrict hU]; exact G.degree_le_maxDegree _
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro v
    by_cases hv : v ∈ U
    · rw [← degree_restrict hU ⟨v, hv⟩]; exact SimpleGraph.degree_le_maxDegree _ _
    · rw [degree_eq_zero_of_not_mem hU hv]; exact Nat.zero_le _

theorem card_edgeFinset_restrict (hU : Supported G U) :
    (restrict G U).edgeFinset.card = G.edgeFinset.card := by
  have h1 := (restrict G U).sum_degrees_eq_twice_card_edges
  have h2 := G.sum_degrees_eq_twice_card_edges
  have h3 : ∑ x : {x // x ∈ U}, (restrict G U).degree x = ∑ v, G.degree v := by
    rw [show (∑ x : {x // x ∈ U}, (restrict G U).degree x) = ∑ x : {x // x ∈ U}, G.degree x.1
      from Fintype.sum_congr _ _ (degree_restrict hU)]
    rw [Finset.sum_coe_sort U (fun v => G.degree v)]
    exact Finset.sum_subset (subset_univ U) fun v _ hv => degree_eq_zero_of_not_mem hU hv
  omega

/-- A literal proper colouring gives an edge colouring. -/
theorem edgeColourable_of_properOn {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {k : ℕ} (colour : Sym2 V → Fin k)
    (hproper : ProperOn H.edgeFinset colour) : EdgeColourable H k := by
  refine ⟨SimpleGraph.Coloring.mk (fun e => colour e.1) ?_⟩
  intro e f hadj hsame
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, v, hve, hvf⟩ := hadj
  have he : e.1 ∈ H.edgeFinset := (SimpleGraph.mem_edgeFinset).2 e.2
  have hf : f.1 ∈ H.edgeFinset := (SimpleGraph.mem_edgeFinset).2 f.2
  have hd := hproper e.1 he f.1 hf (fun h => hne (Subtype.ext h)) hsame
  exact Finset.disjoint_left.1 hd (Sym2.mem_toFinset.2 hve) (Sym2.mem_toFinset.2 hvf)

/-- The inclusion `↥U → W` as a graph homomorphism. -/
def restrictHom (G : SimpleGraph W) (U : Finset W) : restrict G U →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

/-- `G` colourable ⇒ `restrict G U` colourable. -/
theorem edgeColourable_restrict_of_edgeColourable {k : ℕ} (h : EdgeColourable G k) :
    EdgeColourable (restrict G U) k := by
  obtain ⟨C⟩ := h
  let f : (restrict G U).lineGraph →g G.lineGraph :=
    { toFun := (restrictHom G U).mapEdgeSet
      map_rel' := by
        intro e₁ e₂ hadj
        rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj ⊢
        obtain ⟨hne, v, h1, h2⟩ := hadj
        refine ⟨fun h => hne ?_, v.1, ?_, ?_⟩
        · exact SimpleGraph.Hom.mapEdgeSet.injective (restrictHom G U) Subtype.val_injective h
        · exact Sym2.mem_map.2 ⟨v, h1, rfl⟩
        · exact Sym2.mem_map.2 ⟨v, h2, rfl⟩ }
  exact ⟨C.comap f⟩

/-- `restrict G U` colourable ⇒ `G` colourable, when `G` is supported on `U`. -/
theorem edgeColourable_of_edgeColourable_restrict (hU : Supported G U) {k : ℕ}
    (h : EdgeColourable (restrict G U) k) : EdgeColourable G k := by
  -- a graph without edges is colourable with any palette
  have hnoedge : (∀ x y, ¬ G.Adj x y) → EdgeColourable G k := by
    intro hno
    haveI : IsEmpty G.edgeSet := ⟨fun e => by
      obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | _ x y => exact hno x y he⟩
    exact ⟨SimpleGraph.Coloring.ofIsEmpty⟩
  rcases U.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
  · exact hnoedge fun x y hxy => notMem_empty x (hU x y hxy)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨C⟩ := h
    exact hnoedge fun x y hxy =>
      (C ⟨s(⟨x, hU x y hxy⟩, ⟨y, hU y x hxy.symm⟩), hxy⟩).elim0
  obtain ⟨colour, hproper⟩ := exists_properOn_of_edgeColourable (restrict G U) hk h
  let pull : W → {x // x ∈ U} := fun x => if hx : x ∈ U then ⟨x, hx⟩ else ⟨u₀, hu₀⟩
  have hpull : ∀ x (hx : x ∈ U), pull x = ⟨x, hx⟩ := fun x hx => by simp [pull, hx]
  refine edgeColourable_of_properOn (fun e => colour (e.map pull)) ?_
  intro e he f hf hne hsame
  induction e using Sym2.ind with
  | _ x y =>
  induction f using Sym2.ind with
  | _ x' y' =>
    have hxy : G.Adj x y := (SimpleGraph.mem_edgeFinset).1 he
    have hxy' : G.Adj x' y' := (SimpleGraph.mem_edgeFinset).1 hf
    have hx := hU x y hxy
    have hy := hU y x hxy.symm
    have hx' := hU x' y' hxy'
    have hy' := hU y' x' hxy'.symm
    simp only [Sym2.map_mk, hpull x hx, hpull y hy, hpull x' hx', hpull y' hy'] at hsame
    have hE : s((⟨x, hx⟩ : {x // x ∈ U}), ⟨y, hy⟩) ∈ (restrict G U).edgeFinset :=
      (SimpleGraph.mem_edgeFinset).2 hxy
    have hF : s((⟨x', hx'⟩ : {x // x ∈ U}), ⟨y', hy'⟩) ∈ (restrict G U).edgeFinset :=
      (SimpleGraph.mem_edgeFinset).2 hxy'
    have hne' : s((⟨x, hx⟩ : {x // x ∈ U}), ⟨y, hy⟩) ≠ s(⟨x', hx'⟩, ⟨y', hy'⟩) := by
      intro h
      apply hne
      have := congrArg (Sym2.map Subtype.val) h
      simpa using this
    have hd := hproper _ hE _ hF hne' hsame
    rw [Finset.disjoint_left] at hd ⊢
    intro v hv hv'
    rw [Sym2.mem_toFinset, Sym2.mem_iff] at hv hv'
    have hvU : v ∈ U := by rcases hv with rfl | rfl <;> assumption
    apply hd (a := ⟨v, hvU⟩)
    · rw [Sym2.mem_toFinset, Sym2.mem_iff]
      rcases hv with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [Sym2.mem_toFinset, Sym2.mem_iff]
      rcases hv' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

end CDRBicolour
