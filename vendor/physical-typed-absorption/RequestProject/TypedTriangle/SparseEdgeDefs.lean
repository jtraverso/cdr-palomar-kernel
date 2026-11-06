/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Borrado disperso de aristas: definiciones del contrato y lemas básicos (V9)

Definiciones de `Defs.lean`/`Lattice.lean`/`RobustHinge.lean` reescritas con el host
desplegado en `(G, lab)` (mismos cuerpos; coinciden por definición con
`TypedTriangle.lattice ⟨G, lab⟩ F`, etc.), la diferencia de dos triángulos mediante una
bisagra (`hinge_diff_mem`) y la pertenencia de las raíces al soporte de una bisagra.
El resultado principal está en `SparseEdgeLattice.lean`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.SparseEdge

variable {V I : Type*} [Fintype V]

/-! ### Definiciones del contrato, con el host desplegado en `(G, lab)` -/

/-- `E(T)`: las aristas (pares no diagonales) de un conjunto de vértices `T`. -/
def triEdges (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

/-- Las aristas del grafo como `Finset`. -/
def edges (G : SimpleGraph V) : Finset (Sym2 V) := univ.filter (fun e => e ∈ G.edgeSet)

/-- Triángulo permitido (igual a `TypedTriangle.IsAllowed ⟨G, lab⟩`). -/
def IsAllowed (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (T : Finset V) :
    Prop :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y) ∧ T.val.map lab ∈ F

/-- (D1) Descomposición permitida de `J`. -/
def IsDecomposition (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (J : Finset (Sym2 V)) (D : Finset (Finset V)) : Prop :=
  (∀ T ∈ D, IsAllowed G lab F T) ∧ (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
    D.biUnion triEdges = J

/-- Indicador entero. -/
def ind (J : Finset (Sym2 V)) : Sym2 V → ℤ := fun e => if e ∈ J then 1 else 0

/-- (D2) Retículo físico. -/
def lattice (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) :
    Submodule ℤ (Sym2 V → ℤ) :=
  Submodule.span ℤ ((fun T => ind (triEdges T)) '' {T | IsAllowed G lab F T})

/-- (D4) Vecinos comunes con etiqueta `k`. -/
def commonNbrs (G : SimpleGraph V) (lab : V → I) (k : I) (u v : V) : Finset V :=
  univ.filter (fun w => G.Adj u w ∧ G.Adj v w ∧ lab w = k)

/-- (D5) = (H3). -/
def CommonNbrCond (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (α : ℝ) : Prop :=
  ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
    α * Fintype.card V ≤ (commonNbrs G lab k u v).card

/-- Soporte de un conjunto de aristas. -/
def support (J : Finset (Sym2 V)) : Finset V := univ.filter (fun x => ∃ e ∈ J, x ∈ e)

/-- (D6) Cuña `{ua, va}`. -/
def wedge (u v a : V) : Finset (Sym2 V) := {s(u, a), s(v, a)}

/-- Bisagra física. -/
def IsHinge (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a b : V)
    (J : Finset (Sym2 V)) : Prop :=
  J ⊆ edges G ∧ Disjoint J (triEdges {u, v, a} ∪ triEdges {u, v, b}) ∧
    (∃ D, IsDecomposition G lab F (J ∪ wedge u v a) D) ∧
    (∃ D, IsDecomposition G lab F (J ∪ wedge u v b) D)

/-- Bisagras de orden exactamente `i`. -/
def hinges (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a b : V) (i : ℕ) :
    Finset (Finset (Sym2 V)) :=
  univ.filter (fun J => IsHinge G lab F u v a b J ∧ (support J).card = i)

/-- (D7) = (H4). -/
def HingeCond (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ) :
    Prop :=
  ∀ u v a b : V, a ≠ b → IsAllowed G lab F {u, v, a} → IsAllowed G lab F {u, v, b} →
    ∃ i, 6 ≤ i ∧ i ≤ h ∧
      α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges G lab F u v a b i).card

/-- Grafo de `subHost H J` (`Lattice.lean`): `fromEdgeSet J ⊓ G`. -/
def subGraph (G : SimpleGraph V) (J : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (J : Set (Sym2 V)) ⊓ G

/-- Grado de `x` en el conjunto de aristas `B` (`RobustHinge.lean`). -/
def degIn (B : Finset (Sym2 V)) (x : V) : ℕ := (B.filter (fun e => x ∈ e)).card

/-- Vecinos de `x` en `B` (`RobustHinge.lean`). -/
def nbrIn (B : Finset (Sym2 V)) (x : V) : Finset V := univ.filter (fun z => s(x, z) ∈ B)

omit [Fintype V] in
/-- Vectores con coordenada cero en cada arista de `B`. -/
def zeroOn (B : Finset (Sym2 V)) : Submodule ℤ (Sym2 V → ℤ) where
  carrier := {x | ∀ e ∈ B, x e = 0}
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  zero_mem' := by intro e _; rfl
  smul_mem' := by
    intro c x hx e he
    simp [hx e he]

omit [Fintype V] in
/-- Vectores soportados en `K` (cero fuera de `K`): el "ℤ^(E(G−B))" de (1.1). -/
def supportedOn (K : Finset (Sym2 V)) : Submodule ℤ (Sym2 V → ℤ) where
  carrier := {x | ∀ e, e ∉ K → x e = 0}
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  zero_mem' := by intro e _; rfl
  smul_mem' := by
    intro c x hx e he
    simp [hx e he]

/-! ### Lemas básicos -/

omit [Fintype V] in
lemma mem_triEdges {T : Finset V} {x y : V} :
    s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T ∧ x ≠ y := by
  simp [triEdges, and_assoc]

omit [Fintype V] in
lemma not_isDiag_of_mem_triEdges {T : Finset V} {e : Sym2 V} (he : e ∈ triEdges T) :
    ¬ e.IsDiag := (Finset.mem_filter.1 he).2

omit [Fintype V] in
lemma mem_of_mem_triEdges {T : Finset V} {e : Sym2 V} (he : e ∈ triEdges T) {p : V}
    (hp : p ∈ e) : p ∈ T :=
  Finset.mem_sym2_iff.1 (Finset.mem_filter.1 he).1 p hp

lemma mem_edges {G : SimpleGraph V} {e : Sym2 V} : e ∈ edges G ↔ e ∈ G.edgeSet := by
  simp [edges]

lemma not_isDiag_of_mem_edges {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ edges G) :
    ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet (mem_edges.1 he)

lemma mem_edges_subGraph {G : SimpleGraph V} {K : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ edges (subGraph G K) ↔ e ∈ K ∧ e ∈ edges G := by
  simp only [mem_edges, subGraph, SimpleGraph.edgeSet_inf, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_inter_iff, Set.mem_diff, Finset.mem_coe]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, G.not_isDiag_of_mem_edgeSet h2⟩, h2⟩

omit [Fintype V] in
lemma ind_apply (J : Finset (Sym2 V)) (e : Sym2 V) : ind J e = if e ∈ J then 1 else 0 := rfl

omit [Fintype V] in
lemma ind_union_of_disjoint {J K : Finset (Sym2 V)} (h : Disjoint J K) :
    ind (J ∪ K) = ind J + ind K := by
  funext e
  simp only [ind, Finset.mem_union, Pi.add_apply]
  by_cases hJ : e ∈ J
  · have hK : e ∉ K := Finset.disjoint_left.1 h hJ
    simp [hJ, hK]
  · by_cases hK : e ∈ K <;> simp [hJ, hK]

omit [Fintype V] in
lemma ind_biUnion {D : Finset (Finset V)} (hD : (D : Set (Finset V)).PairwiseDisjoint triEdges) :
    ind (D.biUnion triEdges) = ∑ T ∈ D, ind (triEdges T) := by
  induction D using Finset.induction_on with
  | empty => funext e; simp [ind]
  | insert T D hT ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hT]
    have hD' : (D : Set (Finset V)).PairwiseDisjoint triEdges :=
      hD.subset (by simp)
    rw [ind_union_of_disjoint, ih hD']
    rw [Finset.disjoint_biUnion_right]
    intro T' hT'
    exact hD (by simp) (by simp [hT']) (fun h => hT (h ▸ hT'))

omit [Fintype V] in
/-- Triángulo tras extraer dos vértices distintos: hay un tercero. -/
lemma exists_third {T : Finset V} (hT : T.card = 3) (p q : V) :
    ∃ x ∈ T, x ≠ p ∧ x ≠ q := by
  by_contra hcon
  push_neg at hcon
  have hsub : T ⊆ {p, q} := by
    intro x hx
    by_cases hxp : x = p
    · simp [hxp]
    · simp [hcon x hx hxp]
  have := Finset.card_le_card hsub
  have h2 : ({p, q} : Finset V).card ≤ 2 := Finset.card_le_two
  omega

omit [Fintype V] in
lemma card_three_of_distinct {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    ({u, v, a} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [huv, hua]),
    Finset.card_insert_of_notMem (by simp [hva]), Finset.card_singleton]

omit [Fintype V] in
lemma distinct_of_card_three {u v a : V} (h : ({u, v, a} : Finset V).card = 3) :
    u ≠ v ∧ u ≠ a ∧ v ≠ a := by
  have h2 : ∀ p q : V, ({p, q} : Finset V).card ≤ 2 := fun p q => Finset.card_le_two
  refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩ <;> subst heq
  · have : ({u, u, a} : Finset V) ⊆ {u, a} := by intro x; simp
    have := Finset.card_le_card this; have := h2 u a; omega
  · have : ({u, v, u} : Finset V) ⊆ {u, v} := by intro x; simp; tauto
    have := Finset.card_le_card this; have := h2 u v; omega
  · have : ({u, v, v} : Finset V) ⊆ {u, v} := by intro x; simp
    have := Finset.card_le_card this; have := h2 u v; omega

omit [Fintype V] in
/-- Un triángulo que contiene `u ≠ v` es `{u, v, a}`. -/
lemma eq_triple_of_mem {T : Finset V} (hT : T.card = 3) {u v : V} (hu : u ∈ T) (hv : v ∈ T)
    (huv : u ≠ v) : ∃ a, a ≠ u ∧ a ≠ v ∧ T = {u, v, a} := by
  obtain ⟨a, ha, hau, hav⟩ := exists_third hT u v
  refine ⟨a, hau, hav, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [hT, card_three_of_distinct huv (Ne.symm hau) (Ne.symm hav)]

omit [Fintype V] in
lemma triEdges_triple {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    triEdges ({u, v, a} : Finset V) = insert s(u, v) (wedge u v a) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
  rw [mem_triEdges]
  simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
  · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
      simp_all [eq_comm]

omit [Fintype V] in
lemma not_mem_wedge_uv {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    s(u, v) ∉ wedge u v a := by
  simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  tauto

/-! ### Triángulos permitidos en subgrafos y monotonía del retículo -/

/-- Las aristas de un triángulo permitido son aristas del grafo. -/
lemma triEdges_subset_edges {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} (hT : IsAllowed G lab F T) : triEdges T ⊆ edges G := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
  obtain ⟨hx, hy, hxy⟩ := mem_triEdges.1 he
  exact mem_edges.2 (hT.2.1 x hx y hy hxy)

/-- Un triángulo permitido en `G` cuyas aristas están en `G'` es permitido en `G'`. -/
lemma isAllowed_of_triEdges_subset {G G' : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {T : Finset V} (hT : IsAllowed G lab F T)
    (hsub : triEdges T ⊆ edges G') : IsAllowed G' lab F T := by
  refine ⟨hT.1, fun x hx y hy hxy => ?_, hT.2.2⟩
  have := hsub (mem_triEdges.2 ⟨hx, hy, hxy⟩)
  exact mem_edges.1 this

omit [Fintype V] in
lemma isAllowed_mono {G G' : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (hG : G ≤ G') {T : Finset V} (hT : IsAllowed G lab F T) : IsAllowed G' lab F T :=
  ⟨hT.1, fun x hx y hy hxy => hG (hT.2.1 x hx y hy hxy), hT.2.2⟩

omit [Fintype V] in
lemma subGraph_le (G : SimpleGraph V) (K : Finset (Sym2 V)) : subGraph G K ≤ G :=
  inf_le_right

/-- Permitido en `H − (E∖K)` ⟺ permitido en `H` con aristas en `K`. -/
lemma isAllowed_subGraph_iff {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {K : Finset (Sym2 V)} {T : Finset V} :
    IsAllowed (subGraph G K) lab F T ↔ IsAllowed G lab F T ∧ triEdges T ⊆ K := by
  constructor
  · intro hT
    refine ⟨isAllowed_mono (subGraph_le G K) hT, fun e he => ?_⟩
    exact (mem_edges_subGraph.1 (triEdges_subset_edges hT he)).1
  · rintro ⟨hT, hK⟩
    refine isAllowed_of_triEdges_subset hT fun e he => ?_
    exact mem_edges_subGraph.2 ⟨hK he, triEdges_subset_edges hT he⟩

omit [Fintype V] in
lemma ind_mem_lattice {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} (hT : IsAllowed G lab F T) : ind (triEdges T) ∈ lattice G lab F :=
  Submodule.subset_span ⟨T, hT, rfl⟩

omit [Fintype V] in
lemma lattice_mono {G G' : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (hG : G ≤ G') : lattice G lab F ≤ lattice G' lab F := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, rfl⟩
  exact ind_mem_lattice (isAllowed_mono hG hT)

/-- `H − ∅ = H` a nivel de retículo. -/
lemma lattice_subGraph_edges (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) :
    lattice (subGraph G (edges G)) lab F = lattice G lab F := by
  refine le_antisymm (lattice_mono (subGraph_le _ _)) ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, rfl⟩
  exact ind_mem_lattice (isAllowed_subGraph_iff.2 ⟨hT, triEdges_subset_edges hT⟩)

/-- Los vectores del retículo se anulan fuera de las aristas del grafo. -/
lemma lattice_le_supportedOn (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) :
    lattice G lab F ≤ supportedOn (edges G) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, rfl⟩
  intro e he
  have : e ∉ triEdges T := fun h => he (triEdges_subset_edges hT h)
  simp [ind, this]

/-- **Equivalencia de soporte ambiente.** Dentro de `Λ_H`, anularse en `B` equivale a estar
soportado en `E(H) ∖ B`. -/
theorem lattice_inf_zeroOn_eq_inf_supportedOn (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I)) (B : Finset (Sym2 V)) :
    lattice G lab F ⊓ zeroOn B = lattice G lab F ⊓ supportedOn (edges G \ B) := by
  ext x
  simp only [Submodule.mem_inf]
  constructor
  · rintro ⟨hx, hB⟩
    refine ⟨hx, fun e he => ?_⟩
    by_cases heB : e ∈ B
    · exact hB e heB
    · exact lattice_le_supportedOn G lab F hx e (fun h => he (Finset.mem_sdiff.2 ⟨h, heB⟩))
  · rintro ⟨hx, hs⟩
    exact ⟨hx, fun e he => hs e (fun h => (Finset.mem_sdiff.1 h).2 he)⟩

/-- Inclusión fácil de (1.1): `Λ_(H−B) ≤ Λ_H ∩ {x|_B = 0}`. -/
lemma lattice_sdiff_le (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (B : Finset (Sym2 V)) :
    lattice (subGraph G (edges G \ B)) lab F ≤ lattice G lab F ⊓ zeroOn B := by
  refine le_inf (lattice_mono (subGraph_le _ _)) (Submodule.span_le.2 ?_)
  rintro _ ⟨T, hT, rfl⟩
  intro e he
  have : e ∉ triEdges T := fun h =>
    (Finset.mem_sdiff.1 ((isAllowed_subGraph_iff.1 hT).2 h)).2 he
  simp [ind, this]

/-! ### Diferencia de dos triángulos mediante una bisagra -/

/-- **Diferencia por bisagra.** Si `J` es bisagra de `H` para `(uva, uvb)` y `J`, `W_a`, `W_b`
son aristas de `G'` (mismas etiquetas), entonces `χ_(uva) − χ_(uvb) ∈ Λ_(G')`. -/
theorem hinge_diff_mem {G G' : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v a b : V} {J : Finset (Sym2 V)} (hJ : IsHinge G lab F u v a b J)
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b)
    (hJG' : J ⊆ edges G') (haG' : wedge u v a ⊆ edges G') (hbG' : wedge u v b ⊆ edges G') :
    ind (triEdges {u, v, a}) - ind (triEdges {u, v, b}) ∈ lattice G' lab F := by
  have hdec : ∀ c, (wedge u v c ⊆ edges G') → (∃ D, IsDecomposition G lab F (J ∪ wedge u v c) D) →
      ind (J ∪ wedge u v c) ∈ lattice G' lab F := by
    rintro c hc ⟨D, hDall, hDdisj, hDeq⟩
    rw [← hDeq, ind_biUnion hDdisj]
    refine Submodule.sum_mem _ fun T hT => ind_mem_lattice ?_
    refine isAllowed_of_triEdges_subset (hDall T hT) fun e he => ?_
    have : e ∈ J ∪ wedge u v c := hDeq ▸ Finset.mem_biUnion.2 ⟨T, hT, he⟩
    rcases Finset.mem_union.1 this with h | h
    exacts [hJG' h, hc h]
  have hA := hdec a haG' hJ.2.2.1
  have hB := hdec b hbG' hJ.2.2.2
  have hJa : Disjoint J (wedge u v a) := by
    refine hJ.2.1.mono_right ?_
    rw [triEdges_triple huv hua hva]
    exact (Finset.subset_insert _ _).trans Finset.subset_union_left
  have hJb : Disjoint J (wedge u v b) := by
    refine hJ.2.1.mono_right ?_
    rw [triEdges_triple huv hub hvb]
    exact (Finset.subset_insert _ _).trans Finset.subset_union_right
  have key : ind (triEdges {u, v, a}) - ind (triEdges {u, v, b}) =
      ind (J ∪ wedge u v a) - ind (J ∪ wedge u v b) := by
    rw [triEdges_triple huv hua hva, triEdges_triple huv hub hvb,
      ind_union_of_disjoint hJa, ind_union_of_disjoint hJb,
      Finset.insert_eq, Finset.insert_eq,
      ind_union_of_disjoint (Finset.disjoint_singleton_left.2 (not_mem_wedge_uv huv hua hva)),
      ind_union_of_disjoint (Finset.disjoint_singleton_left.2 (not_mem_wedge_uv huv hub hvb))]
    abel
  rw [key]
  exact Submodule.sub_mem _ hA hB

/-! ### Las raíces están en el soporte de una bisagra -/

lemma mem_support_of_mem {J : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ J) {x : V}
    (hx : x ∈ e) : x ∈ support J := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, hx⟩

/-- En una descomposición de `J ∪ W_c`, con `J` disjunta de `E(uvc)`, los vértices
`u`, `v`, `c` tocan `J`. -/
lemma roots_mem_support_of_dec {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v c : V} {J : Finset (Sym2 V)} (huv : u ≠ v) (huc : u ≠ c) (hvc : v ≠ c)
    (hJc : Disjoint J (triEdges {u, v, c}))
    (hD : ∃ D, IsDecomposition G lab F (J ∪ wedge u v c) D) :
    u ∈ support J ∧ v ∈ support J ∧ c ∈ support J := by
  obtain ⟨D, hDall, -, hDeq⟩ := hD
  have huvJ : s(u, v) ∉ J := fun h =>
    Finset.disjoint_left.1 hJc h (mem_triEdges.2 ⟨by simp, by simp, huv⟩)
  have huvW := not_mem_wedge_uv huv huc hvc
  -- triángulo de `D` que cubre la arista `p c` de la cuña (`p = u` o `p = v`)
  have cover : ∀ p q, (p = u ∧ q = v ∨ p = v ∧ q = u) →
      p ∈ support J ∧ c ∈ support J := by
    rintro p q hpq
    have hpc : s(p, c) ∈ J ∪ wedge u v c := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [wedge]
    have hpqne : p ≠ q := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    have hpcne : p ≠ c := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    have hqcne : q ≠ c := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    have hpqJW : s(p, q) ∉ J ∪ wedge u v c := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [Finset.mem_union, not_or]; exact ⟨huvJ, huvW⟩
      · rw [Sym2.eq_swap]; simp only [Finset.mem_union, not_or]; exact ⟨huvJ, huvW⟩
    rw [← hDeq] at hpc
    obtain ⟨T, hTD, hpcT⟩ := Finset.mem_biUnion.1 hpc
    have hT := hDall T hTD
    have hpT := mem_of_mem_triEdges hpcT (by simp : p ∈ s(p, c))
    have hcT := mem_of_mem_triEdges hpcT (by simp : c ∈ s(p, c))
    obtain ⟨x, hxT, hxp, hxc⟩ := exists_third hT.1 p c
    have hsub : ∀ y z, y ∈ T → z ∈ T → y ≠ z → s(y, z) ∈ J ∪ wedge u v c := by
      intro y z hy hz hyz
      rw [← hDeq]
      exact Finset.mem_biUnion.2 ⟨T, hTD, mem_triEdges.2 ⟨hy, hz, hyz⟩⟩
    have hxq : x ≠ q := by
      rintro rfl
      exact hpqJW (hsub p x hpT hxT (Ne.symm hxp))
    -- `p x ∈ J`
    have hpx := hsub p x hpT hxT (Ne.symm hxp)
    have hcx := hsub c x hcT hxT (Ne.symm hxc)
    have hW : ∀ y, y ≠ c → y ≠ p → y ≠ q → ∀ w, (w = p ∨ w = c) → w ≠ y →
        s(w, y) ∉ wedge u v c := by
      intro y hyc hyp hyq w hw hwy
      simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw with rfl | rfl <;> tauto
    have hpxJ : s(p, x) ∈ J := by
      rcases Finset.mem_union.1 hpx with h | h
      · exact h
      · exact absurd h (hW x hxc hxp hxq p (Or.inl rfl) (Ne.symm hxp))
    have hcxJ : s(c, x) ∈ J := by
      rcases Finset.mem_union.1 hcx with h | h
      · exact h
      · exact absurd h (hW x hxc hxp hxq c (Or.inr rfl) (Ne.symm hxc))
    exact ⟨mem_support_of_mem hpxJ (by simp), mem_support_of_mem hcxJ (by simp)⟩
  obtain ⟨hu, hc⟩ := cover u v (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨hv, -⟩ := cover v u (Or.inr ⟨rfl, rfl⟩)
  exact ⟨hu, hv, hc⟩

/-- Las cuatro raíces de una bisagra están en su soporte. -/
lemma IsHinge.roots_subset_support {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v a b : V} {J : Finset (Sym2 V)} (hJ : IsHinge G lab F u v a b J)
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b) :
    ({u, v, a, b} : Finset V) ⊆ support J := by
  have h1 := roots_mem_support_of_dec huv hua hva
    (hJ.2.1.mono_right Finset.subset_union_left) hJ.2.2.1
  have h2 := roots_mem_support_of_dec huv hub hvb
    (hJ.2.1.mono_right Finset.subset_union_right) hJ.2.2.2
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [h1.1, h1.2.1, h1.2.2, h2.2.2]

end TypedTriangle.SparseEdge
