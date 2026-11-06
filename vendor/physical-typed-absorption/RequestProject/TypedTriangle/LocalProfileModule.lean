/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RoutingBudget
public import RequestProject.TypedTriangle.SubtypeCert
public import RequestProject.TypedTriangle.GroupingFrontier

@[expose] public section

/-!
# V16: el módulo de perfiles locales `M` y el puente de soporte físico

* `localProfile G lab F : Submodule ℤ (Sym2 V → ℤ)` con `carrier = {x | IsLocalProfile G lab F x}`
  (`mem_localProfile` es `Iff.rfl`).
* `lattice_le_localProfile`: `Λ = SparseEdge.lattice G lab F ≤ M` (el retículo, NO su
  saturación; no se supone `M = Λ`).
* Para vectores soportados en las aristas de `G`: `l1E = norm1 G`, `front = {v | InSupp G v ·}`.
* `card_blocks_front_le`: **puente exacto de frontera física.** Para bloques disjuntos de
  índices, el número de bloques cuya suma tiene a `v` en su frontera física (UNIÓN de los
  vértices de las aristas del soporte) es `≤` el número de celdas originales con `InSupp G v`.
  La inclusión de soporte a nivel de coordenadas se eleva a raíces físicas explícitamente
  (`front_blockSum_subset`).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Composition

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
open TypedTriangle.Dispersal

variable {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- **El módulo `M` de perfiles locales**, con carrier exactamente `IsLocalProfile`. -/
def localProfile : Submodule ℤ (Sym2 V → ℤ) where
  carrier := {x | IsLocalProfile G lab F x}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun e he => by simp [hx1 e he, hy1 e he], fun v => ?_⟩
    obtain ⟨c1, hc1⟩ := hx2 v
    obtain ⟨c2, hc2⟩ := hy2 v
    exact ⟨c1 + c2, fun w hw => by simp [hc1 w hw, hc2 w hw, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ => ⟨0, fun _ _ => by simp⟩⟩
  smul_mem' := by
    rintro r x ⟨hx1, hx2⟩
    refine ⟨fun e he => by simp [hx1 e he], fun v => ?_⟩
    obtain ⟨c1, hc1⟩ := hx2 v
    exact ⟨r • c1, fun w hw => by simp [hc1 w hw, Finset.mul_sum]⟩

lemma mem_localProfile {x : Sym2 V → ℤ} : x ∈ localProfile G lab F ↔ IsLocalProfile G lab F x :=
  Iff.rfl

omit [Fintype V] in
lemma mem_triEdges_pair {T : Finset V} {v w : V} (hvw : v ≠ w) :
    s(v, w) ∈ triEdges T ↔ v ∈ T ∧ w ∈ T := by
  simp [triEdges, Finset.mem_filter, hvw]

lemma mem_edges_of_mem_triEdges {T : Finset V} (hT : IsAllowed G lab F T) {e : Sym2 V}
    (he : e ∈ triEdges T) : e ∈ edges G := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeSet]
    exact hT.2.1 a he.1.1 b he.1.2 he.2

/-- Cada generador `ind (triEdges T)` (con `T` permitido) es un perfil local. -/
lemma ind_isLocalProfile {T : Finset V} (hT : IsAllowed G lab F T) :
    IsLocalProfile G lab F (ind (triEdges T)) := by
  refine ⟨fun e he => ?_, fun v => ⟨fun T' => if T' = T then 1 else 0, fun w hw => ?_⟩⟩
  · simp only [ind]
    rw [if_neg]
    exact fun h => he (mem_edges_of_mem_triEdges G lab F hT h)
  · rw [Finset.sum_ite_eq']
    simp only [ind, mem_triEdges_pair hw.symm, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v ∈ T <;> by_cases hw' : w ∈ T <;> simp [hv, hw', hT]

/-- **`Λ ≤ M`**: el retículo físico (sin saturar) está contenido en los perfiles locales. -/
theorem lattice_le_localProfile : lattice G lab F ≤ localProfile G lab F := by
  rw [lattice, Submodule.span_le]
  rintro _ ⟨T, hT, rfl⟩
  exact ind_isLocalProfile G lab F hT

/-- Soportado en las aristas de `G`. -/
def EdgeSupp (x : Sym2 V → ℤ) : Prop := ∀ e, e ∉ edges G → x e = 0

variable {G lab F}

lemma edgeSupp_of_lattice {x : Sym2 V → ℤ} (hx : x ∈ lattice G lab F) : EdgeSupp G x :=
  (lattice_le_localProfile G lab F hx).1

lemma l1E_eq_norm1 {x : Sym2 V → ℤ} (hx : EdgeSupp G x) : l1E x = norm1 G x := by
  unfold l1E norm1
  rw [← Finset.sum_subset (Finset.subset_univ (edges G)) (fun e _ he => by rw [hx e he]; simp)]
  exact Finset.sum_subtype _ (fun e => by simp [edges]) (fun e => |x e|)

lemma mem_front_iff {x : Sym2 V → ℤ} (hx : EdgeSupp G x) (v : V) :
    v ∈ front x ↔ InSupp G v x := by
  simp only [front, Finset.mem_filter, Finset.mem_univ, true_and, InSupp]
  constructor
  · rintro ⟨e, he, hve⟩
    have hE : e ∈ G.edgeSet := by
      by_contra hn
      exact he (hx e (by simpa [edges] using hn))
    exact ⟨⟨e, hE⟩, hve, he⟩
  · rintro ⟨e, hve, he⟩
    exact ⟨e.1, he, hve⟩

lemma norm1_nonneg (x : Sym2 V → ℤ) : 0 ≤ norm1 G x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma dabs_nonneg (x : Sym2 V → ℤ) (v : V) : 0 ≤ dabs G x v :=
  Finset.sum_nonneg fun e _ => by split_ifs <;> simp

lemma eq_zero_of_norm1_eq_zero {x : Sym2 V → ℤ} (hx : EdgeSupp G x) (h0 : norm1 G x = 0) :
    x = 0 := by
  rw [← l1E_eq_norm1 hx] at h0
  funext e
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => abs_nonneg (x e))).1 h0 e
    (Finset.mem_univ _)
  simpa using this

/-- **Elevación a raíces físicas.** Si `v` está en la frontera física de la suma de un bloque
(es extremo de una arista `e` con `(∑_{i∈J} b_i) e ≠ 0`), alguna celda `b_i` del bloque tiene
`b_i e ≠ 0`, y como `b_i` está soportada en aristas, `e ∈ G` y `InSupp G v b_i`. -/
lemma front_blockSum_subset {ι : Type*} (b : ι → Sym2 V → ℤ) (hb : ∀ i, EdgeSupp G (b i))
    (J : Finset ι) {v : V} (hv : v ∈ front (∑ i ∈ J, b i)) : ∃ i ∈ J, InSupp G v (b i) := by
  simp only [front, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨e, he, hve⟩ := hv
  rw [Finset.sum_apply] at he
  obtain ⟨i, hi, hie⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  exact ⟨i, hi, (mem_front_iff (hb i) v).1
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, e, hie, hve⟩)⟩

/-- **Puente exacto de frontera física bajo agrupación.** -/
theorem card_blocks_front_le {ι : Type*} [Fintype ι] (b : ι → Sym2 V → ℤ)
    (hb : ∀ i, EdgeSupp G (b i)) (P : Finset (Finset ι))
    (hP : (P : Set (Finset ι)).PairwiseDisjoint id) (v : V) :
    #(P.filter fun J => v ∈ front (∑ i ∈ J, b i)) ≤ #(univ.filter fun i => InSupp G v (b i)) := by
  refine le_trans (Finset.card_le_card ?_)
    (TypedTriangle.Grouping.card_blocks_using_le P hP (fun i v => InSupp G v (b i)) v)
  intro J hJ
  obtain ⟨hJP, hJv⟩ := Finset.mem_filter.1 hJ
  exact Finset.mem_filter.2 ⟨hJP, front_blockSum_subset b hb J hJv⟩

lemma sum_get_eq {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → β) :
    ∑ i : Fin l.length, g (l.get i) = (l.map g).sum := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map l g

/-- Recuento sobre los índices de una lista: `#{i : p (l[i])} = countP p l`. -/
lemma card_filter_get_eq_countP {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (univ.filter (fun i : Fin l.length => p (l.get i))).card = l.countP (fun a => decide (p a)) := by
  rw [Finset.card_filter, sum_get_eq l (fun a => if p a then 1 else 0)]
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [ih, h, add_comm]

end TypedTriangle.Composition
