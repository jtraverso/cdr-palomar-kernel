/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Host

/-!
# A bicoloured trade changing the number of `AAC` blocks by one (item 3, exact spectrum)

On nine points `a₀ a₁ a₂ | b₀ b₁ b₂ | c₀ c₁ c₂` (classes `A | B | C`), the two families of nine
triangles `T₁` and `T₀` (found by integer programming, `tools/refined/aac_trade.py`) are packings
covering the same 27 edges; all 18 triangles are bicoloured; `T₁` has two `AAC` triangles and `T₀`
one.  Facts are checked on `Fin 9` by `decide` (with a computable copy `te` of `triEdges`) and
transported along any injection (`triEdges_map`).
-/

@[expose] public section

namespace CDRBicolour.Absorption.Exact

open Finset TypedTriangle

/-- A computable copy of `triEdges`. -/
def te {α : Type*} [DecidableEq α] (T : Finset α) : Finset (Sym2 α) :=
  T.sym2.filter fun e => ¬ e.IsDiag

theorem te_eq {α : Type*} [DecidableEq α] (T : Finset α) : te T = triEdges T := by
  ext e; simp [te, triEdges]

/-- Half `T₁` (points `0 1 2 = a`, `3 4 5 = b`, `6 7 8 = c`). -/
def T1m : Finset (Finset (Fin 9)) :=
  {{0, 1, 6}, {0, 2, 7}, {0, 3, 5}, {1, 2, 3}, {1, 4, 5}, {1, 7, 8}, {3, 4, 8}, {3, 6, 7}, {5, 6, 8}}

/-- Half `T₀`. -/
def T0m : Finset (Finset (Fin 9)) :=
  {{0, 1, 5}, {0, 2, 3}, {0, 6, 7}, {1, 2, 7}, {1, 3, 4}, {1, 6, 8}, {3, 5, 6}, {3, 7, 8}, {4, 5, 8}}

/-- Class of a model point. -/
def mcol (i : Fin 9) : Fin 3 := ⟨i.val / 3, by omega⟩

set_option maxRecDepth 100000 in
theorem model_union : T1m.biUnion te = T0m.biUnion te := by decide +kernel

set_option maxRecDepth 100000 in
theorem model_disj1 : ∀ T ∈ T1m, ∀ T' ∈ T1m, T ≠ T' → Disjoint (te T) (te T') := by decide +kernel

set_option maxRecDepth 100000 in
theorem model_disj0 : ∀ T ∈ T0m, ∀ T' ∈ T0m, T ≠ T' → Disjoint (te T) (te T') := by decide +kernel

set_option maxRecDepth 100000 in
theorem model_card : (∀ T ∈ T1m, T.card = 3) ∧ ∀ T ∈ T0m, T.card = 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem model_bicol : (∀ T ∈ T1m, (T.image mcol).card = 2) ∧ ∀ T ∈ T0m, (T.image mcol).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem model_halves_disjoint : Disjoint T1m T0m := by decide +kernel

/-- `AAC` triangles: two `A` points and one `C` point. -/
def isAAC (T : Finset (Fin 9)) : Prop :=
  (T.filter fun i => mcol i = 0).card = 2 ∧ (T.filter fun i => mcol i = 2).card = 1

instance : DecidablePred isAAC := fun T => by unfold isAAC; infer_instance

set_option maxRecDepth 100000 in
theorem model_aac : (T1m.filter isAAC).card = 2 ∧ (T0m.filter isAAC).card = 1 := by decide +kernel

/-! ### Transport along an injection -/

variable {V : Type*} [DecidableEq V]

theorem triEdges_map (φ : Fin 9 ↪ V) (T : Finset (Fin 9)) :
    triEdges (T.map φ) = (triEdges T).map ⟨Sym2.map φ, Sym2.map.injective φ.injective⟩ := by
  rw [← te_eq, ← te_eq]
  ext e
  induction e using Sym2.ind with
  | _ u v =>
  simp only [te, mem_filter, mk_mem_sym2_iff, mem_map, Sym2.mk_isDiag_iff,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, hne⟩
    refine ⟨s(x, y), ⟨by simp [hx, hy], ?_⟩, rfl⟩
    rw [Sym2.mk_isDiag_iff]; exact fun h => hne (by rw [h])
  · rintro ⟨e', ⟨he1, he2⟩, hmap⟩
    induction e' using Sym2.ind with
    | _ x y =>
    rw [mk_mem_sym2_iff] at he1
    rw [Sym2.mk_isDiag_iff] at he2
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨⟨x, he1.1, rfl⟩, ⟨y, he1.2, rfl⟩⟩, fun h => he2 (φ.injective h)⟩
    · exact ⟨⟨⟨y, he1.2, rfl⟩, ⟨x, he1.1, rfl⟩⟩, fun h => he2 (φ.injective h).symm⟩
/-- The two halves of the trade placed by `φ`. -/
def half1 (φ : Fin 9 ↪ V) : Finset (Finset V) := T1m.image fun T => T.map φ
def half0 (φ : Fin 9 ↪ V) : Finset (Finset V) := T0m.image fun T => T.map φ

theorem map_inj (φ : Fin 9 ↪ V) : Function.Injective fun T : Finset (Fin 9) => T.map φ :=
  fun _ _ h => Finset.map_injective φ h

theorem union_eq (φ : Fin 9 ↪ V) : (half1 φ).biUnion triEdges = (half0 φ).biUnion triEdges := by
  have key : ∀ S : Finset (Finset (Fin 9)), (S.image fun T => T.map φ).biUnion triEdges =
      (S.biUnion te).map ⟨Sym2.map φ, Sym2.map.injective φ.injective⟩ := by
    intro S
    rw [image_biUnion, map_eq_image, biUnion_image]
    refine biUnion_congr rfl fun T _ => ?_
    rw [triEdges_map, te_eq, map_eq_image]
  unfold half1 half0
  rw [key, key, model_union]

theorem disj_of_model {S : Finset (Finset (Fin 9))}
    (hS : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → Disjoint (te T) (te T')) (φ : Fin 9 ↪ V) :
    ((S.image fun T => T.map φ : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint
      triEdges := by
  intro A hA B hB hAB
  simp only [coe_image, Set.mem_image, mem_coe] at hA hB
  obtain ⟨T, hT, rfl⟩ := hA
  obtain ⟨T', hT', rfl⟩ := hB
  have hne : T ≠ T' := fun h => hAB (h ▸ rfl)
  show Disjoint (triEdges (T.map φ)) (triEdges (T'.map φ))
  rw [triEdges_map, triEdges_map, disjoint_map, ← te_eq, ← te_eq]
  exact hS T hT T' hT' hne

theorem half1_disj (φ : Fin 9 ↪ V) :
    ((half1 φ : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint triEdges :=
  disj_of_model model_disj1 φ

theorem half0_disj (φ : Fin 9 ↪ V) :
    ((half0 φ : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint triEdges :=
  disj_of_model model_disj0 φ

end CDRBicolour.Absorption.Exact
