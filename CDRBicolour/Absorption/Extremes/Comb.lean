/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Exact.Trade

/-!
# Integer combinations of triangles on finite models (item 3, extremes)

A *model combination* is a list of pairs `(κ, T)` with `κ : ℤ` and `T` a triangle of `Fin k`;
its edge function is `combZ L e = Σ κ·[e ∈ E(T)]`.  Identities between model combinations are
checked by `decide` and transported along any injection `φ : Fin k ↪ V`
(`comb_transport`): the edge function of the image combination is the push-forward.

The three identities of the five-type lattice (bicoloured triangles except `AAC`), found by
integer programming (`tools/extremes/identities.py`), classes `A | B | C`:
* `I1` on `A₀A₁ | B₂B₃ | C₄C₅C₆`: `A₀A₁C₄ − A₀A₁C₅` is a combination of 10 non-`AAC` triangles;
* `I2` on the same model: `2·A₀A₁C₄` is a combination of 17 non-`AAC` triangles;
* `I3` on `A₀A₁A₂ | B₃B₄B₅ | C₆C₇C₈`: `A₀A₁C₆ + A₁A₂C₇ + A₀A₂C₈` is a combination of 15.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Extremes

open Finset TypedTriangle CDRBicolour.Absorption.Exact

/-- Edge function of a model combination. -/
def combZ {k : ℕ} (L : List (ℤ × Finset (Fin k))) (e : Sym2 (Fin k)) : ℤ :=
  (L.map fun p => p.1 * if e ∈ te p.2 then 1 else 0).sum

/-- Model labels: `A` points first, then `B`, then `C`. -/
def mlab {k : ℕ} (na nb : ℕ) (i : Fin k) : Fin 3 :=
  if i.val < na then 0 else if i.val < na + nb then 1 else 2

/-! ### The identities on the models -/

/-- `I1`, left side (non-`AAC` triangles). -/
def I1L : List (ℤ × Finset (Fin 7)) :=
  [(1, {0, 4, 6}), (-1, {0, 5, 6}), (1, {1, 4, 6}), (-1, {1, 5, 6}), (1, {2, 3, 4}),
    (-1, {2, 3, 5}), (-1, {2, 4, 6}), (1, {2, 5, 6}), (-1, {3, 4, 6}), (1, {3, 5, 6})]

/-- `I1`, right side. -/
def I1R : List (ℤ × Finset (Fin 7)) := [(1, {0, 1, 4}), (-1, {0, 1, 5})]

/-- `I2`, left side. -/
def I2L : List (ℤ × Finset (Fin 7)) :=
  [(1, {0, 1, 2}), (1, {0, 1, 3}), (-1, {0, 2, 3}), (1, {0, 4, 5}), (1, {0, 4, 6}),
    (-1, {0, 5, 6}), (-1, {1, 2, 3}), (1, {1, 4, 5}), (1, {1, 4, 6}), (-1, {1, 5, 6}),
    (2, {2, 3, 4}), (-1, {2, 4, 5}), (-1, {2, 4, 6}), (1, {2, 5, 6}), (-1, {3, 4, 5}),
    (-1, {3, 4, 6}), (1, {3, 5, 6})]

/-- `I2`, right side. -/
def I2R : List (ℤ × Finset (Fin 7)) := [(2, {0, 1, 4})]

/-- `I3`, left side. -/
def I3L : List (ℤ × Finset (Fin 9)) :=
  [(1, {0, 1, 3}), (1, {0, 2, 5}), (-1, {0, 3, 5}), (1, {0, 6, 8}), (1, {1, 2, 4}),
    (-1, {1, 3, 4}), (1, {1, 6, 7}), (-1, {2, 4, 5}), (1, {2, 7, 8}), (1, {3, 4, 7}),
    (1, {3, 5, 6}), (-1, {3, 6, 7}), (1, {4, 5, 8}), (-1, {4, 7, 8}), (-1, {5, 6, 8})]

/-- `I3`, right side. -/
def I3R : List (ℤ × Finset (Fin 9)) := [(1, {0, 1, 6}), (1, {1, 2, 7}), (1, {0, 2, 8})]

set_option maxRecDepth 100000 in
theorem I1_model : combZ I1L = combZ I1R := by decide +kernel

set_option maxRecDepth 100000 in
theorem I2_model : combZ I2L = combZ I2R := by decide +kernel

set_option maxRecDepth 100000 in
theorem I3_model : combZ I3L = combZ I3R := by decide +kernel

/-- Every triangle on the left sides is bicoloured and not `AAC`. -/
def okTri {k : ℕ} (na nb : ℕ) (T : Finset (Fin k)) : Prop :=
  T.card = 3 ∧ T.val.map (mlab na nb) ≠ ({0, 0, 2} : Multiset (Fin 3)) ∧
    (T.image (mlab na nb)).card = 2

instance {k : ℕ} (na nb : ℕ) (T : Finset (Fin k)) : Decidable (okTri na nb T) := by
  unfold okTri; infer_instance

set_option maxRecDepth 100000 in
theorem I1L_ok : ∀ p ∈ I1L, okTri 2 2 p.2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem I2L_ok : ∀ p ∈ I2L, okTri 2 2 p.2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem I3L_ok : ∀ p ∈ I3L, okTri 3 3 p.2 := by decide +kernel

/-! ### Transport along an injection -/

variable {V : Type*} [DecidableEq V]

theorem triEdges_map' {k : ℕ} (φ : Fin k ↪ V) (T : Finset (Fin k)) :
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

/-- The image combination as an integer edge function on `V`. -/
def combV {k : ℕ} (φ : Fin k ↪ V) (L : List (ℤ × Finset (Fin k))) : Sym2 V → ℤ :=
  (L.map fun p => p.1 • ind (triEdges (p.2.map φ))).sum

theorem combV_apply {k : ℕ} (φ : Fin k ↪ V) (L : List (ℤ × Finset (Fin k))) (e : Sym2 V) :
    combV φ L e = (L.map fun p => p.1 * if e ∈ triEdges (p.2.map φ) then 1 else 0).sum := by
  unfold combV
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, Pi.add_apply, ih, List.map_cons, List.sum_cons]
    congr 1
    simp only [Pi.smul_apply, ind, smul_eq_mul]
    congr

theorem mem_triEdges_map_iff {k : ℕ} (φ : Fin k ↪ V) (T : Finset (Fin k)) (e' : Sym2 (Fin k)) :
    Sym2.map φ e' ∈ triEdges (T.map φ) ↔ e' ∈ te T := by
  rw [triEdges_map', te_eq]
  simp only [mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, hxe⟩
    rwa [← Sym2.map.injective φ.injective hxe]
  · intro h; exact ⟨e', h, rfl⟩

theorem not_mem_triEdges_map {k : ℕ} (φ : Fin k ↪ V) (T : Finset (Fin k)) {e : Sym2 V}
    (he : ∀ e' : Sym2 (Fin k), Sym2.map φ e' ≠ e) : e ∉ triEdges (T.map φ) := by
  rw [triEdges_map']
  simp only [mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
  exact fun x _ => he x

/-- **Transport**: a model identity gives the same identity between image combinations. -/
theorem comb_transport {k : ℕ} (φ : Fin k ↪ V) {L₁ L₂ : List (ℤ × Finset (Fin k))}
    (h : combZ L₁ = combZ L₂) : combV φ L₁ = combV φ L₂ := by
  funext e
  rw [combV_apply, combV_apply]
  by_cases he : ∃ e' : Sym2 (Fin k), Sym2.map φ e' = e
  · obtain ⟨e', rfl⟩ := he
    have := congrFun h e'
    simp only [combZ] at this
    simp only [mem_triEdges_map_iff]
    exact this
  · simp only [not_exists] at he
    have h0 : ∀ L : List (ℤ × Finset (Fin k)),
        (L.map fun p => p.1 * if e ∈ triEdges (p.2.map φ) then (1 : ℤ) else 0).sum = 0 := by
      intro L
      induction L with
      | nil => simp
      | cons p L ih =>
        simp only [List.map_cons, List.sum_cons, ite_eq_right_iff.mpr (fun h => absurd h (not_mem_triEdges_map φ p.2 he)), mul_zero,
          ih, add_zero]
    rw [h0, h0]

end CDRBicolour.Absorption.Extremes
