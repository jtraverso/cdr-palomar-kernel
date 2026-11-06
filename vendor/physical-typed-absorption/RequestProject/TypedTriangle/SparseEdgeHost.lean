/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Lattice
public import RequestProject.TypedTriangle.SparseEdgeLattice

@[expose] public section

/-!
# Borrado disperso de aristas con el `Host` original (Prioridad A, V11)

ESTADO: FUENTE NO COMPILADA EN ESTE ENTORNO. Se entrega como adaptador para compilar
junto a las fuentes originales `Defs.lean`, `Basic.lean`, `Lattice.lean` (SHA-256 en
`INPUT_RECEIPT_V11.md`) y a `SparseEdgeDefs.lean`/`SparseEdgeLattice.lean` (V9). No importa
`Theorem.lean` ni `RobustHinge.lean`; no clona `Host` ni `Defs`.

Identificaciones (todas por definición, `rfl`/`Iff.rfl`, sin hipótesis nuevas):

* `TypedTriangle.lattice H F = SparseEdge.lattice H.G H.lab F`
* `TypedTriangle.CommonNbrCond H F α ↔ SparseEdge.CommonNbrCond H.G H.lab F α`   (H3)
* `TypedTriangle.HingeCond H F α h ↔ SparseEdge.HingeCond H.G H.lab F α h`       (H4)
* `TypedTriangle.edges H = SparseEdge.edges H.G`
* `(TypedTriangle.subHost H J).G = SparseEdge.subGraph H.G J`, con las mismas etiquetas.

El grado se enuncia como `(B.filter (fun e => x ∈ e)).card`, que es literalmente el cuerpo
de `degIn` (`RobustHinge.lean`) y de `SparseEdge.degIn`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

theorem lattice_eq_sparseEdge (H : Host V I) (F : Set (Multiset I)) :
    lattice H F = SparseEdge.lattice H.G H.lab F := rfl

theorem commonNbrCond_iff_sparseEdge (H : Host V I) (F : Set (Multiset I)) (α : ℝ) :
    CommonNbrCond H F α ↔ SparseEdge.CommonNbrCond H.G H.lab F α := Iff.rfl

theorem hingeCond_iff_sparseEdge (H : Host V I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ) :
    HingeCond H F α h ↔ SparseEdge.HingeCond H.G H.lab F α h := Iff.rfl

theorem edges_eq_sparseEdge (H : Host V I) : edges H = SparseEdge.edges H.G := rfl

theorem subHost_G_eq (H : Host V I) (J : Finset (Sym2 V)) :
    (subHost H J).G = SparseEdge.subGraph H.G J := rfl

theorem subHost_lab_eq (H : Host V I) (J : Finset (Sym2 V)) : (subHost H J).lab = H.lab := rfl

/-- **Borrado disperso de aristas con el `Host` original.** Para `α > 0` y `h` existen
`η > 0` y `n₀` (dependientes sólo de `α, h`; explícitamente `η = α/(8·2^C(h,2))`,
`n₀ = ⌈4/α⌉ + 1`) tales que para todo host `H` de orden `n ≥ n₀` con (H3) y (H4) y todo
`B` con grado máximo `≤ η n`: `x ∈ Λ_(H−B) ↔ x ∈ Λ_H ∧ x|_B = 0`, donde
`H − B = subHost H (edges H \ B)`. -/
theorem sparse_edge_deletion_host (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ, ∀ (V I : Type) [Fintype V] (H : Host V I)
      (F : Set (Multiset I)), n₀ ≤ Fintype.card V →
      CommonNbrCond H F α → HingeCond H F α h →
      ∀ B : Finset (Sym2 V),
        (∀ x, (((B.filter (fun e => x ∈ e)).card : ℕ) : ℝ) ≤ η * Fintype.card V) →
        ∀ y : Sym2 V → ℤ,
          y ∈ lattice (subHost H (edges H \ B)) F ↔ y ∈ lattice H F ∧ ∀ e ∈ B, y e = 0 := by
  obtain ⟨η, hη, n₀, hmain⟩ := SparseEdge.sparse_edge_deletion_lattice α h hα
  refine ⟨η, hη, n₀, fun V I _ H F hn hH3 hH4 B hdeg y => ?_⟩
  have heq : lattice (subHost H (edges H \ B)) F =
      SparseEdge.lattice H.G H.lab F ⊓ SparseEdge.zeroOn B :=
    hmain V I H.G H.lab F hn hH3 hH4 B hdeg
  rw [heq, Submodule.mem_inf]
  rfl

end TypedTriangle
