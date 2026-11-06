/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Polígono en zigzag (V13, S26 §5, parte A: combinatoria pura)

Para un polígono orientado con vértices `0, 1, …, l-1` (`l ≥ 3`) se CONSTRUYE la
triangulación en zigzag por orejas alternadas del intervalo actual `[a, b]`:
oreja izquierda `(a, a+1, b)`, luego oreja derecha `(a, b-1, b)`, y así hasta los tres
últimos vértices (`zig`). No es una premisa de un proveedor de triangulaciones.

* `zig_eq_map` — forma explícita: la cara `j` es `(lo j, third j, hi j)` con
  `lo j = ⌊(j+1)/2⌋`, `hi j = l-1-⌊j/2⌋` (`polyFaces_eq`).
* `length_polyFaces` — exactamente `l - 2` caras.
* `card_faces_at_le_three` — cada vértice está en a lo sumo TRES caras.
* `card_diagonals_at_le_two` — cada vértice es extremo de a lo sumo DOS diagonales
  (las diagonales son `(lo i, hi i)`, `1 ≤ i ≤ l-3`).
* `faces_with_diag` / `faces_with_diag_rev` — cada diagonal interna aparece exactamente en
  dos caras, con orientaciones opuestas: `(lo i, hi i)` sólo en la cara `i-1` y
  `(hi i, lo i)` sólo en la cara `i`.
* `edge_cases` — toda arista orientada de una cara es un lado del polígono en su sentido
  original o una diagonal en uno de los dos sentidos; `faces_with_side` — cada lado aparece
  exactamente en una cara, y nunca invertido (`faces_with_side_rev`).
* `polyFaces_sum` — la suma orientada de los bordes de las caras es el borde orientado del
  polígono, para cualquier `g` antisimétrica con valores en un grupo abeliano.
-/

@[expose] public section

open Finset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Zigzag

/-- **Construcción por orejas alternadas.** `zig a k left` son las caras del zigzag sobre el
intervalo `[a, a+k+2]`, empezando por una oreja izquierda `(a, a+1, b)` si `left` y por una
derecha `(a, b-1, b)` si no; el último paso es el triángulo `(a, a+1, a+2)`. -/
def zig : ℕ → ℕ → Bool → List (ℕ × ℕ × ℕ)
  | a, 0, _ => [(a, a + 1, a + 2)]
  | a, k + 1, true => (a, a + 1, a + k + 3) :: zig (a + 1) k false
  | a, k + 1, false => (a, a + k + 2, a + k + 3) :: zig a k true

/-- Cara `j` del zigzag sobre `[a, a+k+2]` en forma explícita. -/
def zigF (a k : ℕ) (left : Bool) (j : ℕ) : ℕ × ℕ × ℕ :=
  let lo := if left then a + (j + 1) / 2 else a + j / 2
  let hi := if left then a + k + 2 - j / 2 else a + k + 2 - (j + 1) / 2
  (lo, if (left = true ↔ j % 2 = 0) then lo + 1 else hi - 1, hi)

lemma zig_eq_map (a k : ℕ) (left : Bool) :
    zig a k left = (List.range (k + 1)).map (zigF a k left) := by
  induction k generalizing a left with
  | zero => cases left <;> simp [zig, zigF]
  | succ k ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    cases left <;>
    · rw [zig, ih]
      refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
      · rfl
      · refine List.map_congr_left fun j _ => ?_
        simp only [zigF, Function.comp]
        ext <;> simp <;> (try split_ifs) <;> omega

/-! ### El polígono `0, …, l-1` -/

/-- Extremo inferior del intervalo antes de la cara `j`. -/
def lo (j : ℕ) : ℕ := (j + 1) / 2

/-- Extremo superior del intervalo antes de la cara `j`. -/
def hi (l j : ℕ) : ℕ := l - 1 - j / 2

/-- Tercer vértice de la cara `j`: `lo+1` (oreja izquierda, `j` par) o `hi-1` (oreja
derecha, `j` impar). -/
def third (l j : ℕ) : ℕ := if j % 2 = 0 then lo j + 1 else hi l j - 1

/-- Cara orientada `j` del polígono. -/
def face (l j : ℕ) : ℕ × ℕ × ℕ := (lo j, third l j, hi l j)

/-- Caras del zigzag del polígono de `l` vértices (construcción recursiva). -/
def polyFaces (l : ℕ) : List (ℕ × ℕ × ℕ) := zig 0 (l - 3) true

/-- Aristas orientadas de una cara `(p, q, r)`: `p→q`, `q→r`, `r→p`. -/
def oEdges (f : ℕ × ℕ × ℕ) : List (ℕ × ℕ) := [(f.1, f.2.1), (f.2.1, f.2.2), (f.2.2, f.1)]

/-- Vértices de una cara. -/
def verts (f : ℕ × ℕ × ℕ) : List ℕ := [f.1, f.2.1, f.2.2]

/-- Lado orientado del polígono (sentido original): `i → i+1` o `l-1 → 0`. -/
def IsSide (l : ℕ) (e : ℕ × ℕ) : Prop := (e.2 = e.1 + 1 ∧ e.2 < l) ∨ (e.1 = l - 1 ∧ e.2 = 0)

/-- Diagonal `i` (`1 ≤ i ≤ l-3`): el intervalo antes de la cara `i`. -/
def diag (l i : ℕ) : ℕ × ℕ := (lo i, hi l i)

/-- **Forma explícita de la construcción.** -/
theorem polyFaces_eq {l : ℕ} (hl : 3 ≤ l) :
    polyFaces l = (List.range (l - 2)).map (face l) := by
  unfold polyFaces
  rw [zig_eq_map, show l - 3 + 1 = l - 2 by omega]
  refine List.map_congr_left fun j _ => ?_
  simp only [zigF, face, lo, hi, third]
  ext <;> simp <;> (try split_ifs) <;> omega

/-- **Exactamente `l - 2` caras.** -/
theorem length_polyFaces {l : ℕ} (hl : 3 ≤ l) : (polyFaces l).length = l - 2 := by
  rw [polyFaces_eq hl]; simp

lemma getElem_polyFaces {l : ℕ} (hl : 3 ≤ l) (j : ℕ) (hj : j < (polyFaces l).length) :
    (polyFaces l)[j] = face l j := by
  simp [polyFaces_eq hl]

/-- **Cada vértice está en a lo sumo tres caras.** -/
theorem card_faces_at_le_three (l v : ℕ) :
    ((range (l - 2)).filter (fun j => v ∈ verts (face l j))).card ≤ 3 := by
  by_cases h : 2 * v ≤ l - 1
  · refine (card_le_card (t := {2 * v - 2, 2 * v - 1, 2 * v}) ?_).trans card_le_three
    intro j hj
    simp only [mem_filter, mem_range, verts, face, lo, hi, third, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    simp only [mem_insert, mem_singleton]
    split_ifs at hj <;> omega
  · refine (card_le_card (t := {2 * l - 2 * v - 3, 2 * l - 2 * v - 2, 2 * l - 2 * v - 1})
      ?_).trans card_le_three
    intro j hj
    simp only [mem_filter, mem_range, verts, face, lo, hi, third, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    simp only [mem_insert, mem_singleton]
    split_ifs at hj <;> omega

/-- **Cada vértice es extremo de a lo sumo dos diagonales.** -/
theorem card_diagonals_at_le_two (l v : ℕ) :
    ((Icc 1 (l - 3)).filter (fun i => v = (diag l i).1 ∨ v = (diag l i).2)).card ≤ 2 := by
  by_cases h : 2 * v ≤ l - 1
  · refine (card_le_card (t := {2 * v - 1, 2 * v}) ?_).trans card_le_two
    intro j hj
    simp only [mem_filter, mem_Icc, diag, lo, hi] at hj
    simp only [mem_insert, mem_singleton]
    omega
  · refine (card_le_card (t := {2 * l - 2 * v - 2, 2 * l - 2 * v - 1}) ?_).trans card_le_two
    intro j hj
    simp only [mem_filter, mem_Icc, diag, lo, hi] at hj
    simp only [mem_insert, mem_singleton]
    omega

/-- Las aristas de la cara `j`. -/
lemma oEdges_face (l j : ℕ) :
    oEdges (face l j) = [(lo j, third l j), (third l j, hi l j), (hi l j, lo j)] := rfl

/-- **Una diagonal interna, en su sentido `lo → hi`, aparece sólo en la cara `i-1`.** -/
theorem faces_with_diag {l i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ l - 3) :
    (range (l - 2)).filter (fun j => diag l i ∈ oEdges (face l j)) = {i - 1} := by
  ext j
  simp only [mem_filter, mem_range, oEdges_face, diag, lo, hi, third, List.mem_cons,
    Prod.mk.injEq, List.not_mem_nil, or_false, mem_singleton]
  (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)

/-- **La misma diagonal, en sentido `hi → lo`, aparece sólo en la cara `i`.** -/
theorem faces_with_diag_rev {l i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ l - 3) :
    (range (l - 2)).filter (fun j => ((diag l i).2, (diag l i).1) ∈ oEdges (face l j)) =
      {i} := by
  ext j
  simp only [mem_filter, mem_range, oEdges_face, diag, lo, hi, third, List.mem_cons,
    Prod.mk.injEq, List.not_mem_nil, or_false, mem_singleton]
  (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)

/-- **Clasificación de las aristas de las caras**: lado original, diagonal, o diagonal
invertida. -/
theorem edge_cases {l j : ℕ} (hl : 3 ≤ l) (hj : j < l - 2) {e : ℕ × ℕ}
    (he : e ∈ oEdges (face l j)) :
    IsSide l e ∨ ∃ i, 1 ≤ i ∧ i ≤ l - 3 ∧ (e = diag l i ∨ e = ((diag l i).2, (diag l i).1)) := by
  simp only [oEdges_face, List.mem_cons, List.not_mem_nil, or_false] at he
  unfold IsSide diag
  rcases he with rfl | rfl | rfl
  · by_cases hj2 : j % 2 = 0
    · left; left
      refine ⟨?_, ?_⟩ <;> simp only [third, lo, hj2, if_true]; omega
    · by_cases hlast : j = l - 3
      · left; left
        refine ⟨?_, ?_⟩ <;> simp only [third, lo, hi, hj2, if_false] <;> omega
      · right; refine ⟨j + 1, by omega, by omega, Or.inl ?_⟩
        simp only [third, lo, hi, hj2, if_false, Prod.mk.injEq]
        refine ⟨?_, ?_⟩ <;> omega
  · by_cases hj2 : j % 2 = 0
    · by_cases hlast : j = l - 3
      · left; left
        refine ⟨?_, ?_⟩ <;> simp only [third, lo, hi, hj2, if_true] <;> omega
      · right; refine ⟨j + 1, by omega, by omega, Or.inl ?_⟩
        simp only [third, lo, hi, hj2, if_true, Prod.mk.injEq]
        refine ⟨?_, ?_⟩ <;> omega
    · left; left
      refine ⟨?_, ?_⟩ <;> simp only [third, lo, hi, hj2, if_false] <;> omega
  · by_cases hj0 : j = 0
    · subst hj0; left; right; simp [hi, lo]
    · right; exact ⟨j, by omega, by omega, Or.inr rfl⟩

/-- Cada diagonal interna no es un lado (en ningún sentido). -/
theorem diag_not_side {l i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ l - 3) :
    ¬ IsSide l (diag l i) ∧ ¬ IsSide l ((diag l i).2, (diag l i).1) := by
  unfold IsSide diag lo hi; constructor <;> omega

/-- **Cada lado del polígono aparece exactamente en una cara**, en su sentido original. -/
theorem faces_with_side {l i : ℕ} (hl : 3 ≤ l) (hlt : i < l) :
    ((range (l - 2)).filter (fun j => (i, (i + 1) % l) ∈ oEdges (face l j))).card = 1 := by
  rw [card_eq_one]
  by_cases hil : i = l - 1
  · refine ⟨0, ?_⟩
    ext j
    simp only [mem_filter, mem_range, oEdges_face, lo, hi, third, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false, mem_singleton]
    rw [show (i + 1) % l = 0 by rw [hil, Nat.sub_add_cancel (by omega), Nat.mod_self]]
    (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)
  · rw [Nat.mod_eq_of_lt (by omega)]
    by_cases h2 : 2 * i ≤ l - 3
    · refine ⟨2 * i, ?_⟩
      ext j
      simp only [mem_filter, mem_range, oEdges_face, lo, hi, third, List.mem_cons,
        Prod.mk.injEq, List.not_mem_nil, or_false, mem_singleton]
      (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)
    · by_cases h3 : 2 * i ≤ l - 1
      · refine ⟨l - 3, ?_⟩
        ext j
        simp only [mem_filter, mem_range, oEdges_face, lo, hi, third, List.mem_cons,
          Prod.mk.injEq, List.not_mem_nil, or_false, mem_singleton]
        (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)
      · refine ⟨2 * l - 2 * i - 3, ?_⟩
        ext j
        simp only [mem_filter, mem_range, oEdges_face, lo, hi, third, List.mem_cons,
          Prod.mk.injEq, List.not_mem_nil, or_false, mem_singleton]
        (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)

/-- **Ningún lado aparece invertido.** -/
theorem faces_with_side_rev {l i : ℕ} (hl : 3 ≤ l) (hlt : i < l) :
    (range (l - 2)).filter (fun j => ((i + 1) % l, i) ∈ oEdges (face l j)) = ∅ := by
  ext j
  simp only [mem_filter, mem_range, oEdges_face, lo, hi, third,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, Finset.notMem_empty, iff_false,
    not_and]
  intro hj
  by_cases hil : i = l - 1
  · rw [show (i + 1) % l = 0 by rw [hil, Nat.sub_add_cancel (by omega), Nat.mod_self]]
    (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)
  · rw [Nat.mod_eq_of_lt (by omega)]
    (by_cases hj2 : j % 2 = 0 <;> simp only [hj2, ↓reduceIte] <;> omega)

/-! ### Suma orientada de los bordes -/

/-- Borde orientado de una cara evaluado con `g`. -/
def faceBd {M : Type*} [AddCommGroup M] (g : ℕ → ℕ → M) (f : ℕ × ℕ × ℕ) : M :=
  g f.1 f.2.1 + g f.2.1 f.2.2 + g f.2.2 f.1

lemma zig_sum {M : Type*} [AddCommGroup M] (g : ℕ → ℕ → M) (hg : ∀ p q, g q p = - g p q)
    (a k : ℕ) (left : Bool) :
    ((zig a k left).map (faceBd g)).sum =
      ∑ i ∈ range (k + 2), g (a + i) (a + i + 1) + g (a + k + 2) a := by
  induction k generalizing a left with
  | zero =>
    cases left <;> simp [zig, faceBd, Finset.sum_range_succ]
  | succ k ih =>
    cases left
    · rw [zig, List.map_cons, List.sum_cons, ih, Finset.sum_range_succ _ (k + 2)]
      simp only [faceBd]
      rw [hg (a + k + 2) a, show a + k + 2 + 1 = a + k + 3 by ring,
        show a + (k + 1) + 2 = a + k + 3 by ring]
      generalize ∑ i ∈ range (k + 2), g (a + i) (a + i + 1) = S
      abel_nf
    · rw [zig, List.map_cons, List.sum_cons, ih, Finset.sum_range_succ' _ (k + 2)]
      simp only [faceBd]
      have hs : ∑ i ∈ range (k + 2), g (a + 1 + i) (a + 1 + i + 1) =
          ∑ i ∈ range (k + 2), g (a + (i + 1)) (a + (i + 1) + 1) :=
        Finset.sum_congr rfl fun i _ => by rw [show a + 1 + i = a + (i + 1) by ring]
      rw [hs, show a + 1 + k + 2 = a + k + 3 by ring, show a + (k + 1) + 2 = a + k + 3 by ring,
        hg (a + k + 3) (a + 1), add_zero]
      abel

/-- **La suma orientada de los bordes de las caras es el borde del polígono.** Para toda
`g` antisimétrica, `Σ_caras (g p q + g q r + g r p) = Σ_{i<l} g i ((i+1) mod l)`. -/
theorem polyFaces_sum {M : Type*} [AddCommGroup M] (g : ℕ → ℕ → M)
    (hg : ∀ p q, g q p = - g p q) {l : ℕ} (hl : 3 ≤ l) :
    ((polyFaces l).map (faceBd g)).sum = ∑ i ∈ range l, g i ((i + 1) % l) := by
  unfold polyFaces
  rw [zig_sum g hg]
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  simp only [zero_add]
  rw [show m + 1 - 3 + 2 = m by omega, Finset.sum_range_succ _ m, Nat.mod_self]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.mod_eq_of_lt (by simp at hi; omega)]

end TypedTriangle.Zigzag
