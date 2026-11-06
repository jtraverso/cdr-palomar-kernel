/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Empaquetamiento de vecindades cerradas y diámetro (V12, S26 §3, parte genérica)

Para un grafo simple finito arbitrario `H` con grado mínimo `≥ m`:

* `dist_packing` — si `u` y `v` están conectados, `(dist u v / 3 + 1) · (m + 1) ≤ |V(H)|`:
  las vecindades cerradas de los vértices `0, 3, 6, …` de un camino más corto son disjuntas.
* `dist_lt_of_card_le` — con `|V(H)| ≤ 2 C n` y `n ≤ 2 C m` (grado `≥ n/(2C)`), `n > 0`:
  `dist u v < 12 C²` para todo par conectado (luego `< ⌈12 C²⌉ + 3`).

Es puramente combinatorio y no usa nada del host.
-/

open Finset Classical

namespace TypedTriangle.Packing

variable {W : Type*} [Fintype W] (H : SimpleGraph W)

/-- Vecindad cerrada. -/
noncomputable def closedNbhd (w : W) : Finset W := insert w (H.neighborFinset w)

lemma card_closedNbhd (w : W) : (closedNbhd H w).card = H.degree w + 1 := by
  rw [closedNbhd, Finset.card_insert_of_notMem (by simp), SimpleGraph.card_neighborFinset_eq_degree]

lemma mem_closedNbhd {w x : W} : x ∈ closedNbhd H w ↔ x = w ∨ H.Adj w x := by
  simp [closedNbhd]

variable {H}

lemma walk_to_closedNbhd {u v : W} (p : H.Walk u v) (i : ℕ) {x : W}
    (hx : x ∈ closedNbhd H (p.getVert i)) : ∃ q : H.Walk u x, q.length ≤ i + 1 := by
  rcases (mem_closedNbhd H).mp hx with rfl | h
  · exact ⟨p.take i, by rw [SimpleGraph.Walk.take_length]; omega⟩
  · exact ⟨(p.take i).concat h, by
      rw [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.take_length]; omega⟩

lemma walk_from_closedNbhd {u v : W} (p : H.Walk u v) (j : ℕ) {x : W}
    (hx : x ∈ closedNbhd H (p.getVert j)) : ∃ q : H.Walk x v, q.length ≤ p.length - j + 1 := by
  rcases (mem_closedNbhd H).mp hx with rfl | h
  · exact ⟨p.drop j, by rw [SimpleGraph.Walk.drop_length]; omega⟩
  · exact ⟨SimpleGraph.Walk.cons h.symm (p.drop j), by
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.drop_length]⟩

/-- **Empaquetamiento**: en un grafo con grado mínimo `≥ m`, dos vértices conectados a
distancia `d` dan `(d/3 + 1)(m + 1) ≤ |V|`. -/
theorem dist_packing (m : ℕ) (hdeg : ∀ w, m ≤ H.degree w) {u v : W} (huv : H.Reachable u v) :
    (H.dist u v / 3 + 1) * (m + 1) ≤ Fintype.card W := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  set d := H.dist u v
  let N : ℕ → Finset W := fun k => closedNbhd H (p.getVert (3 * k))
  have hdisj : Set.PairwiseDisjoint (↑(range (d / 3 + 1)) : Set ℕ) N := by
    intro k hk l hl hkl
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxk hxl
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    -- sin pérdida de generalidad `k < l`
    have key : ∀ a b, a < b → b < d / 3 + 1 → x ∈ N a → x ∈ N b → False := by
      intro a b hab hb hxa hxb
      obtain ⟨q1, hq1⟩ := walk_to_closedNbhd p (3 * a) hxa
      obtain ⟨q2, hq2⟩ := walk_from_closedNbhd p (3 * b) hxb
      have := SimpleGraph.dist_le (q1.append q2)
      rw [SimpleGraph.Walk.length_append] at this
      omega
    rcases Nat.lt_or_gt_of_ne hkl with h | h
    · exact key k l h hl hxk hxl
    · exact key l k h hk hxl hxk
  calc (d / 3 + 1) * (m + 1) = ∑ _k ∈ range (d / 3 + 1), (m + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ k ∈ range (d / 3 + 1), (N k).card := Finset.sum_le_sum fun k _ => by
        simp only [N, card_closedNbhd]; exact Nat.succ_le_succ (hdeg _)
    _ = ((range (d / 3 + 1)).biUnion N).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card W := Finset.card_le_univ _

/-- **Diámetro**: con a lo sumo `2 C n` vértices y grado mínimo `≥ n/(2C)` (es decir
`n ≤ 2 C m`), `n > 0`, dos vértices conectados están a distancia `< 12 C²`. -/
theorem dist_lt_of_card_le (C n m : ℕ) (hn : 0 < n) (hcard : Fintype.card W ≤ 2 * C * n)
    (hm : n ≤ 2 * C * m) (hdeg : ∀ w, m ≤ H.degree w) {u v : W} (huv : H.Reachable u v) :
    H.dist u v < 12 * C ^ 2 := by
  have hpack := dist_packing m hdeg huv
  set d := H.dist u v
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have h1 : (d / 3 + 1) * (m + 1) < (4 * C ^ 2) * (m + 1) := by
    calc (d / 3 + 1) * (m + 1) ≤ 2 * C * n := hpack.trans hcard
      _ ≤ 2 * C * (2 * C * m) := Nat.mul_le_mul_left _ hm
      _ = 4 * C ^ 2 * m := by ring
      _ < 4 * C ^ 2 * (m + 1) := by
        have hC : 0 < C := by
          rcases Nat.eq_zero_or_pos C with h | h
          · subst h; omega
          · exact h
        apply Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  have h2 := Nat.lt_of_mul_lt_mul_right h1
  omega

end TypedTriangle.Packing
