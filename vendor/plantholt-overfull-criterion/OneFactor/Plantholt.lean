/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Main
public import Plantholt.Main

/-!
# Plantholt's criterion with an explicit constant

`regularOneFactorable`: every regular graph of even order `n` and degree at least `11 n / 12` is
1-factorizable (`OneFactor.colorable_of_regular`), so Plantholt's Theorem 1.2 applies with
`c* = 11/12`:

`overfull_criterion`: if `G` has even order `n` and `3δ − Δ ≥ 11 n / 6`, then `G` is Class 1 if and
only if it has no `Δ`-overfull subgraph.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph

universe u

/-- **Regular graphs of degree at least `11/12` of the (even) order are 1-factorizable.** -/
theorem lineGraph_colorable_of_isRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : G.IsRegularOfDegree d) (hd : 11 * n ≤ 6 * d) : G.lineGraph.Colorable d := by
  classical
  exact colorable_of_regular hcard (fun v => by convert hreg v) hd

theorem regularOneFactorable : Plantholt.RegularOneFactorable.{u} (11 / 12) := by
  intro W _ _ H _ d hev hreg hcd
  classical
  obtain ⟨n, hn⟩ := hev
  have h11 : 11 * n ≤ 6 * d := by
    have : (11 / 12 : ℝ) * (n + n : ℕ) ≤ d := by rw [← hn]; exact hcd
    push_cast at this
    have : (11 * n : ℝ) ≤ 6 * d := by linarith
    exact_mod_cast this
  exact colorable_of_regular (G := H) (by omega) (fun v => by convert hreg v) h11

/-- **Plantholt's criterion with `c* = 11/12`.** -/
theorem overfull_criterion {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : 11 * Fintype.card V ≤ 6 * (3 * G.minDegree - G.maxDegree)) :
    G.lineGraph.Colorable G.maxDegree ↔ ¬ Plantholt.HasOverfullSubgraph G := by
  refine Plantholt.theorem_1_2 (by norm_num) regularOneFactorable G hev ?_
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · have hΔ : G.maxDegree = 0 := by
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.1 h0
      exact le_antisymm (maxDegree_le_of_forall_degree_le G 0 fun v => isEmptyElim v) (by omega)
    rw [h0, hΔ]
    have := (Nat.cast_nonneg G.minDegree : (0 : ℝ) ≤ _)
    push_cast
    linarith
  · haveI : Nonempty V := Fintype.card_pos_iff.1 hpos
    have hle : G.minDegree ≤ G.maxDegree := by
      obtain ⟨v⟩ := ‹Nonempty V›
      exact (G.minDegree_le_degree v).trans (G.degree_le_maxDegree v)
    have h1 : (11 * Fintype.card V : ℝ) ≤ 6 * ((3 * G.minDegree - G.maxDegree : ℕ) : ℝ) := by
      exact_mod_cast hdeg
    rw [Nat.cast_sub (by omega)] at h1
    push_cast at h1
    linarith

end OneFactor
