/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V35.Gauge

/-!
# Gauge lemma with the radius bound discharged from cardinality and degree (V35, layer 2)

Hypotheses: `LinkMatrix B`, `|R| ≤ N`, `1 ≤ m`, every unanchored row has at least `m` distinct
neighbours in `linkGraph B`, `|(Bᵀ t) e| ≤ L` for every column, `0 ≤ L`.

* `anch_radius`, `free_radius` (ball form) and `anch_dist_bound`, `free_diam_bound`
  (`SimpleGraph.dist` form): radius `K = 3 * (N / m)` around the anchors in anchored components;
  diameter `≤ 3 * (N / m)` in anchor-free components.
* `gauge_bound_subgroup`: some `t'` with `Bᵀ t' = Bᵀ t`, `|t' i| ≤ (6 (N / m) + 1) L`, and
  `2 t' i ∈ A` for any additive subgroup `A` containing all data.
* `gauge_bound`: the real statement (`A = ⊤`).
* `gauge_bound_requested_constant`: the bound `(3 D + 2) L` with `D = ⌈3 N / m⌉₊ + 5`.
* `gauge_bound_eighth`: quarter-integer data ⇒ eighth-integer `t'`, same bound.
* `colDeg`, `SimpleCols`, `colDeg_le_card_nbrs`, `gauge_bound_colDeg`: degree measured by
  counting two-entry columns at a row; simplicity of the column graph converts this count into a
  count of distinct neighbours. `parallel_colDeg`, `parallel_card_nbrs`, `parallel_not_simple`:
  without simplicity the column count (2) exceeds the number of distinct neighbours (1).
-/

@[expose] public section

namespace S07V35

open Finset

variable {R E : Type*} [Fintype R] [DecidableEq R] [Fintype E] {B : R → E → ℤ}

omit [Fintype E] in
/-- Anchored components lie in the radius-`3 (N / m)` ball of the anchors. -/
theorem anch_radius {m N : ℕ} (hm : 0 < m) (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card) :
    ∀ x, AnchComp B x → x ∈ ball (linkGraph B) (anchors B) (3 * (N / m)) := by
  classical
  have stall := ball_stall (linkGraph B) (S := anchors B) hm hN
    (fun _ x _ hxS => hdeg x (fun hx => hxS (by simpa [anchors] using hx)))
  rintro x ⟨a, ha, hr⟩
  exact mem_ball_of_stall _ stall (subset_ball _ _ _ (by simpa [anchors] using ha)) hr

omit [Fintype E] in
/-- In an anchor-free component, every vertex is within the radius-`3 (N / m)` ball of every
other vertex. -/
theorem free_radius {m N : ℕ} (hm : 0 < m) (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card) :
    ∀ x y, ¬ AnchComp B x → (linkGraph B).Reachable x y →
      y ∈ ball (linkGraph B) {x} (3 * (N / m)) := by
  intro x y hx hxy
  have stall := ball_stall (linkGraph B) (S := {x}) hm hN (by
    intro k z hz _
    apply hdeg z
    intro hza
    obtain ⟨w, hw, hwz⟩ := reachable_of_mem_ball _ hz
    rw [mem_singleton] at hw
    subst hw
    exact hx ⟨z, hza, hwz.symm⟩)
  exact mem_ball_of_stall _ stall (subset_ball _ _ _ (mem_singleton_self x)) hxy

omit [Fintype E] in
/-- **Distance bound (discharged).** Every vertex of a component containing an anchor is within
graph distance `3 (N / m)` of some anchor. -/
theorem anch_dist_bound {m N : ℕ} (hm : 0 < m) (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card) :
    ∀ x, AnchComp B x → ∃ a, Anchored B a ∧ (linkGraph B).Reachable a x ∧
      (linkGraph B).dist a x ≤ 3 * (N / m) := by
  classical
  intro x hx
  obtain ⟨a, ha, p, hp⟩ := exists_walk_of_mem_ball _ (anch_radius hm hN hdeg x hx)
  exact ⟨a, by simpa [anchors] using ha, p.reachable, (SimpleGraph.dist_le p).trans hp⟩

omit [Fintype E] in
/-- **Diameter bound (discharged).** Any two vertices of an anchor-free component are within
graph distance `3 (N / m)`. -/
theorem free_diam_bound {m N : ℕ} (hm : 0 < m) (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card) :
    ∀ x y, ¬ AnchComp B x → (linkGraph B).Reachable x y →
      (linkGraph B).dist x y ≤ 3 * (N / m) := by
  intro x y hx hxy
  obtain ⟨w, hw, p, hp⟩ := exists_walk_of_mem_ball _ (free_radius hm hN hdeg x y hx hxy)
  rw [mem_singleton] at hw
  subst hw
  exact (SimpleGraph.dist_le p).trans hp

/-- **Gauge lemma (layer 2), with an arbitrary data subgroup `A`.** -/
theorem gauge_bound_subgroup (hB : LinkMatrix B) {m N : ℕ} (hm : 1 ≤ m)
    (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card)
    (t : R → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : ∀ e, |dat B t e| ≤ L)
    (A : AddSubgroup ℝ) (hA : ∀ e, dat B t e ∈ A) :
    ∃ t' : R → ℝ, (∀ e, dat B t' e = dat B t e) ∧
      (∀ i, |t' i| ≤ ((6 * (N / m) + 1 : ℕ) : ℝ) * L) ∧ ∀ i, 2 * t' i ∈ A := by
  obtain ⟨t', h1, h2, h3⟩ := gauge_of_dist hB t L hL hd A hA (3 * (N / m))
    (anch_dist_bound hm hN hdeg) (free_diam_bound hm hN hdeg)
  refine ⟨t', h1, fun i => ?_, h3⟩
  have := h2 i
  push_cast at this ⊢
  linarith

/-- **Gauge lemma (layer 2).** Signed link matrix, `|R| ≤ N`, every unanchored row has at least
`m ≥ 1` distinct neighbours, `|(Bᵀ t) e| ≤ L`. Then some `t'` has `Bᵀ t' = Bᵀ t` and
`|t' i| ≤ (6 ⌊N / m⌋ + 1) L` for every row. The bound does not depend on `|E|` or on `t`. -/
theorem gauge_bound (hB : LinkMatrix B) {m N : ℕ} (hm : 1 ≤ m) (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card)
    (t : R → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : ∀ e, |dat B t e| ≤ L) :
    ∃ t' : R → ℝ, (∀ e, dat B t' e = dat B t e) ∧
      ∀ i, |t' i| ≤ ((6 * (N / m) + 1 : ℕ) : ℝ) * L := by
  obtain ⟨t', h1, h2, -⟩ := gauge_bound_subgroup hB hm hN hdeg t L hL hd ⊤ (fun _ => trivial)
  exact ⟨t', h1, h2⟩

/-- The constant `6 ⌊N/m⌋ + 1` is at most `3 D + 2` with `D = ⌈3 N / m⌉₊ + 5`. -/
theorem const_le_requested (m N : ℕ) :
    ((6 * (N / m) + 1 : ℕ) : ℝ) ≤ 3 * ((⌈(3 * N : ℝ) / m⌉₊ + 5 : ℕ) : ℝ) + 2 := by
  have h1 : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have h2 : (3 * N : ℝ) / m ≤ (⌈(3 * N : ℝ) / m⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : (3 * N : ℝ) / m = 3 * ((N : ℝ) / m) := by ring
  have h4 : (0 : ℝ) ≤ ((N / m : ℕ) : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- **Gauge lemma with the requested constant**: `|t' i| ≤ (3 D + 2) L`,
`D = ⌈3 N / m⌉₊ + 5`. -/
theorem gauge_bound_requested_constant (hB : LinkMatrix B) {m N : ℕ} (hm : 1 ≤ m)
    (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card)
    (t : R → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : ∀ e, |dat B t e| ≤ L) :
    ∃ t' : R → ℝ, (∀ e, dat B t' e = dat B t e) ∧
      ∀ i, |t' i| ≤ (3 * ((⌈(3 * N : ℝ) / m⌉₊ + 5 : ℕ) : ℝ) + 2) * L := by
  obtain ⟨t', h1, h2⟩ := gauge_bound hB hm hN hdeg t L hL hd
  exact ⟨t', h1, fun i => (h2 i).trans (mul_le_mul_of_nonneg_right (const_le_requested m N) hL)⟩

/-- **Discrete refinement.** If all data are quarter-integers, `t'` can be chosen with
eighth-integer coordinates, with the same bound. -/
theorem gauge_bound_eighth (hB : LinkMatrix B) {m N : ℕ} (hm : 1 ≤ m) (hN : Fintype.card R ≤ N)
    (hdeg : ∀ i, ¬ Anchored B i → m ≤ (nbrs (linkGraph B) i).card)
    (t : R → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : ∀ e, |dat B t e| ≤ L)
    (hq : ∀ e, ∃ n : ℤ, dat B t e = n / 4) :
    ∃ t' : R → ℝ, (∀ e, dat B t' e = dat B t e) ∧
      (∀ i, |t' i| ≤ ((6 * (N / m) + 1 : ℕ) : ℝ) * L) ∧ ∀ i, ∃ n : ℤ, t' i = n / 8 := by
  obtain ⟨t', h1, h2, h3⟩ := gauge_bound_subgroup hB hm hN hdeg t L hL hd
    (AddSubgroup.zmultiples (1 / 4 : ℝ)) (by
      intro e
      obtain ⟨n, hn⟩ := hq e
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨n, by rw [hn, zsmul_eq_mul]; ring⟩)
  refine ⟨t', h1, h2, fun i => ?_⟩
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (h3 i)
  rw [zsmul_eq_mul] at hn
  exact ⟨n, by linarith⟩

/-! ## Degree counted by columns: where simplicity is indispensable -/

/-- Number of two-entry columns meeting row `i` (a weighted degree; parallel columns count
separately). -/
noncomputable def colDeg (B : R → E → ℤ) (i : R) : ℕ := by
  classical exact (univ.filter (fun e => (supp B e).card = 2 ∧ B i e ≠ 0)).card

/-- Simplicity: no two distinct two-entry columns have the same (unordered) pair of rows. -/
def SimpleCols (B : R → E → ℤ) : Prop :=
  ∀ e e', (supp B e).card = 2 → supp B e' = supp B e → e = e'

/-- Under simplicity, the column count at a row is at most the number of distinct
neighbours (in fact equal). -/
theorem colDeg_le_card_nbrs (hB : LinkMatrix B) (hs : SimpleCols B) (i : R) :
    colDeg B i ≤ (nbrs (linkGraph B) i).card := by
  classical
  unfold colDeg
  have hex : ∀ e ∈ univ.filter (fun e => (supp B e).card = 2 ∧ B i e ≠ 0),
      ∃ j, j ≠ i ∧ B j e ≠ 0 := by
    intro e he
    obtain ⟨h2, -⟩ := (mem_filter.1 he).2
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega : 1 < (supp B e).card) i
    exact ⟨j, hji, (mem_filter.1 hj).2⟩
  let f : E → R := fun e => if h : ∃ j, j ≠ i ∧ B j e ≠ 0 then h.choose else i
  have hf : ∀ e ∈ univ.filter (fun e => (supp B e).card = 2 ∧ B i e ≠ 0),
      f e ≠ i ∧ B (f e) e ≠ 0 := by
    intro e he
    have h := hex e he
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro e he
    have he' : e ∈ univ.filter (fun e => (supp B e).card = 2 ∧ B i e ≠ 0) := he
    obtain ⟨hne, hfe⟩ := hf e he'
    simp only [nbrs, coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
    exact ⟨hne.symm, e, (mem_filter.1 he').2.2, hfe⟩
  · intro e1 he1 e2 he2 heq
    have he1' : e1 ∈ univ.filter (fun e => (supp B e).card = 2 ∧ B i e ≠ 0) := he1
    have he2' : e2 ∈ univ.filter (fun e => (supp B e).card = 2 ∧ B i e ≠ 0) := he2
    obtain ⟨hn1, hb1⟩ := hf e1 he1'
    obtain ⟨hn2, hb2⟩ := hf e2 he2'
    have s1 := supp_pair hB hn1.symm (mem_filter.1 he1').2.2 hb1
    have s2 := supp_pair hB hn2.symm (mem_filter.1 he2').2.2 hb2
    rw [← heq] at s2
    exact hs e1 e2 (mem_filter.1 he1').2.1 (s2.trans s1.symm)

/-- **Gauge lemma, column-count degree.** Same as `gauge_bound`, with the degree hypothesis
stated as "every unanchored row meets at least `m` two-entry columns" together with simplicity
of the column graph. -/
theorem gauge_bound_colDeg (hB : LinkMatrix B) (hs : SimpleCols B) {m N : ℕ} (hm : 1 ≤ m)
    (hN : Fintype.card R ≤ N) (hcol : ∀ i, ¬ Anchored B i → m ≤ colDeg B i)
    (t : R → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : ∀ e, |dat B t e| ≤ L) :
    ∃ t' : R → ℝ, (∀ e, dat B t' e = dat B t e) ∧
      ∀ i, |t' i| ≤ ((6 * (N / m) + 1 : ℕ) : ℝ) * L :=
  gauge_bound hB hm hN (fun i hi => (hcol i hi).trans (colDeg_le_card_nbrs hB hs i)) t L hL hd

/-- Two parallel columns on the two rows of `Fin 2`. -/
def parallelB : Fin 2 → Fin 2 → ℤ := fun _ _ => 1

theorem parallel_supp (e : Fin 2) : supp parallelB e = univ := by
  ext i; simp [supp, parallelB]

theorem parallel_colDeg : colDeg parallelB 0 = 2 := by
  classical
  unfold colDeg
  simp [parallel_supp, parallelB]

theorem parallel_card_nbrs : (nbrs (linkGraph parallelB) 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext j
  fin_cases j <;> simp [nbrs, linkGraph, parallelB]

theorem parallel_not_simple : ¬ SimpleCols parallelB := by
  intro h
  have := h 0 1 (by simp [parallel_supp]) (by simp [parallel_supp])
  exact absurd this (by decide)

end S07V35
