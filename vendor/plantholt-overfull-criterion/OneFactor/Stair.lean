/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Chetwynd–Hilton's staircase matchings

A vertex set `HS` is split into a left side `L` (indices `1, …, m + 1`, injective) and a right side
`R` (indices `t, …, m`, injective), `t ≤ 1`. The edges kept for the staircase (`Eplus`) are those
inside `L` and those `lr` with `idx r < idx l`; the edge `uv` gets the index `stair u v`
(`idx l + idx l' − t` inside `L`, `idx l − idx r` across). Then:
* `stair_pos`, `stair_le`: indices lie in `1, …, q`, `q = 2m + 1 − t`;
* `stair_inj`: edges at a vertex have distinct indices (each index class is a matching);
* `card_cls_le`: the vertices covered by the class `i` number at most `2 (q + 2 − i)`;
* `not_cls_of_good`: in the class of `l_{m+1} y`, a vertex `x ∈ R` is uncovered if `y ∈ L`, or if
  `y ∈ R` and `idx y < idx x`.
-/

@[expose] public section

namespace OneFactor

open Finset

variable {V : Type*} [DecidableEq V]

/-- A staircase labelling of `HS`. -/
structure StairData (HS : Finset V) where
  side : V → Bool
  idx : V → ℤ
  t : ℤ
  m : ℤ
  ht : t ≤ 1
  hm : 0 ≤ m
  hL : ∀ v ∈ HS, side v = true → 1 ≤ idx v ∧ idx v ≤ m + 1
  hR : ∀ v ∈ HS, side v = false → t ≤ idx v ∧ idx v ≤ m
  injL : ∀ u ∈ HS, ∀ v ∈ HS, side u = true → side v = true → idx u = idx v → u = v
  injR : ∀ u ∈ HS, ∀ v ∈ HS, side u = false → side v = false → idx u = idx v → u = v

namespace StairData

variable {HS : Finset V} (D : StairData HS) (G : SimpleGraph V)

/-- The edges covered by the staircase. -/
def Eplus (u v : V) : Prop :=
  u ∈ HS ∧ v ∈ HS ∧ G.Adj u v ∧
    ((D.side u = true ∧ D.side v = true) ∨ (D.side u = true ∧ D.side v = false ∧ D.idx v < D.idx u) ∨
      (D.side u = false ∧ D.side v = true ∧ D.idx u < D.idx v))

/-- The staircase index of an edge. -/
def stair (u v : V) : ℤ :=
  if D.side u = true ∧ D.side v = true then D.idx u + D.idx v - D.t
  else if D.side u = true ∧ D.side v = false then D.idx u - D.idx v
  else if D.side u = false ∧ D.side v = true then D.idx v - D.idx u else 0

/-- `q = 2m + 1 − t`. -/
def q : ℤ := 2 * D.m + 1 - D.t

variable {D G}

theorem Eplus.symm {u v : V} (h : D.Eplus G u v) : D.Eplus G v u := by
  obtain ⟨hu, hv, huv, h⟩ := h
  refine ⟨hv, hu, huv.symm, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)
  · exact Or.inr (Or.inl ⟨h2, h1, h3⟩)

theorem stair_symm (u v : V) : D.stair u v = D.stair v u := by
  unfold stair
  cases hu : D.side u <;> cases hv : D.side v <;> simp <;> omega

theorem stair_pos {u v : V} (h : D.Eplus G u v) : 1 ≤ D.stair u v := by
  obtain ⟨hu, hv, huv, h⟩ := h
  have ht := D.ht
  unfold stair
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · simp only [h1, h2, and_self, if_true]
    have a := D.hL u hu h1
    have b := D.hL v hv h2
    have hne : D.idx u ≠ D.idx v := fun e => huv.ne (D.injL u hu v hv h1 h2 e)
    omega
  · simp [stair, h1, h2]; omega
  · simp [stair, h1, h2]
    omega

theorem stair_le {u v : V} (h : D.Eplus G u v) : D.stair u v ≤ D.q := by
  obtain ⟨hu, hv, huv, h⟩ := h
  have hm := D.hm
  unfold stair q
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · simp only [h1, h2, and_self, if_true]
    have a := D.hL u hu h1
    have b := D.hL v hv h2
    have hne : D.idx u ≠ D.idx v := fun e => huv.ne (D.injL u hu v hv h1 h2 e)
    omega
  · simp [stair, h1, h2]
    have a := D.hL u hu h1
    have b := D.hR v hv h2
    omega
  · simp [stair, h1, h2]
    have a := D.hR u hu h1
    have b := D.hL v hv h2
    omega

/-- **Each index class is a matching.** -/
theorem stair_inj {u v v' : V} (h : D.Eplus G u v) (h' : D.Eplus G u v')
    (he : D.stair u v = D.stair u v') : v = v' := by
  obtain ⟨hu, hv, -, h⟩ := h
  obtain ⟨-, hv', -, h'⟩ := h'
  have ht := D.ht
  cases hsu : D.side u
  · have hvL : D.side v = true := by
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩ <;> simp_all
    have hvL' : D.side v' = true := by
      rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩ <;> simp_all
    simp [stair, hsu, hvL, hvL'] at he
    exact D.injL v hv v' hv' hvL hvL' (by omega)
  · cases hsv : D.side v <;> cases hsv' : D.side v' <;> simp [stair, hsu, hsv, hsv'] at he <;>
      first
      | exact D.injR v hv v' hv' hsv hsv' (by omega)
      | exact D.injL v hv v' hv' hsv hsv' (by omega)
      | (have := D.hR v hv hsv; have := D.hL v' hv' hsv'; omega)
      | (have := D.hL v hv hsv; have := D.hR v' hv' hsv'; omega)

variable (D G) in
/-- The vertices covered by the class `i`. -/
noncomputable def cls (i : ℤ) : Finset V := by
  classical
  exact HS.filter fun v => ∃ u, D.Eplus G v u ∧ D.stair v u = i

variable (D G) in
theorem mem_cls {i : ℤ} {v : V} : v ∈ D.cls G i ↔ v ∈ HS ∧ ∃ u, D.Eplus G v u ∧ D.stair v u = i := by
  classical
  unfold cls
  rw [mem_filter]

/-- **The class `i` covers at most `2 (q + 2 − i)` vertices.** -/
theorem card_cls_le {i : ℤ} (hi : i ≤ D.q + 2) : ((#(D.cls G i) : ℕ) : ℤ) ≤ 2 * (D.q + 2 - i) := by
  classical
  set A := (D.cls G i).filter fun v => D.side v = true
  set B := (D.cls G i).filter fun v => D.side v = false
  have hAB : #(D.cls G i) = #A + #B := by
    rw [← card_filter_add_card_filter_not (p := fun v => D.side v = true)]
    congr 2
  -- the left part sits in an interval of indices
  have hA : ((#A : ℕ) : ℤ) ≤ D.q + 2 - i := by
    have hsub : ∀ v ∈ A, D.idx v ∈ Finset.Icc (i + D.t - D.m - 1) (D.m + 1) := by
      intro v hv
      obtain ⟨hvc, hvL⟩ := mem_filter.1 hv
      obtain ⟨hvH, u, hu, hst⟩ := (mem_cls _ _).1 hvc
      have := D.hL v hvH hvL
      rw [Finset.mem_Icc]
      refine ⟨?_, this.2⟩
      obtain ⟨-, huH, -, h⟩ := hu
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · simp [stair, h1, h2] at hst
        have := D.hL u huH h2
        omega
      · simp [stair, h1, h2] at hst
        have := D.hR u huH h2
        have := D.hm
        omega
      · rw [hvL] at h1; exact absurd h1 (by simp)
    have hAH : ∀ v ∈ A, v ∈ HS := fun v hv => ((mem_cls _ _).1 (mem_filter.1 hv).1).1
    have hinj : Set.InjOn D.idx A := fun a ha b hb e =>
      D.injL a (hAH a ha) b (hAH b hb) (mem_filter.1 ha).2 (mem_filter.1 hb).2 e
    have := card_le_card_of_injOn D.idx (fun v hv => hsub v hv) hinj
    rw [Int.card_Icc] at this
    have hq : D.q = 2 * D.m + 1 - D.t := rfl
    have e := Int.toNat_of_nonneg (show (0 : ℤ) ≤ D.m + 1 + 1 - (i + D.t - D.m - 1) by omega)
    omega
  -- the right part injects into the left part
  have hB : #B ≤ #A := by
    have hpart : ∀ v ∈ B, ∃ u ∈ A, D.Eplus G v u ∧ D.stair v u = i := by
      intro v hv
      obtain ⟨hvc, hvR⟩ := mem_filter.1 hv
      obtain ⟨hvH, u, hu, hst⟩ := (mem_cls _ _).1 hvc
      have huL : D.side u = true := by
        obtain ⟨-, -, -, h⟩ := hu
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩
        · rw [hvR] at h1; exact absurd h1 (by simp)
        · rw [hvR] at h1; exact absurd h1 (by simp)
        · exact h2
      refine ⟨u, mem_filter.2 ⟨(mem_cls _ _).2 ⟨hu.2.1, v, hu.symm,
        (stair_symm u v).trans hst⟩, huL⟩, hu, hst⟩
    choose! f hfA hf using hpart
    refine card_le_card_of_injOn f (fun v hv => hfA v hv) fun a ha b hb e => ?_
    have h1 := (hf a ha).1.symm
    have h2 := (hf b hb).1.symm
    rw [e] at h1
    refine stair_inj h1 h2 ?_
    rw [← e, stair_symm, (hf a ha).2, stair_symm, e, (hf b hb).2]
  push_cast [hAB]
  omega

/-- **The good pairs.** In the class of `v* y` (`v* ∈ L` of index `m + 1`), a vertex `x ∈ R`
is uncovered if `y ∈ L`, or if `y ∈ R` and `idx y < idx x`. -/
theorem not_cls_of_good {vs y x : V} (hvs : vs ∈ HS) (hvsL : D.side vs = true)
    (hvsi : D.idx vs = D.m + 1) (hy : D.Eplus G vs y) (hx : x ∈ HS) (hxR : D.side x = false)
    (hgood : D.side y = true ∨ D.idx y < D.idx x) : x ∉ D.cls G (D.stair vs y) := by
  intro hcls
  obtain ⟨-, u, hu, hst⟩ := (mem_cls _ _).1 hcls
  obtain ⟨-, huH, -, h⟩ := hu
  have huL : D.side u = true ∧ D.idx x < D.idx u := by
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, h3⟩
    · rw [hxR] at h1; exact absurd h1 (by simp)
    · rw [hxR] at h1; exact absurd h1 (by simp)
    · exact ⟨h2, h3⟩
  have hu' := D.hL u huH huL.1
  have hx' := D.hR x hx hxR
  have hyH := hy.2.1
  rcases hgood with hyL | hlt
  · simp [stair, hxR, huL.1, hvsL, hyL] at hst
    have := D.hL y hyH hyL
    omega
  · cases hyS : D.side y
    · simp [stair, hxR, huL.1, hvsL, hyS] at hst
      omega
    · simp [stair, hxR, huL.1, hvsL, hyS] at hst
      have := D.hL y hyH hyS
      omega

end StairData

end OneFactor
