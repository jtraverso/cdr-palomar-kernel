/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.SeedCounts
public import CDRBicolour.Absorption.Extremes.Lattice5

/-!
# The count seed for the five-type host (item 3, extremes)

`seedN_edge`: the type-uniform count seed has incidence exactly `1` on every edge, for every
`t` (only admissibility is used).  `seed5_bounds`: for `F5`-allowed triangles it is diffuse as soon
as `t ≥ 0` and the five non-`AAC` counts are at least `ε n²`.  At `t = 0` it gives no weight to
`AAC` triangles, so it is an exact seed of the five-type host (`seed5_exact`).
-/

@[expose] public section

namespace CDRBicolour.Absorption.Extremes

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

set_option maxHeartbeats 1600000 in
/-- The count seed has incidence `1` on every edge. -/
theorem seedN_edge {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) (t : ℝ)
    (e : Sym2 (Fin (a + b + c))) (he : e ∈ (cdrHost a b c).G.edgeSet) :
    ∑ T ∈ (allowed (cdrHost a b c) cdrF).filter (fun T => e ∈ triEdges T),
      wtN a b c t (T.val.map (col3 a b c)) = 1 := by
  classical
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h hn
  have hadmZ := h.2.2.2.2.1
  have hadm : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 - a * b - a * c - b * c = a + b + c := by
    exact_mod_cast hadmZ
  have hN : (400 : ℝ) ≤ a + b + c := by exact_mod_cast hn
  have ha : (a : ℝ) + b + c + 8 ≤ 4 * a := by exact_mod_cast ha4
  have hb : (a : ℝ) + b + c + 8 ≤ 4 * b := by exact_mod_cast hb4
  have hc : (a : ℝ) + b + c + 8 ≤ 4 * c := by exact_mod_cast hc4
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hcard : (Fintype.card (Fin (a + b + c)) : ℝ) = a + b + c := by simp
  have hnn : (((a + b + c : ℕ) : ℝ)) = a + b + c := by push_cast; ring
  have hA1 : (a : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hB1 : (b : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hC1 : (c : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hA : (a : ℝ) ≠ 0 := by intro h'; linarith
  have hB : (b : ℝ) ≠ 0 := by intro h'; linarith
  have hC : (c : ℝ) ≠ 0 := by intro h'; linarith
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := he
  simp only [cdrHost]
  rw [edge_sum_top' (col3 a b c) cdrF (wtN a b c t) huv _ ?hS]
  case hS =>
    intro T
    convert (mem_filter (s := allowed (⟨⊤, col3 a b c⟩ : Host (Fin (a + b + c)) (Fin 3)) cdrF)
      (p := fun T => s(u, v) ∈ triEdges T) (a := T))
  rw [sum_by_label (col3 a b c) (fun k => ({col3 a b c u, col3 a b c v, k} :
    Multiset (Fin 3)) ∈ cdrF) (fun k => wtN a b c t {col3 a b c u, col3 a b c v, k})]
  simp only [card_third (col3 a b c) huv, card_class, Fin.sum_univ_three]
  generalize col3 a b c u = i
  generalize col3 a b c v = j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [cdrF, wtN, cntAAB, cntAAC, cntBBC, cntABB, cntACC,
      cntBCC, ch] <;>
    field_simp <;> ring_nf <;> nlinarith [hadm]


set_option maxHeartbeats 1600000 in
/-- Bounds of the count seed on the `F5` triangles. -/
theorem seed5_bounds {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c)
    {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t)
    (h1 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntAAB a b c t)
    (h3 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntBBC a b c t)
    (h4 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntABB a b c t)
    (h5 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntACC a b c t)
    (h6 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntBCC a b c t) (T : Finset (Fin (a + b + c)))
    (hT : IsAllowed (cdrHost a b c) F5 T) :
    1 / ((64 + 1 / ε) * Fintype.card (Fin (a + b + c))) ≤ wtN a b c t (T.val.map (col3 a b c)) ∧
      wtN a b c t (T.val.map (col3 a b c)) ≤ (64 + 1 / ε) / Fintype.card (Fin (a + b + c)) := by
  classical
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h hn
  have hadmZ := h.2.2.2.2.1
  have hadm : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 - a * b - a * c - b * c = a + b + c := by
    exact_mod_cast hadmZ
  have hN : (400 : ℝ) ≤ a + b + c := by exact_mod_cast hn
  have ha : (a : ℝ) + b + c + 8 ≤ 4 * a := by exact_mod_cast ha4
  have hb : (a : ℝ) + b + c + 8 ≤ 4 * b := by exact_mod_cast hb4
  have hc : (a : ℝ) + b + c + 8 ≤ 4 * c := by exact_mod_cast hc4
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hcard : (Fintype.card (Fin (a + b + c)) : ℝ) = a + b + c := by simp
  have hnn : (((a + b + c : ℕ) : ℝ)) = a + b + c := by push_cast; ring
  rw [hnn] at h1 h3 h4 h5 h6
  have hA1 : (a : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hB1 : (b : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hC1 : (c : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hA : (a : ℝ) ≠ 0 := by intro h'; linarith
  have hB : (b : ℝ) ≠ 0 := by intro h'; linarith
  have hC : (c : ℝ) ≠ 0 := by intro h'; linarith
  have hC64 : (64 : ℝ) ≤ 64 + 1 / ε := le_add_of_nonneg_right (by positivity)
  have hCε : 1 ≤ (64 + 1 / ε) * ε := by
    rw [add_mul, one_div, inv_mul_cancel₀ hε.ne']; nlinarith
  set n : ℝ := (a : ℝ) + b + c with hn_def
  have hn0 : 0 < n := by linarith
  -- the six counts are at most `n²/2`
  have hεn : 0 ≤ ε * n ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 1 ≤ x → x ≤ n → ch x ≤ n ^ 2 / 2 := by
    intro x hx1 hxn
    unfold ch
    have := mul_le_mul hxn (show x - 1 ≤ n by linarith) (by linarith) (by linarith)
    nlinarith
  have hchA : ch a ≤ n ^ 2 / 2 := hsq a (by linarith) (by linarith)
  have hchB : ch b ≤ n ^ 2 / 2 := hsq b (by linarith) (by linarith)
  have hchC : ch c ≤ n ^ 2 / 2 := hsq c (by linarith) (by linarith)
  have u1 := h1; have u2 : (0 : ℝ) ≤ t := ht0; have u3 := h3; have u4 := h4; have u5 := h5; have u6 := h6
  simp only [cntAAB, cntAAC, cntBBC, cntABB, cntACC, cntBCC] at u1 u2 u3 u4 u5 u6
  have hab : (a : ℝ) * b / 2 ≤ n ^ 2 / 2 := by nlinarith
  have hac : (a : ℝ) * c / 2 ≤ n ^ 2 / 2 := by nlinarith
  have hbc : (b : ℝ) * c / 2 ≤ n ^ 2 / 2 := by nlinarith
  rw [hcard]
  beta_reduce
  have hm : T.val.map (col3 a b c) ∈ cdrF := hT.2.2.1
  rcases type_cases hm with ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ |
    ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩
  · have hw : wtN a b c t (T.val.map (col3 a b c)) = cntAAB a b c t / (ch a * b) := by
      simp [wtN, h0', h1']
    rw [hw]
    obtain ⟨hT1, hT2⟩ := tri_bounds (n := n) ha hb (by linarith) (by linarith) hn0
    refine ratio_bounds hn0 hε h1 ?_ hT1 hT2 hC64 hCε
    unfold cntAAB; linarith [u1, u2, u3, u4, u5, u6, hab, hac, hbc, hchA, hchB, hchC, hεn]
  · exfalso; apply hT.2.2.2
    show T.val.map (col3 a b c) = aac
    ext k; fin_cases k <;> simp [aac, h0', h1', h2']
  · have hw : wtN a b c t (T.val.map (col3 a b c)) = cntBBC a b c t / (ch b * c) := by
      simp [wtN, h0', h1', h2']
    rw [hw]
    obtain ⟨hT1, hT2⟩ := tri_bounds (n := n) hb hc (by linarith) (by linarith) hn0
    refine ratio_bounds hn0 hε h3 ?_ hT1 hT2 hC64 hCε
    unfold cntBBC; linarith [u1, u2, u3, u4, u5, u6, hab, hac, hbc, hchA, hchB, hchC, hεn]
  · have hw : wtN a b c t (T.val.map (col3 a b c)) = cntABB a b c t / (a * ch b) := by
      simp [wtN, h0', h1', h2']
    rw [hw, mul_comm (a : ℝ) (ch b)]
    obtain ⟨hT1, hT2⟩ := tri_bounds (n := n) hb ha (by linarith) (by linarith) hn0
    refine ratio_bounds hn0 hε h4 ?_ hT1 hT2 hC64 hCε
    unfold cntABB; linarith [u1, u2, u3, u4, u5, u6, hab, hac, hbc, hchA, hchB, hchC, hεn]
  · have hw : wtN a b c t (T.val.map (col3 a b c)) = cntACC a b c t / (a * ch c) := by
      simp [wtN, h0', h1', h2']
    rw [hw, mul_comm (a : ℝ) (ch c)]
    obtain ⟨hT1, hT2⟩ := tri_bounds (n := n) hc ha (by linarith) (by linarith) hn0
    refine ratio_bounds hn0 hε h5 ?_ hT1 hT2 hC64 hCε
    unfold cntACC; linarith [u1, u2, u3, u4, u5, u6, hab, hac, hbc, hchA, hchB, hchC, hεn]
  · have hw : wtN a b c t (T.val.map (col3 a b c)) = cntBCC a b c t / (b * ch c) := by
      simp [wtN, h0', h1', h2']
    rw [hw, mul_comm (b : ℝ) (ch c)]
    obtain ⟨hT1, hT2⟩ := tri_bounds (n := n) hc hb (by linarith) (by linarith) hn0
    refine ratio_bounds hn0 hε h6 ?_ hT1 hT2 hC64 hCε
    unfold cntBCC; linarith [u1, u2, u3, u4, u5, u6, hab, hac, hbc, hchA, hchB, hchC, hεn]

end CDRBicolour.Absorption.Extremes
