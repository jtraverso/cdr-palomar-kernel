/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Host

/-!
# A one-parameter family of diffuse seeds for the CDR host

The six edge equations of a type-uniform seed (weights `x_AAB, …, x_BCC`) have a one-dimensional
kernel, spanned by `dir`:

  `AAB: 1/b`, `AAC: -1/c`, `BBC: r/c`, `ABB: -r/a`, `ACC: r'/a`, `BCC: -r'/b`,

with `r = a(a-1)/(b(b-1))` and `r' = a(a-1)/(c(c-1))`.  Hence `wtS s = wt + s · dir` is again an
exact fractional decomposition, and for `|s| ≤ 1/32` it is a diffuse seed with constant `8`
(`cdr_H1_family`).  Its total weight on `AAC` triangles is `(1/2 - σ_A - s) · C(a,2)`, so `s`
steers the expected number of `AAC` blocks over an interval of length `C(a,2)/16`.
-/

@[expose] public section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-- The kernel direction of the six edge equations. -/
noncomputable def dir (a b c : ℝ) (m : Multiset (Fin 3)) : ℝ :=
  if m.count 0 = 2 ∧ m.count 1 = 1 then 1 / b
  else if m.count 0 = 2 ∧ m.count 2 = 1 then -(1 / c)
  else if m.count 1 = 2 ∧ m.count 2 = 1 then a * (a - 1) / (b * (b - 1)) / c
  else if m.count 1 = 2 ∧ m.count 0 = 1 then -(a * (a - 1) / (b * (b - 1))) / a
  else if m.count 2 = 2 ∧ m.count 0 = 1 then a * (a - 1) / (c * (c - 1)) / a
  else if m.count 2 = 2 ∧ m.count 1 = 1 then -(a * (a - 1) / (c * (c - 1))) / b
  else 0

/-- The perturbed type weight. -/
noncomputable def wtS (a b c s : ℝ) (m : Multiset (Fin 3)) : ℝ := wt a b c m + s * dir a b c m

/-- A weight between `1/(8N)` and `8/N`. -/
theorem wbound8 {Y N s : ℝ} (hY : N + 8 ≤ 4 * Y) (hYN : Y ≤ N) (hs : |s| ≤ 3 / 8) :
    1 / (8 * N) ≤ (1 / 2 + s) / Y ∧ (1 / 2 + s) / Y ≤ 8 / N := by
  rw [abs_le] at hs
  have hY0 : 0 < Y := by linarith
  have hN0 : 0 < N := by linarith
  constructor
  · rw [div_le_div_iff₀ (by positivity) hY0]; nlinarith
  · rw [div_le_div_iff₀ hY0 hN0]; nlinarith

/-- The ratio of pair counts of two classes is at most `4`. -/
theorem ratio_abs {x y z : ℝ} (hy : x + y + z + 8 ≤ 4 * y) (hz : x + y + z + 8 ≤ 4 * z)
    (hx : x + y + z + 8 ≤ 4 * x) : |x * (x - 1) / (y * (y - 1))| ≤ 4 := by
  have hx1 : 0 ≤ x * (x - 1) := by nlinarith
  have hy1 : 0 < y * (y - 1) := by nlinarith
  rw [abs_of_nonneg (div_nonneg hx1 hy1.le), div_le_iff₀ hy1]
  nlinarith

theorem small_mul {s r : ℝ} (hs : |s| ≤ 1 / 32) (hr : |r| ≤ 4) : |s * r| ≤ 1 / 8 := by
  rw [abs_mul]
  calc |s| * |r| ≤ 1 / 32 * 4 := mul_le_mul hs hr (abs_nonneg _) (by norm_num)
    _ = 1 / 8 := by norm_num

theorem add_small {x y : ℝ} (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 8) : |x + y| ≤ 3 / 8 := by
  calc |x + y| ≤ |x| + |y| := abs_add_le _ _
    _ ≤ 3 / 8 := by linarith

/-- **H1 for the seed family**: for `|s| ≤ 1/32`, `wtS s` is a diffuse seed with `C = 8`. -/
theorem cdr_H1_family {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c)
    {s : ℝ} (hs : |s| ≤ 1 / 32) :
    IsDiffuseSeed (cdrHost a b c) cdrF 8
      (fun T => wtS a b c s (T.val.map (col3 a b c))) := by
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
  have hsA : |sigA a c| ≤ 1 / 4 := sig_bound hadm hN ha hb0 hc0
  have hsB : |sigB b c| ≤ 1 / 4 := by
    unfold sigB
    rw [neg_div, abs_neg, show ((b : ℝ) - c) ^ 2 - b - c = (c - b) ^ 2 - c - b by ring]
    exact sig_bound (a := (b : ℝ)) (b := (a : ℝ)) (c := (c : ℝ)) (by linear_combination hadm)
      (by linarith) (by linarith) ha0 hc0
  have hr : |(a : ℝ) * (a - 1) / (b * (b - 1))| ≤ 4 :=
    ratio_abs (z := (c : ℝ)) (by linarith) (by linarith) (by linarith)
  have hr' : |(a : ℝ) * (a - 1) / (c * (c - 1))| ≤ 4 :=
    ratio_abs (z := (b : ℝ)) (by linarith) (by linarith) (by linarith)
  have hsr := small_mul hs hr
  have hsr' := small_mul hs hr'
  have hs8 : |s| ≤ 1 / 8 := by linarith
  have hcard : (Fintype.card (Fin (a + b + c)) : ℝ) = a + b + c := by simp
  have hA1 : (a : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hB1 : (b : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hC1 : (c : ℝ) - 1 ≠ 0 := by intro h'; linarith
  have hA : (a : ℝ) ≠ 0 := by intro h'; linarith
  have hB : (b : ℝ) ≠ 0 := by intro h'; linarith
  have hC : (c : ℝ) ≠ 0 := by intro h'; linarith
  let N_le : ℝ → Prop := fun Y => (a : ℝ) + b + c + 8 ≤ 4 * Y ∧ Y ≤ (a : ℝ) + b + c
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · -- bounds
    rw [hcard]
    have hm : T.val.map (col3 a b c) ∈ cdrF := hT.2.2
    have key : ∀ (x : ℝ) (Y : ℝ), N_le Y → wtS a b c s (T.val.map (col3 a b c)) = (1 / 2 + x) / Y →
        |x| ≤ 3 / 8 → (1 / (8 * ((a : ℝ) + b + c)) ≤ wtS a b c s (T.val.map (col3 a b c)) ∧
          wtS a b c s (T.val.map (col3 a b c)) ≤ 8 / ((a : ℝ) + b + c)) := by
      intro x Y hY hw hx; rw [hw]; exact wbound8 hY.1 hY.2 hx
    rcases type_cases hm with ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ |
      ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩
    · refine key (sigA a c + s) b ⟨hb, by linarith⟩ ?_ (add_small hsA (by linarith))
      simp [wtS, wt, dir, h0', h1', h2'] <;> field_simp <;> ring
    · refine key (-sigA a c + -s) c ⟨hc, by linarith⟩ ?_
        (add_small (by rwa [abs_neg]) (by rw [abs_neg]; linarith))
      simp [wtS, wt, dir, h0', h1', h2'] <;> field_simp <;> ring
    · refine key (sigB b c + s * ((a : ℝ) * (a - 1) / (b * (b - 1)))) c ⟨hc, by linarith⟩ ?_
        (add_small hsB hsr)
      simp [wtS, wt, dir, h0', h1', h2'] <;> field_simp <;> ring
    · refine key (-sigB b c + -(s * ((a : ℝ) * (a - 1) / (b * (b - 1))))) a ⟨ha, by linarith⟩ ?_
        (add_small (by rwa [abs_neg]) (by rwa [abs_neg]))
      simp [wtS, wt, dir, h0', h1', h2'] <;> field_simp <;> ring
    · refine key (0 + s * ((a : ℝ) * (a - 1) / (c * (c - 1)))) a ⟨ha, by linarith⟩ ?_
        (add_small (by simp) hsr')
      simp [wtS, wt, dir, h0', h1', h2'] <;> field_simp <;> ring
    · refine key (0 + -(s * ((a : ℝ) * (a - 1) / (c * (c - 1))))) b ⟨hb, by linarith⟩ ?_
        (add_small (by simp) (by rwa [abs_neg]))
      simp [wtS, wt, dir, h0', h1', h2'] <;> field_simp <;> ring
  · -- edge sums
    induction e using Sym2.ind with
    | _ u v =>
    have huv : u ≠ v := he
    simp only [cdrHost]
    rw [edge_sum_top' (col3 a b c) cdrF (wtS a b c s) huv _ ?hS]
    case hS =>
      intro T
      convert (mem_filter (s := allowed (⟨⊤, col3 a b c⟩ : Host (Fin (a + b + c)) (Fin 3)) cdrF)
        (p := fun T => s(u, v) ∈ triEdges T) (a := T))
    rw [sum_by_label (col3 a b c) (fun k => ({col3 a b c u, col3 a b c v, k} :
      Multiset (Fin 3)) ∈ cdrF) (fun k => wtS a b c s {col3 a b c u, col3 a b c v, k})]
    simp only [card_third (col3 a b c) huv, card_class, Fin.sum_univ_three]
    generalize col3 a b c u = i
    generalize col3 a b c v = j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [cdrF, wtS, wt, dir, sigA, sigB] <;>
      field_simp <;> ring_nf <;> nlinarith [hadm]

end CDRBicolour.Absorption
