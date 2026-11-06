/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.AACCount

/-!
# Seeds from block-type counts

For a real parameter `t` (the intended number of `AAC` blocks), the six pair identities force
the other five counts (`cntAAB … cntBCC`, affine in `t`).  The type-uniform seed

  `x_type = count_type / #triangles_type`

satisfies the six edge equations (`AA`, `AB`, … reduce to the pair identities; `CC` uses the
admissibility identity), and if every count is at least `ε n²` it is a diffuse seed with
`C = 64 + 1/ε` (`cdr_H1_counts`).  Its total weight on `AAC` triangles is exactly `t`
(`seedN_aac_total`).
-/

@[expose] public section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-- `C(x,2)` as a real polynomial. -/
noncomputable def ch (x : ℝ) : ℝ := x * (x - 1) / 2

/-- The six block-type counts determined by `t = N_AAC`. -/
noncomputable def cntAAC (_a _b _c t : ℝ) : ℝ := t
noncomputable def cntAAB (a _b _c t : ℝ) : ℝ := ch a - t
noncomputable def cntACC (a _b c t : ℝ) : ℝ := a * c / 2 - t
noncomputable def cntABB (a b _c t : ℝ) : ℝ := a * b / 2 - ch a + t
noncomputable def cntBBC (a b _c t : ℝ) : ℝ := ch b - a * b / 2 + ch a - t
noncomputable def cntBCC (a b c t : ℝ) : ℝ := b * c / 2 - ch b + a * b / 2 - ch a + t

/-- The seed weight of a type: count divided by the number of triangles of that type. -/
noncomputable def wtN (a b c t : ℝ) (m : Multiset (Fin 3)) : ℝ :=
  if m.count 0 = 2 ∧ m.count 1 = 1 then cntAAB a b c t / (ch a * b)
  else if m.count 0 = 2 ∧ m.count 2 = 1 then cntAAC a b c t / (ch a * c)
  else if m.count 1 = 2 ∧ m.count 2 = 1 then cntBBC a b c t / (ch b * c)
  else if m.count 1 = 2 ∧ m.count 0 = 1 then cntABB a b c t / (a * ch b)
  else if m.count 2 = 2 ∧ m.count 0 = 1 then cntACC a b c t / (a * ch c)
  else if m.count 2 = 2 ∧ m.count 1 = 1 then cntBCC a b c t / (b * ch c)
  else 0

/-- Bounds `1/(Cn) ≤ N/T ≤ C/n` from `ε n² ≤ N ≤ n²/2` and `n³/128 ≤ T ≤ n³`. -/
theorem ratio_bounds {N T n ε C : ℝ} (hn : 0 < n) (hε : 0 < ε) (hN : ε * n ^ 2 ≤ N)
    (hN' : N ≤ n ^ 2 / 2) (hT : n ^ 3 / 128 ≤ T) (hT' : T ≤ n ^ 3) (hC : 64 ≤ C)
    (hCε : 1 ≤ C * ε) : 1 / (C * n) ≤ N / T ∧ N / T ≤ C / n := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hC0 : 0 < C := by linarith
  constructor
  · rw [div_le_div_iff₀ (by positivity) hT0]
    have hn3 : 0 ≤ n ^ 3 := by positivity
    have h1 : 1 * n ^ 3 ≤ C * ε * n ^ 3 := mul_le_mul_of_nonneg_right hCε hn3
    have h2 : C * ε * n ^ 3 = C * n * (ε * n ^ 2) := by ring
    have h3 : C * n * (ε * n ^ 2) ≤ C * n * N := mul_le_mul_of_nonneg_left hN (by positivity)
    linarith
  · rw [div_le_div_iff₀ hT0 hn]
    nlinarith

/-- Triangle counts of a type: between `n³/128` and `n³`. -/
theorem tri_bounds {x y n : ℝ} (hx : n + 8 ≤ 4 * x) (hy : n + 8 ≤ 4 * y) (hxn : x ≤ n)
    (hyn : y ≤ n) (hn : 0 < n) : n ^ 3 / 128 ≤ ch x * y ∧ ch x * y ≤ n ^ 3 := by
  unfold ch
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  constructor
  · have h1 : n ^ 2 / 16 ≤ x * (x - 1) := by nlinarith
    have h2 : n / 4 ≤ y := by linarith
    have : n ^ 2 / 16 * (n / 4) ≤ x * (x - 1) * y :=
      mul_le_mul h1 h2 (by positivity) (by nlinarith)
    nlinarith
  · have h1 : x * (x - 1) ≤ n ^ 2 := by nlinarith
    have : x * (x - 1) * y ≤ n ^ 2 * n := mul_le_mul h1 hyn hy0 (by positivity)
    nlinarith

set_option maxHeartbeats 1600000 in
/-- **H1 from counts**: if all six counts are at least `ε n²`, the count seed is a diffuse seed
with `C = 64 + 1/ε`. -/
theorem cdr_H1_counts {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c)
    {ε t : ℝ} (hε : 0 < ε)
    (h1 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntAAB a b c t)
    (h2 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntAAC a b c t)
    (h3 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntBBC a b c t)
    (h4 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntABB a b c t)
    (h5 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntACC a b c t)
    (h6 : ε * ((a + b + c : ℕ) : ℝ) ^ 2 ≤ cntBCC a b c t) :
    IsDiffuseSeed (cdrHost a b c) cdrF (64 + 1 / ε)
      (fun T => wtN a b c t (T.val.map (col3 a b c))) := by
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
  rw [hnn] at h1 h2 h3 h4 h5 h6
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
  have u1 := h1; have u2 := h2; have u3 := h3; have u4 := h4; have u5 := h5; have u6 := h6
  simp only [cntAAB, cntAAC, cntBBC, cntABB, cntACC, cntBCC] at u1 u2 u3 u4 u5 u6
  have hab : (a : ℝ) * b / 2 ≤ n ^ 2 / 2 := by nlinarith
  have hac : (a : ℝ) * c / 2 ≤ n ^ 2 / 2 := by nlinarith
  have hbc : (b : ℝ) * c / 2 ≤ n ^ 2 / 2 := by nlinarith
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · -- bounds
    rw [hcard]
    beta_reduce
    have hm : T.val.map (col3 a b c) ∈ cdrF := hT.2.2
    rcases type_cases hm with ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ |
      ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩
    · have hw : wtN a b c t (T.val.map (col3 a b c)) = cntAAB a b c t / (ch a * b) := by
        simp [wtN, h0', h1']
      rw [hw]
      obtain ⟨hT1, hT2⟩ := tri_bounds (n := n) ha hb (by linarith) (by linarith) hn0
      refine ratio_bounds hn0 hε h1 ?_ hT1 hT2 hC64 hCε
      unfold cntAAB; linarith [u1, u2, u3, u4, u5, u6, hab, hac, hbc, hchA, hchB, hchC, hεn]
    · have hw : wtN a b c t (T.val.map (col3 a b c)) = cntAAC a b c t / (ch a * c) := by
        simp [wtN, h0', h1', h2']
      rw [hw]
      obtain ⟨hT1, hT2⟩ := tri_bounds (n := n) ha hc (by linarith) (by linarith) hn0
      refine ratio_bounds hn0 hε h2 ?_ hT1 hT2 hC64 hCε
      unfold cntAAC; linarith [u1, u2, u3, u4, u5, u6, hab, hac, hbc, hchA, hchB, hchC, hεn]
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
  · -- edge sums
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

/-- The count seed puts total weight exactly `t` on the `AAC` triangles. -/
theorem seedN_aac_total {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c)
    (t : ℝ) :
    ∑ Q ∈ allowed (cdrHost a b c) cdrF,
        wtN a b c t (Q.val.map (col3 a b c)) *
          (if Q.val.map (col3 a b c) = aac then 1 else 0) = t := by
  classical
  obtain ⟨ha4, -, hc4⟩ := class_lower_all h hn
  have ha : (4 : ℝ) ≤ a := by exact_mod_cast (show 4 ≤ a by omega)
  have hc0 : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpos : (0 : ℝ) < a * (a - 1) := by nlinarith
  have hch : ch a ≠ 0 := by unfold ch; positivity
  have hw : wtN a b c t aac = t / (ch a * c) := by
    simp [wtN, aac, cntAAC]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  have hfil : (allowed (cdrHost a b c) cdrF).filter (fun Q => Q.val.map (col3 a b c) = aac) =
      univ.filter fun T : Finset (Fin (a + b + c)) =>
        T.card = 3 ∧ T.val.map (col3 a b c) = aac := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTa, hm⟩ := mem_filter.mp hT
      have hA : IsAllowed (cdrHost a b c) cdrF T := by
        unfold allowed at hTa; exact (mem_filter.mp hTa).2
      exact mem_filter.mpr ⟨mem_univ _, hA.1, hm⟩
    · intro hT
      obtain ⟨-, h3, hm⟩ := mem_filter.mp hT
      have hA : IsAllowed (cdrHost a b c) cdrF T :=
        ⟨h3, fun x _ y _ hxy => hxy, hm ▸ aac_mem_cdrF⟩
      refine mem_filter.mpr ⟨?_, hm⟩
      unfold allowed
      exact mem_filter.mpr ⟨mem_univ _, hA⟩
  rw [hfil, sum_congr rfl (fun Q hQ => by rw [(mem_filter.mp hQ).2.2, hw]), sum_const,
    card_aac, nsmul_eq_mul]
  have : ((a.choose 2 * c : ℕ) : ℝ) = ch a * c := by
    rw [Nat.cast_mul, Nat.cast_choose_two]; unfold ch; ring
  rw [this]
  field_simp

end CDRBicolour.Absorption
