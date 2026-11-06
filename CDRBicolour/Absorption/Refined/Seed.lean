/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.Expand
public import CDRBicolour.Absorption.Refined.Count
public import CDRBicolour.Absorption.BRIFinal

/-!
# The refined bounded inverse and the approximate refined seed (item 2b)

Labels `rlab v = (col3 v, v mod 6)`.  In parity class `j`:

* `triG_iff`: the allowed triangles are the bicoloured ones with `rv j T < 3`;
* `refined_bri`: `Φ_j = psi1 ∘ psi1 ∘ Φ` is a bounded right inverse of the refined incidence
  operator on `ker ℓ`, constant `32929² K`;
* `approx_seed`: `μ_j = 2 · wt · 𝟏_{right}` has the right size and covers every edge up to
  `84/n` (signs on each colour class sum to at most `5`, `abs_class_sgn_le`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Refined

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

variable {a b c : ℕ}

/-- `v mod 6`. -/
def b6 {n : ℕ} (v : Fin n) : Fin 6 := ⟨v.val % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The refined labels of the CDR host. -/
abbrev rlab (a b c : ℕ) : Fin (a + b + c) → Fin 3 × Fin 6 := refLab (col3 a b c) b6

theorem rlab_map_fst (T : Finset (Fin (a + b + c))) :
    (T.val.map (rlab a b c)).map Prod.fst = T.val.map (col3 a b c) := by
  rw [Multiset.map_map]; rfl

theorem rlab_sum (T : Finset (Fin (a + b + c))) :
    ((T.val.map (rlab a b c)).map fun l => (l.2 : ℕ)).sum = ∑ v ∈ T, v.val % 6 := by
  rw [Multiset.map_map, sum_eq_multiset_sum]; rfl

theorem triG_iff (j : ℕ) (hj : j < 2) {T : Finset (Fin (a + b + c))} :
    T ∈ triG (rlab a b c) (refF j) ↔ T ∈ tri (col3 a b c) ∧ rv j T < 3 := by
  rw [gmem_tri, mem_tri]
  unfold IsAllowed refF rv
  simp only [Set.mem_ofPred_eq, rlab_map_fst, rlab_sum]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, by omega⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, by omega⟩

/-- On functions carried by right triangles the two incidence operators agree. -/
theorem MincG_eq (j : ℕ) (hj : j < 2) (cf : Finset (Fin (a + b + c)) → ℝ)
    (hc : ∀ T, 3 ≤ rv j T → cf T = 0) :
    MincG (rlab a b c) (refF j) cf = Minc (col3 a b c) cf := by
  ext e
  simp only [MincG, Minc, LinearMap.coe_mk, AddHom.coe_mk]
  have hset : (triG (rlab a b c) (refF j)).filter (fun T => e.1 ∈ triEdges T) =
      ((tri (col3 a b c)).filter fun T => e.1 ∈ triEdges T).filter fun T => rv j T < 3 := by
    ext T; simp only [mem_filter, triG_iff j hj]; tauto
  rw [hset, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with h
  · rfl
  · rw [hc T (by omega)]

theorem ell_eq (d : E0 (Fin (a + b + c)) → ℝ) :
    ellG' (wl (col3 a b c)) d = ell (col3 a b c) d := rfl

/-- **The refined bounded right inverse.** -/
def refined_bri (hbig : BigCls a b c) (j : ℕ) (hj : j < 2) {K : ℝ} (hK : 0 ≤ K)
    (B : BRI (col3 a b c) K) : BRIG (rlab a b c) (refF j) (wl (col3 a b c)) (32929 ^ 2 * K) where
  Φ := psi1 j ∘ₗ psi1 j ∘ₗ B.Φ
  exact d hd := by
    show MincG (rlab a b c) (refF j) (psi1 j (psi1 j (B.Φ d))) = d
    rw [MincG_eq j hj _ fun T hT => psi2_zero hbig j hj _ hT, Minc_psi1 hbig, Minc_psi1 hbig]
    exact B.exact d (by rw [← ell_eq]; exact hd)
  bound d hd T := by
    show |psi1 j (psi1 j (B.Φ d)) T| ≤ _
    have hd' : ell (col3 a b c) d = 0 := by rw [← ell_eq]; exact hd
    have hr : 0 ≤ K / Fintype.card (Fin (a + b + c)) * ‖d‖ := by positivity
    have h1 := fun T' => abs_psi1_le hbig j (B.Φ d) hr (B.bound d hd') T'
    have h2 := abs_psi1_le hbig j (psi1 j (B.Φ d)) (by positivity) h1 T
    calc _ ≤ 32929 * (32929 * (K / Fintype.card (Fin (a + b + c)) * ‖d‖)) := h2
      _ = _ := by ring

theorem refined_hw (j : ℕ) (hj : j < 2) :
    ∀ T ∈ triG (rlab a b c) (refF j), ∑ f ∈ triEdges T, wl (col3 a b c) f = 0 :=
  fun T hT => wl_tri ((triG_iff j hj).mp hT).1

/-! ### The CDR seed covers every edge -/

theorem Minc_wt (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) (e : E0 (Fin (a + b + c))) :
    Minc (col3 a b c) (fun T => wt a b c (T.val.map (col3 a b c))) e = 1 := by
  have he : e.1 ∈ (cdrHost a b c).G.edgeSet := by
    show e.1 ∈ (⊤ : SimpleGraph (Fin (a + b + c))).edgeSet
    rw [SimpleGraph.edgeSet_top]; exact e.2
  have := (cdr_H1 h hn).2 e.1 he
  simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk]
  convert this using 2
  ext T
  simp only [mem_filter]
  apply and_congr_left'
  rw [mem_tri]
  classical
  unfold allowed
  simp only [mem_filter, mem_univ, true_and]
  exact Iff.rfl

theorem refined_hell1 (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) :
    ellG' (wl (col3 a b c)) (fun _ => 1) = 0 := by
  have : (fun _ : E0 (Fin (a + b + c)) => (1 : ℝ)) =
      Minc (col3 a b c) (fun T => wt a b c (T.val.map (col3 a b c))) :=
    funext fun e => (Minc_wt h hn e).symm
  rw [this, ell_eq, ell_M]

/-! ### The approximate seed -/

/-- `μ_j = 2 wt 𝟏_{right}`. -/
def muJ (a b c : ℕ) (j : ℕ) (T : Finset (Fin (a + b + c))) : ℝ :=
  if rv j T < 3 then 2 * wt a b c (T.val.map (col3 a b c)) else 0

theorem muJ_bounds (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) (j : ℕ) (hj : j < 2)
    {T : Finset (Fin (a + b + c))} (hT : T ∈ triG (rlab a b c) (refF j)) :
    1 / (8 * Fintype.card (Fin (a + b + c))) ≤ muJ a b c j T ∧
      muJ a b c j T ≤ 8 / Fintype.card (Fin (a + b + c)) := by
  obtain ⟨hTt, hr⟩ := (triG_iff j hj).mp hT
  obtain ⟨h1, h2⟩ := (cdr_H1 h hn).1 T (mem_tri.mp hTt)
  have hN : (0 : ℝ) < Fintype.card (Fin (a + b + c)) := by
    rw [Fintype.card_fin]; exact_mod_cast (show 0 < a + b + c by omega)
  unfold muJ
  rw [if_pos hr]
  constructor
  · calc 1 / (8 * (Fintype.card (Fin (a + b + c)) : ℝ)) ≤
          1 / (2 * (Fintype.card (Fin (a + b + c)) : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = 2 * (1 / (4 * Fintype.card (Fin (a + b + c)))) := by ring
      _ ≤ _ := by gcongr
  · calc _ ≤ 2 * (4 / (Fintype.card (Fin (a + b + c)) : ℝ)) := by gcongr
      _ ≤ _ := by rw [mul_div_assoc']; gcongr; norm_num

open Classical in
/-- The triangles through an edge, by their third vertex. -/
theorem tri_filter_edge {u v : Fin (a + b + c)} (huv : u ≠ v) :
    (tri (col3 a b c)).filter (fun T => s(u, v) ∈ triEdges T) =
      (univ.filter fun w => w ≠ u ∧ w ≠ v ∧
        ({col3 a b c u, col3 a b c v, col3 a b c w} : Multiset (Fin 3)) ∈ cdrF).image
        fun w => ({u, v, w} : Finset (Fin (a + b + c))) := by
  ext T
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hT, he⟩
    have hA := mem_tri.mp hT
    have huvT : u ∈ T ∧ v ∈ T := by
      simpa [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, huv] using he
    obtain ⟨w, hwu, hwv, rfl⟩ := third_vertex hA.1 huv huvT.1 huvT.2
    exact ⟨w, ⟨hwu, hwv, cols_of_tri huv (Ne.symm hwu) (Ne.symm hwv) hT⟩, rfl⟩
  · rintro ⟨w, ⟨hwu, hwv, hF⟩, rfl⟩
    refine ⟨mem_tri.mpr (isAllowed_triple (col3 a b c) huv (Ne.symm hwu) (Ne.symm hwv) hF), ?_⟩
    simp [triEdges, mem_filter, huv]

open Classical in
theorem sum_tri_edge {u v : Fin (a + b + c)} (huv : u ≠ v) (F : Finset (Fin (a + b + c)) → ℝ) :
    ∑ T ∈ (tri (col3 a b c)).filter (fun T => s(u, v) ∈ triEdges T), F T =
      ∑ w ∈ univ.filter (fun w => w ≠ u ∧ w ≠ v ∧
        ({col3 a b c u, col3 a b c v, col3 a b c w} : Multiset (Fin 3)) ∈ cdrF),
        F {u, v, w} := by
  rw [tri_filter_edge huv, sum_image]
  intro w hw w' hw' he
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw hw'
  have : w ∈ ({u, v, w'} : Finset (Fin (a + b + c))) := by
    simp only at he; rw [← he]; simp
  simp only [mem_insert, mem_singleton] at this
  rcases this with h | h | h
  · exact absurd h hw.1
  · exact absurd h hw.2.1
  · exact h

open Classical in
/-- **The approximate refined seed covers every edge up to `84/n`.** -/
theorem muJ_deficit (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) (j : ℕ) (hj : j < 2)
    (e : E0 (Fin (a + b + c))) :
    |MincG (rlab a b c) (refF j) (muJ a b c j) e - 1| ≤ 84 / Fintype.card (Fin (a + b + c)) := by
  have hN : (0 : ℝ) < Fintype.card (Fin (a + b + c)) := by
    rw [Fintype.card_fin]; exact_mod_cast (show 0 < a + b + c by omega)
  set n : ℝ := (Fintype.card (Fin (a + b + c)) : ℝ)
  rw [MincG_eq j hj _ (fun T hT => by unfold muJ; rw [if_neg (by omega)]),
    ← Minc_wt h hn e]
  rcases e with ⟨e, hed⟩
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := by simpa using hed
  simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← sum_sub_distrib, sum_tri_edge huv]
  set W := univ.filter (fun w : Fin (a + b + c) => w ≠ u ∧ w ≠ v ∧
    ({col3 a b c u, col3 a b c v, col3 a b c w} : Multiset (Fin 3)) ∈ cdrF)
  set t := u.val % 6 + v.val % 6 + 6 - 3 * j
  have hterm : ∀ w ∈ W, muJ a b c j {u, v, w} -
      wt a b c (({u, v, w} : Finset (Fin (a + b + c))).val.map (col3 a b c)) =
      wt a b c {col3 a b c u, col3 a b c v, col3 a b c w} * sgn6 (t + w.val) := by
    intro w hw
    simp only [W, mem_filter, mem_univ, true_and] at hw
    obtain ⟨hwu, hwv, -⟩ := hw
    rw [val_map_triple (col3 a b c) huv (by exact hwu) (by exact hwv)]
    unfold muJ sgn6
    rw [val_map_triple (col3 a b c) huv (by exact hwu) (by exact hwv)]
    have hrv : rv j ({u, v, w} : Finset (Fin (a + b + c))) = (t + w.val) % 6 := by
      unfold rv; rw [sum3 (fun v => v.val % 6) huv (Ne.symm hwu) (Ne.symm hwv)]; omega
    rw [hrv]
    split_ifs <;> ring
  rw [sum_congr rfl hterm]
  -- group by the class of the third vertex
  rw [← sum_fiberwise W (fun w => col3 a b c w)]
  have hX : ∀ X : Fin 3, |∑ w ∈ W.filter (fun w => col3 a b c w = X),
      wt a b c {col3 a b c u, col3 a b c v, col3 a b c w} * sgn6 (t + w.val)| ≤ 28 / n := by
    intro X
    by_cases hne : (W.filter fun w => col3 a b c w = X).Nonempty
    · obtain ⟨w₀, hw₀⟩ := hne
      simp only [W, mem_filter, mem_univ, true_and] at hw₀
      obtain ⟨⟨hw₀u, hw₀v, hF₀⟩, hc₀⟩ := hw₀
      have hT₀ : ({u, v, w₀} : Finset (Fin (a + b + c))) ∈ tri (col3 a b c) :=
        mem_tri.mpr (isAllowed_triple (col3 a b c) huv (Ne.symm hw₀u) (Ne.symm hw₀v) hF₀)
      obtain ⟨b1, b2⟩ := (cdr_H1 h hn).1 _ (mem_tri.mp hT₀)
      beta_reduce at b1 b2
      rw [val_map_triple (col3 a b c) huv (by exact hw₀u) (by exact hw₀v), hc₀] at b1 b2
      have hwt : ∀ w ∈ W.filter (fun w => col3 a b c w = X),
          wt a b c {col3 a b c u, col3 a b c v, col3 a b c w} * sgn6 (t + w.val) =
            wt a b c {col3 a b c u, col3 a b c v, X} * sgn6 (t + w.val) := by
        intro w hw; rw [(mem_filter.mp hw).2]
      rw [sum_congr rfl hwt, ← mul_sum, abs_mul,
        abs_of_nonneg (le_trans (by positivity) b1)]
      -- the signs on the class minus `u, v`
      have hW : W.filter (fun w => col3 a b c w = X) =
          ((univ.filter fun w : Fin (a + b + c) => col3 a b c w = X).erase u).erase v := by
        ext w
        simp only [W, mem_filter, mem_univ, true_and, mem_erase]
        constructor
        · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h2, h1, h3⟩
        · rintro ⟨h2, h1, h3⟩; exact ⟨⟨h1, h2, by rw [h3, ← hc₀]; exact hF₀⟩, h3⟩
      have hs : |∑ w ∈ W.filter (fun w => col3 a b c w = X), sgn6 (t + w.val)| ≤ 7 := by
        rw [hW]
        have hbase := abs_class_sgn_le (a := a) (b := b) (c := c) X t
        have hsg : ∀ m, |sgn6 m| ≤ 1 := fun m => by unfold sgn6; split_ifs <;> norm_num
        set S := univ.filter fun w : Fin (a + b + c) => col3 a b c w = X
        have e1 : ∑ w ∈ S, sgn6 (t + w.val) =
            ∑ w ∈ S.erase u, sgn6 (t + w.val) + (if u ∈ S then sgn6 (t + u.val) else 0) := by
          split_ifs with hu
          · rw [← add_sum_erase _ _ hu, add_comm]
          · rw [erase_eq_of_notMem hu, add_zero]
        have e2 : ∑ w ∈ S.erase u, sgn6 (t + w.val) =
            ∑ w ∈ (S.erase u).erase v, sgn6 (t + w.val) +
              (if v ∈ S.erase u then sgn6 (t + v.val) else 0) := by
          split_ifs with hv
          · rw [← add_sum_erase _ _ hv, add_comm]
          · rw [erase_eq_of_notMem hv, add_zero]
        have i1 : |(if u ∈ S then sgn6 (t + u.val) else 0)| ≤ 1 := by
          split_ifs
          · exact hsg _
          · simp
        have i2 : |(if v ∈ S.erase u then sgn6 (t + v.val) else 0)| ≤ 1 := by
          split_ifs
          · exact hsg _
          · simp
        have : ∑ w ∈ (S.erase u).erase v, sgn6 (t + w.val) = ∑ w ∈ S, sgn6 (t + w.val) -
            (if u ∈ S then sgn6 (t + u.val) else 0) -
            (if v ∈ S.erase u then sgn6 (t + v.val) else 0) := by rw [e1, e2]; ring
        rw [this]
        calc _ ≤ |∑ w ∈ S, sgn6 (t + w.val)| + |(if u ∈ S then sgn6 (t + u.val) else 0)| +
              |(if v ∈ S.erase u then sgn6 (t + v.val) else 0)| := by
              have k1 := abs_sub (∑ w ∈ S, sgn6 (t + w.val) - (if u ∈ S then sgn6 (t + u.val) else 0))
                (if v ∈ S.erase u then sgn6 (t + v.val) else 0)
              have k2 := abs_sub (∑ w ∈ S, sgn6 (t + w.val)) (if u ∈ S then sgn6 (t + u.val) else 0)
              linarith
          _ ≤ 5 + 1 + 1 := by gcongr
          _ = 7 := by norm_num
      calc _ ≤ 4 / n * 7 := mul_le_mul b2 hs (abs_nonneg _) (by positivity)
        _ = 28 / n := by ring
    · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty, abs_zero]; positivity
  calc _ ≤ ∑ X : Fin 3, |∑ w ∈ W.filter (fun w => col3 a b c w = X),
          wt a b c {col3 a b c u, col3 a b c v, col3 a b c w} * sgn6 (t + w.val)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _X : Fin 3, 28 / n := sum_le_sum fun X _ => hX X
    _ = 84 / n := by simp; ring

end CDRBicolour.Absorption.Refined
