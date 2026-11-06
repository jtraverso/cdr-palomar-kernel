/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V48.WeightedTail
@[expose] public section

/-!
# V48 — deterministic persistence of the RAW seed profile; true-subtype adapter; window

Nothing here is probabilistic: `W` is fixed, and the later sets are arbitrary.

* `exclC G K lab F W U u v` — the EXCLUDED completions of `uv`: vertices `a ∈ W` with `{u,v,a}`
  allowed in the original `G` but NOT (`a ∈ U` and `{u,v,a}` allowed in the surviving graph `K`).
* `sampW_loss_eq` — for `K ≤ G` and `U ⊆ W`, the loss `sampW G W - sampW K U` is EXACTLY the
  original seed weight of the excluded completions; `sampW_loss_le` — it lies in
  `[0, |exclC| · C/n]`.
* `profile_persist` — if `|sampW G W u v / q - 1| ≤ δ` then
  `|sampW K U u v / q - 1| ≤ δ + |exclC| · C/(q n)`.
* `card_exclC_le` — for `K = G \ B` (sparse edge deletion) and `U = W \ Z` (vertex deletion)
  and a surviving edge (`¬ B.Adj u v`), `|exclC| ≤ |Z| + deg_B u + deg_B v`.
* `subSum K lab F φ U u v` — the raw completion sum on the TRUE subtype host
  `K.comap Subtype.val` over `{a // a ∈ U}`, labels `lab ∘ Subtype.val`, weights
  `φ (T.map ↪val)`; `subSum_eq` — it equals `sampW K lab F φ U u v` (no surrogate host with
  isolated deleted vertices is used).
* `coeff_window` — the positive coefficient window of the raw subtype weights `φ T / q` in terms
  of the ACTUAL size `|U|`: from `q n / κ ≤ |U| < 2 q n`,
  `1/(κ C |U|) ≤ φ T / q ≤ 2C/|U|`.

No exact seed and no divisibility of any induced or surviving host is claimed.
-/

open Finset

namespace S07V48

open TypedTriangle.SparseEdge S07V24

variable {V I : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- the excluded completions of `uv` when passing from `(G, W)` to `(K, U)` -/
noncomputable def exclC (G K : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (W U : Finset V) (u v : V) : Finset V :=
  W.filter (fun a => IsAllowed G lab F {u, v, a} ∧ ¬ (a ∈ U ∧ IsAllowed K lab F {u, v, a}))

omit [Fintype V] [DecidableEq V] in
lemma allowed_mono {G K : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} (hKG : K ≤ G)
    {T : Finset V} (h : IsAllowed K lab F T) : IsAllowed G lab F T :=
  ⟨h.1, fun x hx y hy hxy => hKG (h.2.1 x hx y hy hxy), h.2.2⟩

omit [Fintype V] in
/-- **the loss is exactly the seed weight of the excluded completions** -/
theorem sampW_loss_eq {G K : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} (hKG : K ≤ G)
    {W U : Finset V} (hUW : U ⊆ W) (φ : Finset V → ℝ) (u v : V) :
    sampW G lab F φ W u v - sampW K lab F φ U u v =
      ∑ a ∈ exclC G K lab F W U u v, compW G lab F φ u v a := by
  classical
  have hU : sampW K lab F φ U u v =
      ∑ a ∈ W, (if a ∈ U then compW K lab F φ u v a else 0) := by
    unfold sampW wsum
    rw [sum_ite_mem, inter_eq_right.2 hUW]
  rw [hU]
  unfold sampW wsum exclC
  rw [← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro a _
  unfold compW
  by_cases hG : IsAllowed G lab F {u, v, a}
  · by_cases haU : a ∈ U
    · by_cases hK : IsAllowed K lab F {u, v, a}
      · simp [hG, haU, hK]
      · simp [hG, haU, hK]
    · simp [hG, haU]
  · have hK : ¬ IsAllowed K lab F {u, v, a} := fun h => hG (allowed_mono hKG h)
    simp [hG, hK]

/-- **the loss lies in `[0, |exclC| · C/n]`** -/
theorem sampW_loss_le {G K : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (hKG : K ≤ G)
    {W U : Finset V} (hUW : U ⊆ W) (u v : V) :
    0 ≤ sampW G lab F φ W u v - sampW K lab F φ U u v ∧
      sampW G lab F φ W u v - sampW K lab F φ U u v ≤
        (exclC G K lab F W U u v).card * (C / Fintype.card V) := by
  rw [sampW_loss_eq hKG hUW φ u v]
  refine ⟨sum_nonneg fun a _ => compW_nonneg hφ hC u v a, ?_⟩
  have := sum_le_card_nsmul (exclC G K lab F W U u v) (compW G lab F φ u v)
    (C / Fintype.card V) (fun a _ => compW_le hφ hC u v a)
  rwa [nsmul_eq_mul] at this

/-- **persistence of the RAW relative profile** -/
theorem profile_persist {G K : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C q δ : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (hq : 0 < q) (hKG : K ≤ G)
    {W U : Finset V} (hUW : U ⊆ W) {u v : V}
    (hprof : |sampW G lab F φ W u v / q - 1| ≤ δ) :
    |sampW K lab F φ U u v / q - 1| ≤
      δ + ((exclC G K lab F W U u v).card : ℝ) * C / (q * Fintype.card V) := by
  obtain ⟨h0, h1⟩ := sampW_loss_le hφ hC hKG hUW u v
  set x := sampW G lab F φ W u v
  set y := sampW K lab F φ U u v
  set N : ℝ := ((exclC G K lab F W U u v).card : ℝ)
  have e : (N * (C / Fintype.card V)) / q = N * C / (q * Fintype.card V) := by
    rw [mul_div_assoc', div_div, mul_comm (Fintype.card V : ℝ) q]
  have hd : (x - y) / q ≤ N * C / (q * Fintype.card V) := by
    rw [← e]; exact div_le_div_of_nonneg_right h1 hq.le
  have hd0 : 0 ≤ (x - y) / q := div_nonneg h0 hq.le
  have hsplit : y / q - 1 = (x / q - 1) - (x - y) / q := by field_simp; ring
  rw [hsplit]
  calc |(x / q - 1) - (x - y) / q| ≤ |x / q - 1| + |(x - y) / q| := abs_sub _ _
    _ ≤ δ + N * C / (q * Fintype.card V) := by
        rw [abs_of_nonneg hd0]; exact add_le_add hprof hd

/-- **excluded completions under vertex deletion `Z` and sparse edge deletion `B`** -/
theorem card_exclC_le (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (B : SimpleGraph V) [DecidableRel B.Adj] (W Z : Finset V) {u v : V} (huvB : ¬ B.Adj u v) :
    (exclC G (G \ B) lab F W (W \ Z) u v).card ≤ Z.card + B.degree u + B.degree v := by
  classical
  have hsub : exclC G (G \ B) lab F W (W \ Z) u v ⊆
      (Z ∪ B.neighborFinset u) ∪ B.neighborFinset v := by
    intro a ha
    simp only [exclC, mem_filter] at ha
    obtain ⟨haW, hG, hnot⟩ := ha
    simp only [mem_union, SimpleGraph.mem_neighborFinset]
    by_contra hc
    push_neg at hc
    obtain ⟨⟨haZ, hua⟩, hva⟩ := hc
    apply hnot
    refine ⟨mem_sdiff.2 ⟨haW, haZ⟩, hG.1, ?_, hG.2.2⟩
    intro x hx y hy hxy
    refine ⟨hG.2.1 x hx y hy hxy, ?_⟩
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hxy
      | exact huvB
      | exact fun h => huvB h.symm
      | exact hua
      | exact fun h => hua h.symm
      | exact hva
      | exact fun h => hva h.symm
  calc (exclC G (G \ B) lab F W (W \ Z) u v).card
      ≤ ((Z ∪ B.neighborFinset u) ∪ B.neighborFinset v).card := card_le_card hsub
    _ ≤ (Z ∪ B.neighborFinset u).card + (B.neighborFinset v).card := card_union_le _ _
    _ ≤ Z.card + (B.neighborFinset u).card + (B.neighborFinset v).card := by
        have := card_union_le Z (B.neighborFinset u); omega
    _ = Z.card + B.degree u + B.degree v := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]

/-! ### The true subtype host -/

/-- the raw completion sum on the TRUE subtype host `K.comap Subtype.val` over `{a // a ∈ U}`,
with weights `φ (T.map ↪val)` -/
noncomputable def subSum (K : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) (U : Finset V) (u v : {a // a ∈ U}) : ℝ :=
  ∑ a : {a // a ∈ U}, compW (K.comap Subtype.val) (lab ∘ Subtype.val) F
    (fun T => φ (T.map (Function.Embedding.subtype _))) u v a

omit [Fintype V] in
lemma map_triple_subtype {U : Finset V} (u v a : {a // a ∈ U}) :
    ({u, v, a} : Finset {a // a ∈ U}).map (Function.Embedding.subtype _) = {u.1, v.1, a.1} := by
  simp [Finset.map_insert, Finset.map_singleton]

omit [Fintype V] [DecidableEq V] in
/-- allowed triangles of the subtype host are exactly the allowed triangles of `K` -/
lemma isAllowed_subtype_iff {K : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {U : Finset V} (T : Finset {a // a ∈ U}) :
    IsAllowed (K.comap Subtype.val) (lab ∘ Subtype.val) F T ↔
      IsAllowed K lab F (T.map (Function.Embedding.subtype _)) := by
  unfold IsAllowed
  simp only [Finset.card_map, Finset.mem_map, Function.Embedding.coe_subtype,
    SimpleGraph.comap_adj, Finset.map_val, Multiset.map_map]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact h2 x hx y hy (fun h => hxy (h ▸ rfl))
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun x hx y hy hxy =>
      h2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ (fun h => hxy (Subtype.ext h)), h3⟩

omit [Fintype V] in
/-- **adapter: the subtype raw sum is the ambient sampled sum** -/
theorem subSum_eq (K : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) (U : Finset V) (u v : {a // a ∈ U}) :
    subSum K lab F φ U u v = sampW K lab F φ U u.1 v.1 := by
  classical
  unfold subSum sampW wsum
  rw [← Finset.sum_coe_sort U]
  apply sum_congr rfl
  intro a _
  unfold compW
  dsimp only
  rw [map_triple_subtype]
  by_cases h : IsAllowed K lab F {u.1, v.1, a.1}
  · have h' : IsAllowed (K.comap Subtype.val) (lab ∘ Subtype.val) F {u, v, a} := by
      rw [isAllowed_subtype_iff, map_triple_subtype]; exact h
    simp only [h, h', if_true]
  · have h' : ¬ IsAllowed (K.comap Subtype.val) (lab ∘ Subtype.val) F {u, v, a} := by
      rw [isAllowed_subtype_iff, map_triple_subtype]; exact h
    simp only [h, h', if_false]

/-- **the positive coefficient window in terms of the ACTUAL size `|U|`** -/
theorem coeff_window {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C q κ : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (hq : 0 < q) (hκ : 0 < κ)
    {U : Finset V} (hU1 : q * Fintype.card V / κ ≤ U.card)
    (hU2 : (U.card : ℝ) < 2 * q * Fintype.card V) {T : Finset V} (hT : IsAllowed G lab F T) :
    1 / (κ * C * U.card) ≤ φ T / q ∧ φ T / q ≤ 2 * C / U.card := by
  have hn : (0 : ℝ) < Fintype.card V := by
    by_contra h; push_neg at h
    have : (U.card : ℝ) < 0 := by nlinarith
    exact absurd this (not_lt.2 (Nat.cast_nonneg _))
  have hUpos : (0 : ℝ) < U.card := lt_of_lt_of_le (by positivity) hU1
  obtain ⟨hlo, hhi⟩ := hφ.1 T hT
  have hqn : q * Fintype.card V ≤ κ * U.card := by
    rwa [div_le_iff₀ hκ, mul_comm (U.card : ℝ)] at hU1
  constructor
  · calc 1 / (κ * C * U.card) = 1 / (C * (κ * U.card)) := by ring_nf
      _ ≤ 1 / (C * (q * Fintype.card V)) :=
          one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hqn hC.le)
      _ = 1 / (C * Fintype.card V) / q := by field_simp
      _ ≤ φ T / q := div_le_div_of_nonneg_right hlo hq.le
  · calc φ T / q ≤ C / Fintype.card V / q := div_le_div_of_nonneg_right hhi hq.le
      _ = 2 * C / (2 * (q * Fintype.card V)) := by field_simp
      _ ≤ 2 * C / U.card := by
          apply div_le_div_of_nonneg_left (by positivity) hUpos; linarith

omit [Fintype V] in
lemma card_sdiff_ge' (A S : Finset V) : (A.card : ℝ) - S.card ≤ (A \ S).card := by
  have := Finset.card_le_card_sdiff_add_card (s := A) (t := S)
  have : (A.card : ℝ) ≤ (A \ S).card + S.card := by exact_mod_cast this
  linarith

/-- **inherited H3 pools on the TRUE surviving subtype host** `(G \ B).comap val` over
`{a // a ∈ U}`: each pool loses at most the `B`-degrees of its two roots -/
theorem subtype_pool (G B : SimpleGraph V) [DecidableRel B.Adj] (lab : V → I) (U : Finset V)
    (k : I) (u v : {a // a ∈ U}) :
    ((commonNbrs G lab k u.1 v.1 ∩ U).card : ℝ) - (B.degree u.1 + B.degree v.1) ≤
      (commonNbrs ((G \ B).comap Subtype.val) (lab ∘ Subtype.val) k u v).card := by
  classical
  have hsub : (commonNbrs G lab k u.1 v.1 ∩ U) \ (B.neighborFinset u.1 ∪ B.neighborFinset v.1) ⊆
      (commonNbrs ((G \ B).comap Subtype.val) (lab ∘ Subtype.val) k u v).map
        (Function.Embedding.subtype _) := by
    intro w hw
    simp only [commonNbrs, mem_sdiff, mem_inter, mem_filter, mem_univ, true_and, mem_union,
      SimpleGraph.mem_neighborFinset, not_or] at hw
    obtain ⟨⟨⟨hu, hv, hl⟩, hwU⟩, hBu, hBv⟩ := hw
    rw [mem_map]
    refine ⟨⟨w, hwU⟩, ?_, rfl⟩
    simp only [commonNbrs, mem_filter, mem_univ, true_and, SimpleGraph.comap_adj,
      SimpleGraph.sdiff_adj, Function.comp_apply]
    exact ⟨⟨hu, hBu⟩, ⟨hv, hBv⟩, hl⟩
  have h1 := card_le_card hsub
  rw [card_map] at h1
  have h2 := card_sdiff_ge' (commonNbrs G lab k u.1 v.1 ∩ U)
    (B.neighborFinset u.1 ∪ B.neighborFinset v.1)
  have h3 : ((B.neighborFinset u.1 ∪ B.neighborFinset v.1).card : ℝ) ≤
      B.degree u.1 + B.degree v.1 := by
    have := card_union_le (B.neighborFinset u.1) (B.neighborFinset v.1)
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]
      at this
    exact_mod_cast this
  have h4 : (((commonNbrs G lab k u.1 v.1 ∩ U) \
      (B.neighborFinset u.1 ∪ B.neighborFinset v.1)).card : ℝ) ≤
      (commonNbrs ((G \ B).comap Subtype.val) (lab ∘ Subtype.val) k u v).card := by
    exact_mod_cast h1
  linarith

end S07V48
