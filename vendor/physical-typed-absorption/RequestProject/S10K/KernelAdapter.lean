/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.SourceKernel
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23: the LocalKernel of V22 is CONSTRUCTED from the original H3/H4

`localKernel_of_H3H4`: on the physical host `(G, lab, F)` (vertex type in `Type`), the
ORIGINAL hypotheses

* H3 = `CommonNbrCond G lab F α` (all allowed pairs),
* H4 = `HingeCond G lab F α h` (normalisation `n^(i-4)`, four fixed roots),
* `h ≥ 6`, `α > 0`, `n ≥ n₀ = 2(12h+3)·2^(h choose 2)/α`

produce a `LocalKernel` (S10 (3.1)) for the physical triangle matrix, with the constants

  `L = 14`, `D = 12 K`, `K = max 1 (2^(M+1)/α)`, `M = h choose 2`,

fixed before the host. Each permitted source `T` has its OWN finite probability space (the
positive-weight outcomes of its 12-query process); pivots are uniform on
`triOn(e) ∖ {T}` for each edge `e` of `T`.

`degreeCond_of_H3`: the degree condition `d_e ≥ n/C` with `C = 1/α`.

`smooth_inverse_H3H4`: S10 (1.2) on the physical host with the kernel and the degree
condition DISCHARGED. Remaining input: only the integer congestion provider (1.1) (the
P05-CERT endpoint, connected by the user); nothing else is assumed.
-/

open Finset

noncomputable section
open Classical

namespace S10V23

open TypedTriangle.SparseEdge S10V22 S10V23.Proc

variable {V I : Type} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {al : ℝ} {hh : ℕ}

/-- The constant `K = max 1 (2^(M+1)/α)`. -/
def Kc (al : ℝ) (hh : ℕ) : ℝ := max 1 (2 ^ (hh.choose 2 + 1) / al)

lemma one_le_Kc (al : ℝ) (hh : ℕ) : 1 ≤ Kc al hh := le_max_left _ _
lemma le_Kc (al : ℝ) (hh : ℕ) : 2 ^ (hh.choose 2 + 1) / al ≤ Kc al hh := le_max_right _ _

/-- A labelling `T = {u, v, a}` of a 3-set (default otherwise). -/
def lab3 (d0 : V) (T : Finset V) : V × V × V :=
  if h : ∃ p : V × V × V, p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧
      T = {p.1, p.2.1, p.2.2} then Classical.choose h else (d0, d0, d0)

lemma lab3_spec (d0 : V) {T : Finset V} (hT : T.card = 3) :
    T = {(lab3 d0 T).1, (lab3 d0 T).2.1, (lab3 d0 T).2.2} := by
  have h : ∃ p : V × V × V, p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧
      T = {p.1, p.2.1, p.2.2} := by
    obtain ⟨x, y, z, h1, h2, h3, rfl⟩ := Finset.card_eq_three.1 hT
    exact ⟨(x, y, z), h1, h2, h3, rfl⟩
  unfold lab3; rw [dif_pos h]; exact (Classical.choose_spec h).2.2.2

/-- The pivot of edge `e` in an outcome of the process of `T = {u,v,a}`. -/
def pivotOf (u v a : V) (e : Sym2 V) (ω : Fin 12 → Opt V) : Finset V :=
  if e = s(u, v) then {u, v, ob1 u ω} else if e = s(u, a) then {u, a, ob2 u ω}
  else {v, a, ob3 u ω}

lemma sum_subtype_ne {α : Type} [Fintype α] (w f : α → ℝ) :
    ∑ x : {x // w x ≠ 0}, w x * f x = ∑ x, w x * f x := by
  rw [← Finset.sum_subtype (univ.filter (fun x => w x ≠ 0)) (by simp) (fun x => w x * f x)]
  refine Finset.sum_filter_of_ne fun x _ hx => ?_
  intro h; exact hx (by rw [h, zero_mul])

/-- The guarded pivot query of a permitted triangle is the full set of thirds. -/
lemma apexStep_eq (H3 : CommonNbrCond G lab F al)
    (h2 : 2 ≤ al * (Fintype.card V : ℝ)) {p q r : V} (hT : IsAllowed G lab F {p, q, r}) :
    nz (apexStep G lab F al p q {r}) = (apexSet G lab F p q {r}).image Sum.inl := by
  have h1 := thirds_ge H3 hT
  have h3 := apexSet_card_ge (G := G) (lab := lab) (F := F) p q {r}
  simp only [Finset.card_singleton, Nat.cast_one] at h3
  have hg : al * (Fintype.card V : ℝ) / 2 ≤ (apexSet G lab F p q {r}).card := by linarith
  have hpos : 0 < ((apexSet G lab F p q {r}).card : ℝ) := by linarith
  have hne : (apexSet G lab F p q {r}).Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos)
  unfold apexStep; rw [if_pos hg]
  unfold nz; rw [if_pos (hne.image _)]

lemma card_triOn_ge (H3 : CommonNbrCond G lab F al) {p q r : V}
    (hT : IsAllowed G lab F {p, q, r}) :
    al * (Fintype.card V : ℝ) ≤ (triOn (allowedTri G lab F) s(p, q)).card := by
  obtain ⟨hpq, -, -⟩ := distinct_of_card_three hT.1
  rw [card_triOn hpq]; exact thirds_ge H3 hT

/-- **Degree condition from H3** (`C = 1/α`). -/
theorem degreeCond_of_H3 (H3 : CommonNbrCond G lab F al) :
    DegreeCond (allowedTri G lab F) (1 / al) := by
  intro T hT e he
  rw [mem_allowedTri] at hT
  induction e using Sym2.ind with
  | _ x y =>
  obtain ⟨hx, hy, hxy⟩ := mem_edgesOf.1 he
  obtain ⟨t, -, -, rfl⟩ := eq_triple_of_mem hT.1 hx hy hxy
  rw [one_div, div_inv_eq_mul, mul_comm]
  exact card_triOn_ge H3 hT

/-- **The local geometric kernel (S10 (3.1)) constructed from H3/H4.** -/
theorem localKernel_of_H3H4 (H3 : CommonNbrCond G lab F al) (H4 : HingeCond G lab F al hh)
    (hal : 0 < al) (hh6 : 6 ≤ hh) (hn0 : nZero al hh ≤ (Fintype.card V : ℝ)) :
    Nonempty (LocalKernel (realOp (triMat (allowedTri G lab F))) (allowedTri G lab F) 14
      (12 * Kc al hh)) := by
  set n := (Fintype.card V : ℝ) with hn_def
  have hn : 0 < n := lt_of_lt_of_le (by unfold nZero; positivity) hn0
  have hV : Nonempty V := Fintype.card_pos_iff.1 (Nat.cast_pos.1 hn)
  obtain ⟨d0⟩ := hV
  have h2 : 2 ≤ al * n := by
    have h1 : (1 : ℝ) ≤ 2 ^ (hh.choose 2) := one_le_pow₀ (by norm_num)
    have := hn0; unfold nZero at this
    rw [div_le_iff₀ hal] at this
    have : (2 : ℝ) ≤ 2 * (12 * hh + 3) * 2 ^ (hh.choose 2) := by
      have : (1 : ℝ) ≤ 12 * hh + 3 := by have : (0 : ℝ) ≤ hh := Nat.cast_nonneg _; linarith
      nlinarith
    linarith
  -- the data of a source
  let L3 := lab3 d0
  let pO : Finset V → List (Opt V) → Finset (Opt V) := fun T =>
    opts G lab F al hh (L3 T).1 (L3 T).2.1 (L3 T).2.2
  have key : ∀ T ∈ allowedTri G lab F, ∃ u v a : V, L3 T = (u, v, a) ∧ T = {u, v, a} ∧
      IsAllowed G lab F {u, v, a} := by
    intro T hT
    rw [mem_allowedTri] at hT
    refine ⟨(L3 T).1, (L3 T).2.1, (L3 T).2.2, rfl, lab3_spec d0 hT.1, ?_⟩
    rw [← lab3_spec d0 hT.1]; exact hT
  refine ⟨{
    Ω := fun T => {ω : Fin 12 → Opt V // Expo.wt (pO T) 12 [] ω ≠ 0}
    fin := fun T => inferInstance
    μ := fun T ω => Expo.wt (pO T) 12 [] ω.val
    μ_nonneg := fun T ω => Expo.wt_nonneg _ _ _ _
    μ_sum := fun T => by
      have := sum_subtype_ne (Expo.wt (pO T) 12 []) (fun _ => 1)
      simp only [mul_one] at this
      rw [this]
      exact Expo.sum_wt _ (opts_nonempty _ _ _ _ _ _ _ _) 12 []
    P := fun T e ω => pivotOf (L3 T).1 (L3 T).2.1 (L3 T).2.2 e ω.val
    c := fun T ω => certOf G lab F (L3 T).1 (L3 T).2.1 (L3 T).2.2 ω.val
    mem_tri := fun T hT e he => mem_triOn.2 ⟨hT, he⟩
    two_le := ?_
    marginal := ?_
    boundary := ?_
    supp := ?_
    avoid := ?_
    expect := ?_ }⟩
  · -- two_le
    intro T hT e he
    obtain ⟨u, v, a, -, rfl, hTa⟩ := key T hT
    have hTa1 : IsAllowed G lab F {u, a, v} := by rw [triple_comm1]; exact hTa
    have hTa2 : IsAllowed G lab F {v, a, u} := by rw [triple_comm2]; exact hTa
    obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
    rw [edgesOf_triple huv hua hva] at he
    simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at he
    have : al * n ≤ ((triOn (allowedTri G lab F) e).card : ℝ) := by
      rcases he with rfl | rfl | rfl
      · exact card_triOn_ge H3 hTa
      · exact card_triOn_ge H3 hTa1
      · exact card_triOn_ge H3 hTa2
    exact_mod_cast (show (2 : ℝ) ≤ _ from h2.trans this)
  · -- marginal
    intro T hT e he S
    obtain ⟨u, v, a, hL, rfl, hTa⟩ := key T hT
    have hTa1 : IsAllowed G lab F {u, a, v} := by rw [triple_comm1]; exact hTa
    have hTa2 : IsAllowed G lab F {v, a, u} := by rw [triple_comm2]; exact hTa
    obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
    have hsum : ∑ ω ∈ univ.filter (fun ω : {ω : Fin 12 → Opt V //
          Expo.wt (pO {u, v, a}) 12 [] ω ≠ 0} =>
          pivotOf (L3 {u, v, a}).1 (L3 {u, v, a}).2.1 (L3 {u, v, a}).2.2 e ω.val = S),
          Expo.wt (pO {u, v, a}) 12 [] ω.val =
        ∑ ω, Expo.wt (opts G lab F al hh u v a) 12 [] ω *
          (if pivotOf u v a e ω = S then 1 else 0) := by
      rw [Finset.sum_filter]
      have := sum_subtype_ne (Expo.wt (pO {u, v, a}) 12 [])
        (fun ω => if pivotOf (L3 {u, v, a}).1 (L3 {u, v, a}).2.1 (L3 {u, v, a}).2.2 e ω = S
          then 1 else 0)
      simp only [mul_ite, mul_one, mul_zero] at this ⊢
      rw [this]
      simp only [pO, hL]
    rw [hsum]
    rw [edgesOf_triple huv hua hva] at he
    simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at he
    have hsua : s(u, a) ≠ s(u, v) := by
      intro h; rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
      · exact hva h.symm
      · exact huv h
    have hsva1 : s(v, a) ≠ s(u, v) := by
      intro h; rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
      · exact huv h.symm
      · exact hua h.symm
    have hsva2 : s(v, a) ≠ s(u, a) := by
      intro h; rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact huv h.symm
      · exact hva h
    rcases he with rfl | rfl | rfl
    · have hp : ∀ ω : Fin 12 → Opt V, pivotOf u v a s(u, v) ω =
          {u, v, gv u (ω ⟨0, by norm_num⟩)} := fun ω => by
        simp [pivotOf, ob1, G12_of_lt]
      simp only [hp]
      exact pivot_marginal hTa 0 (by norm_num) (fun h' hl => by
        unfold opts; rw [hl]; exact apexStep_eq H3 h2 hTa) S
    · have hp : ∀ ω : Fin 12 → Opt V, pivotOf u v a s(u, a) ω =
          {u, a, gv u (ω ⟨1, by norm_num⟩)} := fun ω => by
        simp [pivotOf, hsua, ob2, G12_of_lt]
      simp only [hp]
      rw [← triple_comm1 u v a]
      exact pivot_marginal hTa1 1 (by norm_num) (fun h' hl => by
        unfold opts; rw [hl]; exact apexStep_eq H3 h2 hTa1) S
    · have hp : ∀ ω : Fin 12 → Opt V, pivotOf u v a s(v, a) ω =
          {v, a, gv u (ω ⟨2, by norm_num⟩)} := fun ω => by
        simp [pivotOf, hsva1, hsva2, ob3, G12_of_lt]
      simp only [hp]
      rw [← triple_comm2 u v a]
      exact pivot_marginal hTa2 2 (by norm_num) (fun h' hl => by
        unfold opts; rw [hl]; exact apexStep_eq H3 h2 hTa2) S
  · -- boundary
    intro T hT ω
    obtain ⟨u, v, a, hL, rfl, hTa⟩ := key T hT
    obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
    have hw : Expo.wt (opts G lab F al hh u v a) 12 [] ω.val ≠ 0 := by
      have := ω.property; simp only [pO, hL] at this; exact this
    have hv := reach_valid hTa H3 H4 hal hh6 hn0 hw
    obtain ⟨hA, -⟩ := srcCert_spec hv
    simp only [hL]
    unfold certOf
    rw [hA, col_eq hTa, edgesOf_triple huv hua hva]
    have hsua : s(u, a) ≠ s(u, v) := by
      intro h; rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
      · exact hva h.symm
      · exact huv h
    have hsva1 : s(v, a) ≠ s(u, v) := by
      intro h; rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
      · exact huv h.symm
      · exact hua h.symm
    have hsva2 : s(v, a) ≠ s(u, a) := by
      intro h; rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
      · exact huv h.symm
      · exact hva h
    rw [Finset.sum_insert (not_mem_wedge_uv huv hua hva)]
    simp only [wedge]
    rw [Finset.sum_pair hsva2.symm]
    · simp only [pivotOf, if_neg hsua, if_neg hsva1, if_neg hsva2, if_true]
      rw [col_eq hv.hb1, col_eq hv.hb2, col_eq hv.hb3]
      abel
  · -- supp
    intro T hT ω S hS
    obtain ⟨u, v, a, hL, rfl, hTa⟩ := key T hT
    simp only [hL] at hS
    exact mem_allowedTri.2 (srcCert_supp hS)
  · -- avoid
    intro T hT ω S hS
    obtain ⟨u, v, a, hL, rfl, hTa⟩ := key T hT
    have hw : Expo.wt (opts G lab F al hh u v a) 12 [] ω.val ≠ 0 := by
      have := ω.property; simp only [pO, hL] at this; exact this
    have hv := reach_valid hTa H3 H4 hal hh6 hn0 hw
    simp only [hL]
    exact (srcCert_spec hv).2 S hS
  · -- expect
    intro T hT S _
    obtain ⟨u, v, a, hL, rfl, hTa⟩ := key T hT
    have := sum_subtype_ne (Expo.wt (pO {u, v, a}) 12 [])
      (fun ω => |certOf G lab F (L3 {u, v, a}).1 (L3 {u, v, a}).2.1 (L3 {u, v, a}).2.2 ω S|)
    rw [this]
    simp only [pO, hL]
    have := src_expect (G := G) (lab := lab) (F := F) (u := u) (v := v) (a := a) hal hn
      (one_le_Kc al hh) (le_Kc al hh) S
    refine this.trans (le_of_eq ?_)
    congr 2

/-- The threshold `n ≥ n₀` gives `2 ≤ α n`. -/
lemma two_le_al_mul_of_nZero (hal : 0 < al) {n : ℝ} (hn0 : nZero al hh ≤ n) : 2 ≤ al * n := by
  have h1 : (1 : ℝ) ≤ 2 ^ (hh.choose 2) := one_le_pow₀ (by norm_num)
  have := hn0; unfold nZero at this
  rw [div_le_iff₀ hal] at this
  have : (2 : ℝ) ≤ 2 * (12 * hh + 3) * 2 ^ (hh.choose 2) := by
    have : (1 : ℝ) ≤ 12 * hh + 3 := by have : (0 : ℝ) ≤ hh := Nat.cast_nonneg _; linarith
    nlinarith
  linarith

/-- **S10 (1.2) on the physical host with the local kernel and the degree condition
CONSTRUCTED from H3/H4.** The ONLY remaining input is the integer congestion provider
(1.1) (`IntCertProvider`, the P05-CERT endpoint on the prepared robust core). Constants:
`C = 1/α`, `L = 14`, `D = 12 K`, `K = max 1 (2^(M+1)/α)`, threshold `n ≥ n₀(α,h)`. -/
theorem smooth_inverse_H3H4 (H3 : CommonNbrCond G lab F al) (H4 : HingeCond G lab F al hh)
    (hal : 0 < al) (hh6 : 6 ≤ hh) (hn0 : nZero al hh ≤ (Fintype.card V : ℝ))
    {Kp : ℝ} (hKp : 0 ≤ Kp)
    (hprov : IntCertProvider (triMat (allowedTri G lab F)) (triTw (allowedTri G lab F))
      edgeEw Kp (Fintype.card V : ℝ))
    {x : Sym2 V → ℝ} (hx : x ∈ realImage (triMat (allowedTri G lab F))) {xmax : ℝ}
    (hxmax : ∀ e, |x e| ≤ xmax) :
    ∃ w : Finset V → ℝ, realOp (triMat (allowedTri G lab F)) w = x ∧
      ∀ S, |w S| ≤ (6 * (1 / al) + 3 * Kp / 2 * (14 * (3 * (12 * Kc al hh) ^ 2 +
        (12 * Kc al hh) ^ 3 / 3) + 36 * (1 / al) ^ 2)) * xmax / (Fintype.card V : ℝ) := by
  obtain ⟨Ker⟩ := localKernel_of_H3H4 H3 H4 hal hh6 hn0
  have h2 := two_le_al_mul_of_nZero hal hn0
  have hn : 2 * (1 / al) ≤ (Fintype.card V : ℝ) := by
    rw [mul_one_div, div_le_iff₀ hal]; linarith
  have hD : (0 : ℝ) ≤ 12 * Kc al hh := by have := one_le_Kc al hh; linarith
  exact smooth_inverse_physical (by positivity) hn (degreeCond_of_H3 H3) hKp (by norm_num) hD
    hprov Ker hx hxmax

end S10V23
