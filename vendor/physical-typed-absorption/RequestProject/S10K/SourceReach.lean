/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.SourceProcess
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23: the guards hold at every positive-probability history (from H3/H4)

Under the ORIGINAL hypotheses (`CommonNbrCond` = H3 on all allowed pairs, `HingeCond` = H4
with the normalisation `n^(i-4)` and four fixed roots), `h ≥ 6`, `α > 0` and

  `n ≥ n₀ := 2 R 2^M / α`,  `R = 12 h + 3`,  `M = h choose 2`,

every option set met by a positive-probability outcome of the process of a permitted source
`T = {u,v,a}` passes its size guard (apex sets: `≥ αn − R ≥ αn/2`; hinge sets: fresh hinges
`≥ α n^(i-4) − R 2^M n^(i-5) ≥ (α/2) n^(i-4)`, by `card_fresh_ge`). Consequently each such
outcome satisfies the deterministic validity `SrcValid` (`reach_valid`).
-/

open Finset

noncomputable section
open Classical

namespace S10V23.Proc

open TypedTriangle.SparseEdge S10V22 S10V23

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {al : ℝ} {hh : ℕ}

/-! ## Degree from H3 -/

omit [Fintype V] in
lemma map_lab_triple (lab : V → I) {p q t : V} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) :
    ({p, q, t} : Finset V).val.map lab = {lab p, lab q, lab t} := by
  rw [Finset.insert_val_of_notMem (by simp [hpq, hpt]),
    Finset.insert_val_of_notMem (by simp [hqt])]
  simp

/-- **Permitted thirds from H3**: an edge `pq` of a permitted triangle has `≥ αn` permitted
thirds. -/
theorem thirds_ge (H3 : CommonNbrCond G lab F al) {p q t : V}
    (h : IsAllowed G lab F {p, q, t}) :
    al * (Fintype.card V : ℝ) ≤ (univ.filter (fun y => IsAllowed G lab F {p, q, y})).card := by
  obtain ⟨hpq, hpt, hqt⟩ := distinct_of_card_three h.1
  have hF : ({lab p, lab q, lab t} : Multiset I) ∈ F := by
    have := h.2.2; rwa [map_lab_triple lab hpq hpt hqt] at this
  refine (H3 p q hpq (lab t) hF).trans ?_
  have hadj : G.Adj p q := h.2.1 p (by simp) q (by simp) hpq
  exact_mod_cast Finset.card_le_card fun y hy => by
    simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨hpy, hqy, hly⟩ := hy
    have hyp : p ≠ y := G.ne_of_adj hpy
    have hyq : q ≠ y := G.ne_of_adj hqy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨card_three_of_distinct hpq hyp hyq, ?_, ?_⟩
    · intro x hx z hz hxz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hz
      rcases hx with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hxz
        | assumption
        | exact hadj.symm
        | exact hpy.symm
        | exact hqy.symm
    · rw [map_lab_triple lab hpq hyp hyq, hly]; exact hF

/-! ## Apex queries at reachable histories -/

lemma apexSet_card_ge (p q : V) (excl : Finset V) :
    ((univ.filter (fun y => IsAllowed G lab F {p, q, y})).card : ℝ) - excl.card ≤
      (apexSet G lab F p q excl).card := by
  have : univ.filter (fun y => IsAllowed G lab F {p, q, y}) ⊆
      apexSet G lab F p q excl ∪ excl := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_cases hye : y ∈ excl
    · exact Finset.mem_union_right _ hye
    · exact Finset.mem_union_left _ (by simp [apexSet, hy, hye])
  have h2 := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  have : ((univ.filter (fun y => IsAllowed G lab F {p, q, y})).card : ℝ) ≤
      (apexSet G lab F p q excl).card + excl.card := by exact_mod_cast h2
  linarith

/-- An answer of a guarded apex query whose guard holds. -/
theorem apex_mem (H3 : CommonNbrCond G lab F al) (hal : 0 < al)
    (hn : 0 < (Fintype.card V : ℝ)) {p q t : V} (ht : IsAllowed G lab F {p, q, t})
    {excl : Finset V} (hex : 2 * (excl.card : ℝ) ≤ al * Fintype.card V) {o : Opt V}
    (ho : o ∈ nz (apexStep G lab F al p q excl)) :
    ∃ y, o = Sum.inl y ∧ IsAllowed G lab F {p, q, y} ∧ y ∉ excl := by
  have h1 := thirds_ge H3 ht
  have h2 := apexSet_card_ge (G := G) (lab := lab) (F := F) p q excl
  have hg : al * (Fintype.card V : ℝ) / 2 ≤ (apexSet G lab F p q excl).card := by linarith
  have hpos : 0 < ((apexSet G lab F p q excl).card : ℝ) := by
    have : 0 < al * (Fintype.card V : ℝ) / 2 := by positivity
    linarith
  have hne : (apexSet G lab F p q excl).Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos)
  have heq : apexStep G lab F al p q excl = (apexSet G lab F p q excl).image Sum.inl := by
    unfold apexStep; rw [if_pos hg]
  rw [heq] at ho
  unfold nz at ho
  rw [if_pos (hne.image _)] at ho
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ho
  simp only [apexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  exact ⟨y, rfl, hy.1, hy.2⟩

/-! ## Hinge queries at reachable histories -/

/-- The threshold `n₀ = 2 R 2^M / α`, `R = 12h + 3`, `M = h choose 2`. -/
def nZero (al : ℝ) (hh : ℕ) : ℝ := 2 * (12 * hh + 3) * 2 ^ (hh.choose 2) / al

/-- An answer of a guarded hinge query whose guard holds. -/
theorem hinge_mem (H4 : HingeCond G lab F al hh) (hal : 0 < al)
    (hn0 : nZero al hh ≤ (Fintype.card V : ℝ)) {p q x y : V}
    (d1 : p ≠ q) (d2 : p ≠ x) (d3 : q ≠ x) (d4 : p ≠ y) (d5 : q ≠ y) (d6 : x ≠ y)
    (hx : IsAllowed G lab F {p, q, x}) (hy : IsAllowed G lab F {p, q, y})
    {Hs : Finset V} (hsub : ({p, q, x, y} : Finset V) ⊆ Hs)
    (hcard : (Hs.card : ℝ) ≤ 12 * hh + 3) {o : Opt V}
    (ho : o ∈ nz (hingeStep G lab F al hh p q x y Hs)) :
    ∃ J, o = Sum.inr J ∧ IsHinge G lab F p q x y J ∧
      Disjoint (support J) (Hs \ {p, q, x, y}) ∧ (support J).card ≤ hh := by
  set n := (Fintype.card V : ℝ)
  have hR0 : (0 : ℝ) < 12 * hh + 3 := by positivity
  have hn : 0 < n := lt_of_lt_of_le (by unfold nZero; positivity) hn0
  have hc : ∃ i, 6 ≤ i ∧ i ≤ hh ∧ al * n ^ (i - 4) ≤ (hinges G lab F p q x y i).card :=
    H4 p q x y d6 hx hy
  set i := ordH G lab F al hh p q x y with hi
  have hspec : 6 ≤ i ∧ i ≤ hh ∧ al * n ^ (i - 4) ≤ (hinges G lab F p q x y i).card := by
    have : i = Nat.find hc := by rw [hi]; unfold ordH; rw [dif_pos hc]
    rw [this]; exact Nat.find_spec hc
  obtain ⟨hi6, hih, hicard⟩ := hspec
  -- fresh count
  have hZ : Disjoint (Hs \ {p, q, x, y}) {p, q, x, y} := Finset.sdiff_disjoint
  have hfr := card_fresh_ge (G := G) (lab := lab) (F := F) d1 d2 d3 d4 d5 d6 i
    (Hs \ {p, q, x, y}) hZ
  have hZc : ((Hs \ {p, q, x, y}).card : ℝ) ≤ 12 * hh + 3 :=
    le_trans (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) hcard
  have hM : (2 : ℝ) ^ (i.choose 2) ≤ 2 ^ (hh.choose 2) :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
  have hpow : n ^ (i - 4) = n * n ^ (i - 5) := by
    rw [← pow_succ']; congr 1; omega
  have hn0' : 2 * (12 * hh + 3) * 2 ^ (hh.choose 2) ≤ al * n := by
    have := hn0; unfold nZero at this; rwa [div_le_iff₀ hal, mul_comm n al] at this
  have hbad : ((Hs \ {p, q, x, y}).card : ℝ) * (2 ^ (i.choose 2) * n ^ (i - 5)) ≤
      al / 2 * n ^ (i - 4) := by
    rw [hpow]
    have h5 : 0 ≤ n ^ (i - 5) := by positivity
    calc ((Hs \ {p, q, x, y}).card : ℝ) * (2 ^ (i.choose 2) * n ^ (i - 5))
        ≤ (12 * hh + 3) * (2 ^ (hh.choose 2) * n ^ (i - 5)) := by gcongr
      _ = ((12 * hh + 3) * 2 ^ (hh.choose 2)) * n ^ (i - 5) := by ring
      _ ≤ (al * n / 2) * n ^ (i - 5) := by gcongr; linarith
      _ = al / 2 * (n * n ^ (i - 5)) := by ring
  have hfresh : al / 2 * n ^ (i - 4) ≤ (freshSet G lab F al hh p q x y Hs).card := by
    unfold freshSet; rw [← hi]; linarith
  have hok : hingeOK G lab F al hh p q x y Hs :=
    ⟨d1, d2, d3, d4, d5, d6, hsub, by omega, hih, hfresh⟩
  have hpos : 0 < ((freshSet G lab F al hh p q x y Hs).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hfresh
  have hne : (freshSet G lab F al hh p q x y Hs).Nonempty :=
    Finset.card_pos.1 (by exact_mod_cast hpos)
  have heq : hingeStep G lab F al hh p q x y Hs =
      (freshSet G lab F al hh p q x y Hs).image Sum.inr := by
    unfold hingeStep; rw [if_pos hok]
  rw [heq] at ho
  unfold nz at ho
  rw [if_pos (hne.image _)] at ho
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.1 ho
  simp only [freshSet, Finset.mem_filter, hinges, Finset.mem_univ, true_and] at hJ
  refine ⟨J, rfl, hJ.1.1, hJ.2, ?_⟩
  rw [hJ.1.2]; exact hih

end S10V23.Proc
