/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.SourceValidity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23: expectation kernel and conditioned pivots of ONE source

* `src_expect` (S10 (3.1) for one source): `E|c_T(S)| ≤ 14 (12K/n)^(3 - |S ∩ T|)` for every
  `S` (with `K ≥ max 1 (2^(M+1)/α)`). Uses only the first-arrival bound and the facts valid
  for every choice; no H3/H4 needed for THIS inequality (the guards make it hold for every
  history).
* `triOn_eq_image`, `card_apexSet` : permitted triangles through `pq` ↔ permitted thirds.
* `pivot_marginal` : a pivot query whose option set is the (guarded, nonempty) set of thirds
  of `pq` other than `r` gives a pivot `pq b` UNIFORM on `triOn(pq) ∖ {pqr}`.
-/

open Finset

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S10V23.Proc

open TypedTriangle.SparseEdge S10V22 S10V23

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {al : ℝ} {hh : ℕ}

/-- The certificate of an outcome. -/
def certOf (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a : V)
    (ω : Fin 12 → Opt V) : Finset V → ℝ :=
  srcCert G lab F u v a (ob1 u ω) (ob2 u ω) (ob3 u ω) (oc u ω) (oc1 u ω) (oc2 u ω)
    (oJ1 ω) (oJ2 ω) (oJ3 ω) (oJ4 ω) (oJ5 ω) (oJ6 ω)

lemma vsO_G12_subset_aux (ω : Fin 12 → Opt V) {j : ℕ} (hj : j < 12) :
    vsO (G12 ω j) ⊆ Expo.aux vsO ω := by
  intro x hx
  rw [G12_of_lt ω hj] at hx
  exact Finset.mem_biUnion.2 ⟨⟨j, hj⟩, Finset.mem_univ _, hx⟩

lemma support_gJ_subset (o : Opt V) : support (gJ o) ⊆ vsO o := by
  cases o with
  | inl y => intro x hx; simp [gJ, support] at hx
  | inr J => simp [gJ, vsO]

lemma gv_mem (u : V) (o : Opt V) : gv u o ∈ ({u} : Finset V) ∪ vsO o := by
  cases o with
  | inl y => simp [gv, vsO]
  | inr J => simp [gv]

/-- Pointwise: `|c(S)| ≤ 14 · 1[S ∖ T ⊆ revealed]`. -/
lemma certOf_le (u v a : V) (ω : Fin 12 → Opt V) (S : Finset V) :
    |certOf G lab F u v a ω S| ≤ 14 * (if S \ {u, v, a} ⊆ Expo.aux vsO ω then 1 else 0) := by
  by_cases h0 : certOf G lab F u v a ω S = 0
  · rw [h0, abs_zero]; split_ifs <;> norm_num
  · have hJ : ∀ J ∈ [oJ1 ω, oJ2 ω, oJ3 ω, oJ4 ω, oJ5 ω, oJ6 ω],
        support J ⊆ Expo.aux vsO ω := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro J (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        exact (support_gJ_subset _).trans (vsO_G12_subset_aux ω (by norm_num))
    have hpts : ∀ y ∈ [ob1 u ω, ob2 u ω, ob3 u ω, oc u ω, oc1 u ω, oc2 u ω],
        y ∈ ({u, v, a} : Finset V) ∪ Expo.aux vsO ω := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      have key : ∀ j < 12, gv u (G12 ω j) ∈ ({u, v, a} : Finset V) ∪ Expo.aux vsO ω := by
        intro j hj
        rcases Finset.mem_union.1 (gv_mem u (G12 ω j)) with h | h
        · rw [Finset.mem_singleton.1 h]; simp
        · exact Finset.mem_union_right _ (vsO_G12_subset_aux ω hj h)
      rintro y (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact key _ (by norm_num)
    have hv := srcCert_verts (G := G) (lab := lab) (F := F) (Expo.aux vsO ω) hJ hpts h0
    have hsub : S \ {u, v, a} ⊆ Expo.aux vsO ω := by
      intro x hx
      rcases Finset.mem_union.1 (hv (Finset.mem_sdiff.1 hx).1) with h | h
      · exact absurd h (Finset.mem_sdiff.1 hx).2
      · exact h
    rw [if_pos hsub, mul_one]
    exact srcCert_abs_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The expectation kernel of one source (S10 (3.1)).** -/
theorem src_expect {u v a : V} (hal : 0 < al) (hn : 0 < (Fintype.card V : ℝ)) {K : ℝ}
    (hK1 : 1 ≤ K) (hK : 2 ^ (hh.choose 2 + 1) / al ≤ K) (S : Finset V) :
    ∑ ω, Expo.wt (opts G lab F al hh u v a) 12 [] ω * |certOf G lab F u v a ω S| ≤
      14 * (12 * K / Fintype.card V) ^ (3 - (S ∩ {u, v, a}).card) := by
  have hq : 0 ≤ 12 * K / (Fintype.card V : ℝ) := by positivity
  by_cases hS : IsAllowed G lab F S
  · have h3 := hS.1
    have hU : (S \ {u, v, a}).card = 3 - (S ∩ {u, v, a}).card := by
      have := Finset.card_sdiff_add_card_inter S {u, v, a}; omega
    calc ∑ ω, Expo.wt (opts G lab F al hh u v a) 12 [] ω * |certOf G lab F u v a ω S|
        ≤ ∑ ω, Expo.wt (opts G lab F al hh u v a) 12 [] ω *
            (14 * (if S \ {u, v, a} ⊆ Expo.aux vsO ω then 1 else 0)) :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (certOf_le u v a ω S)
            (Expo.wt_nonneg _ _ _ _)
      _ = 14 * ∑ ω, Expo.wt (opts G lab F al hh u v a) 12 [] ω *
            (if S \ {u, v, a} ⊆ Expo.aux vsO ω then 1 else 0) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ 14 * (12 * K / Fintype.card V) ^ (S \ {u, v, a}).card := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact exposure_src G lab F al hh u v a hal hn hK1 hK _
            ((Finset.card_le_card Finset.sdiff_subset).trans h3.le) Finset.sdiff_disjoint
      _ = 14 * (12 * K / Fintype.card V) ^ (3 - (S ∩ {u, v, a}).card) := by rw [hU]
  · have : ∀ ω, certOf G lab F u v a ω S = 0 := fun ω => by
      by_contra h; exact hS (srcCert_supp h)
    simp only [this, abs_zero, mul_zero, Finset.sum_const_zero]
    positivity

/-! ## Conditioned pivots -/

lemma triOn_eq_image {p q : V} (hpq : p ≠ q) :
    triOn (allowedTri G lab F) s(p, q) =
      (univ.filter (fun y => IsAllowed G lab F {p, q, y})).image (fun y => ({p, q, y} : Finset V)) := by
  ext S
  simp only [mem_triOn, mem_allowedTri, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hS, he⟩
    obtain ⟨hp, hq, -⟩ := mem_edgesOf.1 he
    obtain ⟨y, -, -, rfl⟩ := eq_triple_of_mem hS.1 hp hq hpq
    exact ⟨y, hS, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, mem_edgesOf.2 ⟨by simp, by simp, hpq⟩⟩

omit [Fintype V] in
lemma triple_injOn {p q : V} {y y' : V} (hy : y ≠ p ∧ y ≠ q)
    (h : ({p, q, y} : Finset V) = {p, q, y'}) : y = y' := by
  have : y ∈ ({p, q, y'} : Finset V) := h ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h1 | h1 | h1
  · exact absurd h1 hy.1
  · exact absurd h1 hy.2
  · exact h1

lemma card_triOn {p q : V} (hpq : p ≠ q) :
    (triOn (allowedTri G lab F) s(p, q)).card =
      (univ.filter (fun y => IsAllowed G lab F {p, q, y})).card := by
  rw [triOn_eq_image hpq]
  refine Finset.card_image_of_injOn fun y hy y' _ h => ?_
  simp only [coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hy
  obtain ⟨-, h1, h2⟩ := distinct_of_card_three hy.1
  exact triple_injOn ⟨Ne.symm h1, Ne.symm h2⟩ h

lemma card_apexSet {p q r : V} (hT : IsAllowed G lab F {p, q, r}) :
    ((apexSet G lab F p q {r}).card : ℝ) = (triOn (allowedTri G lab F) s(p, q)).card - 1 := by
  obtain ⟨hpq, -, -⟩ := distinct_of_card_three hT.1
  rw [card_triOn hpq]
  have : univ.filter (fun y => IsAllowed G lab F {p, q, y}) =
      insert r (apexSet G lab F p q {r}) := by
    ext y
    simp only [apexSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hy; by_cases h : y = r
      · exact Or.inl h
      · exact Or.inr ⟨hy, h⟩
    · rintro (rfl | ⟨hy, -⟩)
      · exact hT
      · exact hy
  rw [this, Finset.card_insert_of_notMem (by simp [apexSet])]
  push_cast; ring

/-- Number of thirds `y ≠ r` with `pqy = S`. -/
lemma card_filter_apexSet {p q r : V} (hT : IsAllowed G lab F {p, q, r}) (S : Finset V) :
    (((apexSet G lab F p q {r}).filter (fun y => ({p, q, y} : Finset V) = S)).card : ℝ) =
      if S ∈ (triOn (allowedTri G lab F) s(p, q)).erase {p, q, r} then 1 else 0 := by
  obtain ⟨hpq, hpr, hqr⟩ := distinct_of_card_three hT.1
  split_ifs with hS
  · obtain ⟨hSne, hS⟩ := Finset.mem_erase.1 hS
    rw [triOn_eq_image hpq] at hS
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨-, h1, h2⟩ := distinct_of_card_three hy.1
    have hyr : y ≠ r := fun h => hSne (h ▸ rfl)
    have : (apexSet G lab F p q {r}).filter (fun y' => ({p, q, y'} : Finset V) = {p, q, y}) =
        {y} := by
      ext y'
      simp only [apexSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hy', -⟩, he⟩
        obtain ⟨-, h1', h2'⟩ := distinct_of_card_three hy'.1
        exact triple_injOn ⟨Ne.symm h1', Ne.symm h2'⟩ he
      · rintro rfl; exact ⟨⟨hy, hyr⟩, rfl⟩
    rw [this]; simp
  · have : (apexSet G lab F p q {r}).filter (fun y => ({p, q, y} : Finset V) = S) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun y hy he => hS ?_
      simp only [apexSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hy
      refine Finset.mem_erase.2 ⟨fun h => hy.2 ?_, ?_⟩
      · rw [← he] at h
        obtain ⟨-, h1, h2⟩ := distinct_of_card_three hy.1.1
        exact triple_injOn ⟨Ne.symm h1, Ne.symm h2⟩ h
      · rw [← he, mem_triOn, mem_allowedTri]
        exact ⟨hy.1, mem_edgesOf.2 ⟨by simp, by simp, hpq⟩⟩
    rw [this]; simp

/-- **Conditioned pivot marginal.** -/
theorem pivot_marginal {u v a : V} {p q r d : V} (hT : IsAllowed G lab F {p, q, r})
    (k : ℕ) (hk : k < 12)
    (hopts : ∀ h' : List (Opt V), h'.length = k →
      opts G lab F al hh u v a h' = (apexSet G lab F p q {r}).image Sum.inl)
    (S : Finset V) :
    ∑ ω, Expo.wt (opts G lab F al hh u v a) 12 [] ω *
        (if ({p, q, gv d (ω ⟨k, hk⟩)} : Finset V) = S then 1 else 0) =
      if S ∈ (triOn (allowedTri G lab F) s(p, q)).erase {p, q, r} then
        1 / (((triOn (allowedTri G lab F) s(p, q)).card : ℝ) - 1) else 0 := by
  set s := (apexSet G lab F p q {r}).image (Sum.inl : V → Opt V)
  have hsc : (s.card : ℝ) = (apexSet G lab F p q {r}).card := by
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
  -- decompose the event by the value of answer `k`
  have hdec : ∀ ω : Fin 12 → Opt V,
      (if ({p, q, gv d (ω ⟨k, hk⟩)} : Finset V) = S then (1 : ℝ) else 0) =
        ∑ x : Opt V, (if ω ⟨k, hk⟩ = x then 1 else 0) *
          (if ({p, q, gv d x} : Finset V) = S then 1 else 0) := by
    intro ω
    rw [Finset.sum_eq_single (ω ⟨k, hk⟩)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp_rw [hdec, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hmarg : ∀ x : Opt V, ∑ ω : Fin 12 → Opt V, Expo.wt (opts G lab F al hh u v a) 12 [] ω *
      ((if ω ⟨k, hk⟩ = x then 1 else 0) * (if ({p, q, gv d x} : Finset V) = S then 1 else 0)) =
      (if x ∈ s then (s.card : ℝ)⁻¹ else 0) *
        (if ({p, q, gv d x} : Finset V) = S then 1 else 0) := by
    intro x
    have := Expo.marginal_const (opts G lab F al hh u v a) (opts_nonempty G lab F al hh u v a)
      s x k 12 [] hk (fun h' hl => hopts h' (by simpa using hl))
    rw [← this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => by ring
  simp_rw [hmarg]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_image (fun x _ y _ h => Sum.inl_injective h)]
  simp only [gv, Sum.elim_inl, id, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    card_filter_apexSet hT S, hsc, card_apexSet hT]
  split_ifs <;> simp [div_eq_inv_mul]

end S10V23.Proc
