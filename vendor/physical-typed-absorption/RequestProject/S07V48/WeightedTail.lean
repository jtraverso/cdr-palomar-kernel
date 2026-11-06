/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07.HingeCore
@[expose] public section

/-!
# V48 — weighted one-vertex completion tests under the full finite Bernoulli process

Everything here uses the project's own finite Bernoulli machinery (`S07V24.bexp`, `bprob`,
`tail_lower`, `tail_upper`); no new concentration provider is introduced.

* `wsum c W = ∑ a ∈ W, c a` — a weighted one-vertex sampling statistic;
  `bexp_wsum`: its mean is exactly `q · ∑ a, c a`.
* `wtail_lo`, `wtail_hi` — for `0 ≤ c ≤ M`, `∑ c = S > 0` and `0 ≤ s ≤ 2S`,
  `P(wsum c W ≤ qS - s) ≤ exp(-s²/(4MS))` and `P(qS + s ≤ wsum c W) ≤ exp(-s²/(4MS))`.
* `DiffuseSeed G lab F C φ` — an ORIGINAL exact fractional seed (load exactly `1` on every
  host edge, the `H1Load` shape) whose weights on every allowed triangle lie in
  `[1/(C n), C/n]`.
* `compW G lab F φ u v a` — the completion weight `φ {u,v,a}` if `{u,v,a}` is allowed, else `0`
  (an allowed triangle has three distinct vertices, so `a = u` and `a = v` never count).
* `sum_compW_eq_one` — for an exact seed, the completion weights of every host edge sum to `1`.
* `sampW G lab F φ W u v` — the sampled completion sum `∑ a ∈ W, compW … u v a`.
* `fam_seed_lo`, `fam_seed_hi` — one host edge fails the relative test with tolerance `δ ≤ 1`
  with probability `≤ exp(-(δ² q² / (4C)) n)` (each side).
* `seedBad`, `seed_failure_budget` — the simultaneous weighted-completion family over ALL ordered
  host edges (roots inside or outside `W`); total failure budget `≤ 2 n² exp(-(δ²q²/(4C)) n)`.
-/

open Finset

namespace S07V48

open TypedTriangle.SparseEdge S07V24

section General

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℝ}

/-- the weighted one-vertex sampling statistic -/
def wsum (c : V → ℝ) (W : Finset V) : ℝ := ∑ a ∈ W, c a

omit [Fintype V] in
lemma wsum_insert (c : V → ℝ) {W : Finset V} {a : V} (ha : a ∉ W) :
    wsum c (insert a W) = c a + wsum c W := by
  unfold wsum; rw [sum_insert ha]

/-- the mean of a weighted one-vertex statistic -/
lemma bexp_wsum (c : V → ℝ) : bexp q (univ : Finset V) (wsum c) = q * ∑ a, c a := by
  have : wsum c = fun W => ∑ a : V, c a * (if ({a} : Finset V) ⊆ W then (1 : ℝ) else 0) := by
    ext W
    unfold wsum
    simp only [singleton_subset_iff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, univ_inter]
  rw [this, bexp_sum, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [bexp_smul, bexp_subset_ind univ _ (subset_univ _), card_singleton, pow_one, mul_comm]

omit [Fintype V] in
lemma wsum_diff (c : V → ℝ) (W : Finset V) (a : V) (ha : a ∉ W) (hc : 0 ≤ c a) :
    |wsum c (insert a W) - wsum c W| ≤ c a := by
  rw [wsum_insert c ha, add_sub_cancel_right, abs_of_nonneg hc]

omit [DecidableEq V] in
lemma sum_sq_le (c : V → ℝ) {M : ℝ} (hc0 : ∀ a, 0 ≤ c a) (hcM : ∀ a, c a ≤ M) :
    ∑ a ∈ (univ : Finset V), c a ^ 2 ≤ M * ∑ a, c a := by
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  rw [sq]; exact mul_le_mul_of_nonneg_right (hcM a) (hc0 a)

omit [Fintype V] [DecidableEq V] in
/-- exponent arithmetic shared by both tails -/
lemma exponent_bound {M S s Q : ℝ} (hM : 0 < M) (hS : 0 < S) (hQ : Q ≤ M * S) :
    -(s / (2 * M * S) * s) + (s / (2 * M * S)) ^ 2 * Q ≤ -(s ^ 2 / (4 * M * S)) := by
  have h1 : (s / (2 * M * S)) ^ 2 * Q ≤ (s / (2 * M * S)) ^ 2 * (M * S) :=
    mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
  have e : -(s / (2 * M * S) * s) + (s / (2 * M * S)) ^ 2 * (M * S) = -(s ^ 2 / (4 * M * S)) := by
    field_simp; ring
  linarith

/-- **weighted lower tail** -/
theorem wtail_lo (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : V → ℝ) {M S s : ℝ}
    (hc0 : ∀ a, 0 ≤ c a) (hcM : ∀ a, c a ≤ M) (hM : 0 < M) (hS : ∑ a, c a = S) (hSpos : 0 < S)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 * S) :
    bprob q univ (fun W => wsum c W ≤ q * S - s) ≤ Real.exp (-(s ^ 2 / (4 * M * S))) := by
  set l := s / (2 * M * S) with hl
  have hl0 : 0 ≤ l := by positivity
  have hlc : ∀ a ∈ (univ : Finset V), l * c a ≤ 1 := by
    intro a _
    calc l * c a ≤ l * M := mul_le_mul_of_nonneg_left (hcM a) hl0
      _ = s / (2 * S) := by rw [hl]; field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hs
  have ht := tail_lower hq0 hq1 c hl0 univ (wsum c)
    (fun W _ a _ ha => wsum_diff c W a ha (hc0 a)) hlc s
  rw [bexp_wsum, hS] at ht
  refine ht.trans (Real.exp_le_exp.2 ?_)
  exact exponent_bound hM hSpos (by rw [← hS]; exact sum_sq_le c hc0 hcM)

/-- **weighted upper tail** -/
theorem wtail_hi (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : V → ℝ) {M S s : ℝ}
    (hc0 : ∀ a, 0 ≤ c a) (hcM : ∀ a, c a ≤ M) (hM : 0 < M) (hS : ∑ a, c a = S) (hSpos : 0 < S)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 * S) :
    bprob q univ (fun W => q * S + s ≤ wsum c W) ≤ Real.exp (-(s ^ 2 / (4 * M * S))) := by
  set l := s / (2 * M * S) with hl
  have hl0 : 0 ≤ l := by positivity
  have hlc : ∀ a ∈ (univ : Finset V), l * c a ≤ 1 := by
    intro a _
    calc l * c a ≤ l * M := mul_le_mul_of_nonneg_left (hcM a) hl0
      _ = s / (2 * S) := by rw [hl]; field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hs
  have ht := tail_upper hq0 hq1 c hl0 univ (wsum c)
    (fun W _ a _ ha => wsum_diff c W a ha (hc0 a)) hlc s
  rw [bexp_wsum, hS] at ht
  refine ht.trans (Real.exp_le_exp.2 ?_)
  exact exponent_bound hM hSpos (by rw [← hS]; exact sum_sq_le c hc0 hcM)

end General

section Seed

variable {V I : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- the completion weight of `a` for the edge `uv` -/
noncomputable def compW (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) (u v a : V) : ℝ :=
  if IsAllowed G lab F {u, v, a} then φ {u, v, a} else 0

open Classical in
/-- an ORIGINAL exact diffuse fractional seed: load exactly `1` on every host edge (the
`H1Load` shape) and weights in `[1/(C n), C/n]` on every allowed triangle -/
def DiffuseSeed (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (C : ℝ)
    (φ : Finset V → ℝ) : Prop :=
  (∀ T, IsAllowed G lab F T →
    1 / (C * Fintype.card V) ≤ φ T ∧ φ T ≤ C / Fintype.card V) ∧
  ∀ e ∈ edges G, ∑ T ∈ univ.filter (fun T => IsAllowed G lab F T ∧ e ∈ triEdges T), φ T = 1

/-- the sampled completion sum of the edge `uv` over `W` -/
noncomputable def sampW (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) (W : Finset V) (u v : V) : ℝ :=
  wsum (compW G lab F φ u v) W

omit [Fintype V] in
lemma allowed_third {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v : V}
    (huv : u ≠ v) {T : Finset V} (hT : IsAllowed G lab F T) (hu : u ∈ T) (hv : v ∈ T) :
    ∃ a, T = {u, v, a} := by
  have hsub : ({u, v} : Finset V) ⊆ T := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
  have hc : (T \ {u, v}).card = 1 := by
    rw [card_sdiff_of_subset hsub, hT.1, card_pair huv]
  obtain ⟨a, ha⟩ := card_eq_one.1 hc
  refine ⟨a, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxuv : x ∈ ({u, v} : Finset V)
    · simp only [mem_insert, mem_singleton] at hxuv ⊢; tauto
    · have : x ∈ T \ {u, v} := mem_sdiff.2 ⟨hx, hxuv⟩
      rw [ha, mem_singleton] at this
      simp [this]
  · intro hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · have : x ∈ T \ {u, v} := by rw [ha]; exact mem_singleton_self _
      exact (mem_sdiff.1 this).1

open Classical in
/-- completion weights of an edge = the edge load of the seed -/
theorem sum_compW_eq_load (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) {u v : V} (huv : u ≠ v) :
    ∑ a, compW G lab F φ u v a =
      ∑ T ∈ univ.filter (fun T => IsAllowed G lab F T ∧ s(u, v) ∈ triEdges T), φ T := by
  classical
  have h1 : ∑ a, compW G lab F φ u v a =
      ∑ a ∈ univ.filter (fun a => IsAllowed G lab F {u, v, a}), φ {u, v, a} := by
    rw [sum_filter]; rfl
  rw [h1]
  have hinj : Set.InjOn (fun a => ({u, v, a} : Finset V))
      (univ.filter (fun a => IsAllowed G lab F {u, v, a}) : Set V) := by
    intro a ha b hb hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha hb
    obtain ⟨-, hua, hva⟩ := distinct_of_allowed ha
    have : a ∈ ({u, v, b} : Finset V) := by
      rw [← show ({u, v, a} : Finset V) = {u, v, b} from hab]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact absurd h.symm hua
    · exact absurd h.symm hva
    · exact h
  rw [← sum_image (f := φ) hinj]
  apply sum_congr _ (fun _ _ => rfl)
  ext T
  simp only [mem_image, mem_filter, mem_univ, true_and, mem_triEdges]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, by simp, by simp, huv⟩
  · rintro ⟨hT, hu, hv, -⟩
    obtain ⟨a, rfl⟩ := allowed_third huv hT hu hv
    exact ⟨a, hT, rfl⟩

/-- for an exact seed, the completion weights of every host edge sum to `1` -/
theorem sum_compW_eq_one {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) {u v : V} (huv : G.Adj u v) :
    ∑ a, compW G lab F φ u v a = 1 := by
  rw [sum_compW_eq_load G lab F φ huv.ne]
  exact hφ.2 _ (mem_edges.2 ((SimpleGraph.mem_edgeSet G).2 huv))

lemma compW_nonneg {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (u v a : V) :
    0 ≤ compW G lab F φ u v a := by
  unfold compW
  split_ifs with h
  · exact le_trans (by positivity) (hφ.1 _ h).1
  · exact le_rfl

lemma compW_le {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (u v a : V) :
    compW G lab F φ u v a ≤ C / Fintype.card V := by
  unfold compW
  split_ifs with h
  · exact (hφ.1 _ h).2
  · positivity

/-- **one host edge, lower side** -/
theorem fam_seed_lo {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C q δ : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < Fintype.card V) {u v : V} (huv : G.Adj u v) :
    bprob q univ (fun W => sampW G lab F φ W u v < q - δ * q) ≤
      Real.exp (-(δ ^ 2 * q ^ 2 / (4 * C) * Fintype.card V)) := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  refine (bprob_mono hq.le hq1 (E := fun W => sampW G lab F φ W u v < q - δ * q)
    (E' := fun W => wsum (compW G lab F φ u v) W ≤ q * 1 - δ * q)
    (iE' := fun _ => inferInstance) (fun W h => by simp only [sampW] at h; linarith)).trans ((wtail_lo hq.le hq1 _ (compW_nonneg hφ hC u v) (compW_le hφ hC u v)
    (by positivity) (sum_compW_eq_one hφ huv) one_pos (by positivity) (by nlinarith)).trans
    (le_of_eq ?_))
  congr 1; field_simp

/-- **one host edge, upper side** -/
theorem fam_seed_hi {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C q δ : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < Fintype.card V) {u v : V} (huv : G.Adj u v) :
    bprob q univ (fun W => q + δ * q < sampW G lab F φ W u v) ≤
      Real.exp (-(δ ^ 2 * q ^ 2 / (4 * C) * Fintype.card V)) := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  refine (bprob_mono hq.le hq1 (E := fun W => q + δ * q < sampW G lab F φ W u v)
    (E' := fun W => q * 1 + δ * q ≤ wsum (compW G lab F φ u v) W)
    (iE' := fun _ => inferInstance) (fun W h => by simp only [sampW] at h; linarith)).trans ((wtail_hi hq.le hq1 _ (compW_nonneg hφ hC u v) (compW_le hφ hC u v)
    (by positivity) (sum_compW_eq_one hφ huv) one_pos (by positivity) (by nlinarith)).trans
    (le_of_eq ?_))
  congr 1; field_simp

/-- the weighted-completion failure events, one per ordered pair and side -/
def seedBad (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (φ : Finset V → ℝ)
    (q δ : ℝ) : V × V × Bool → Finset V → Prop
  | (u, v, true) => fun W => G.Adj u v ∧ sampW G lab F φ W u v < q - δ * q
  | (u, v, false) => fun W => G.Adj u v ∧ q + δ * q < sampW G lab F φ W u v

open Classical in
/-- each weighted-completion failure event has probability `≤ exp(-(δ²q²/(4C)) n)` -/
theorem seedBad_prob {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C q δ : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < Fintype.card V) (j : V × V × Bool) :
    bprob q univ (seedBad G lab F φ q δ j) ≤
      Real.exp (-(δ ^ 2 * q ^ 2 / (4 * C) * Fintype.card V)) := by
  obtain ⟨u, v, b⟩ := j
  by_cases huv : G.Adj u v
  · cases b
    · exact (bprob_mono hq.le hq1 (E := seedBad G lab F φ q δ (u, v, false))
        (E' := fun W => q + δ * q < sampW G lab F φ W u v) (iE' := fun _ => inferInstance)
        (fun W h => h.2)).trans (fam_seed_hi hφ hC hq hq1 hδ hδ1 hn huv)
    · exact (bprob_mono hq.le hq1 (E := seedBad G lab F φ q δ (u, v, true))
        (E' := fun W => sampW G lab F φ W u v < q - δ * q) (iE' := fun _ => inferInstance)
        (fun W h => h.2)).trans (fam_seed_lo hφ hC hq hq1 hδ hδ1 hn huv)
  · rw [bprob_false (fun W h => by cases b <;> exact huv h.1)]
    exact (Real.exp_pos _).le

open Classical in
/-- **the simultaneous weighted-completion family, explicit failure budget** -/
theorem seed_failure_budget {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {C q δ : ℝ}
    {φ : Finset V → ℝ} (hφ : DiffuseSeed G lab F C φ) (hC : 0 < C) (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < Fintype.card V) :
    ∑ j : V × V × Bool, bprob q univ (seedBad G lab F φ q δ j) ≤
      2 * (Fintype.card V : ℝ) ^ 2 * Real.exp (-(δ ^ 2 * q ^ 2 / (4 * C) * Fintype.card V)) := by
  calc ∑ j : V × V × Bool, bprob q univ (seedBad G lab F φ q δ j)
      ≤ ∑ _j : V × V × Bool, Real.exp (-(δ ^ 2 * q ^ 2 / (4 * C) * Fintype.card V)) :=
        sum_le_sum fun j _ => seedBad_prob hφ hC hq hq1 hδ hδ1 hn j
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        simp only [Fintype.card_prod, Fintype.card_bool]
        push_cast; ring

omit [Fintype V] in
/-- a sample avoiding every failure event satisfies the relative profile on every host edge -/
lemma profile_of_not_bad {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {φ : Finset V → ℝ} {q δ : ℝ} (hq : 0 < q) {W : Finset V}
    (hW : ∀ j, ¬ seedBad G lab F φ q δ j W) {u v : V} (huv : G.Adj u v) :
    |sampW G lab F φ W u v / q - 1| ≤ δ := by
  have h1 := hW (u, v, true)
  have h2 := hW (u, v, false)
  simp only [seedBad, not_and, not_lt] at h1 h2
  have a1 := h1 huv
  have a2 := h2 huv
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hq]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hq]; linarith

end Seed

end S07V48
