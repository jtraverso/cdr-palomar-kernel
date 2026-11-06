/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.Bernoulli
public import RequestProject.S07.PathCount

@[expose] public section

/-!
# V24 / S07 §2: ONE random core preserving all the robust path families

Host vertex type `V`, `|V| = n`. Links `L v : SimpleGraph V` (one per root `v`) and an
admissibility predicate `adm v x y`. The interface consumed here is exactly the conclusion of
S07 (1.1) (proved in `ManyOddPaths.lean` from degree + expansion of each component / cover):
`a n^m ≤ #(simple paths of length m+1 from x to y in L v)` for admissible `(v,x,y)`.
Linear candidate pools `P i` (`|P i| ≥ β n`, at most `n²` of them) are also preserved.

* `pay_deterministic` — after `W` is FIXED: if at least `K` admissible paths have all internal
  vertices in `W` and `(m|Z| + (m+1)d) N^(m-1) < K`, then for EVERY vertex set `Z` and EVERY
  graph `B` of maximum degree `≤ d` there is such a path avoiding `Z` internally and using no
  edge of `B`. Pure counting; no probability, no union over deletion graphs.
* `random_core` — the constants `n₀` and the window `ε` depend only on `(a, β, q, m)`; for
  every host with `n ≥ n₀` there is ONE `W` with `qn/2 ≤ |W| < 2qn`,
  `|P i ∩ W| ≥ qβn/2` for all pools, and at least `a q^m n^m / 2` admissible paths inside `W`
  for every admissible test (at most `n³` tests). It is obtained from the full finite
  Bernoulli process (`Bernoulli.lean`): bounded differences + the finite union bound.
* `random_core_robust` — the same `W`, and then simultaneously for all `Z` with `|Z| ≤ εn`
  and all `B` with `Δ(B) ≤ εn`, every admissible test still has a surviving path in `W`.
-/

open Finset

namespace S07V24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- the set of internal vertices of a walk of length `m+1` -/
def intlSet {G : SimpleGraph V} (m : ℕ) {x y : V} (p : G.Walk x y) : Finset V :=
  univ.image (intl m p)

omit [Fintype V] in
lemma mem_intlSet {G : SimpleGraph V} (m : ℕ) {x y : V} (p : G.Walk x y) (a : V) :
    a ∈ intlSet m p ↔ ∃ i : Fin m, intl m p i = a := by
  simp [intlSet]

/-- paths of length `m+1` whose internal vertices all lie in `W` -/
def pathsIn (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V) (W : Finset V) :
    Finset (G.Walk x y) :=
  (pathsLen G (m + 1) x y).filter fun p => intlSet m p ⊆ W

/-- **Deterministic payment after fixing `W`.** -/
theorem pay_deterministic (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V)
    (W : Finset V) {K : ℝ} (hK : K ≤ (pathsIn G m x y W).card)
    (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ) (hB : ∀ u, B.degree u ≤ d)
    (hwin : ((Z.card * m + (m + 1) * d : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (m - 1) < K) :
    ∃ p ∈ pathsLen G (m + 1) x y, intlSet m p ⊆ W ∧ (∀ i : Fin m, intl m p i ∉ Z) ∧
      ∀ k < m + 1, ¬ B.Adj (p.getVert k) (p.getVert (k + 1)) := by
  set A := pathsIn G m x y W
  have hA : ∀ p ∈ A, p.length = m + 1 := by
    intro p hp
    simp only [A, pathsIn, pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp
    exact hp.1.1
  have h1 := card_through_le m x y A hA Z
  have h2 := card_edgeB_le m x y A hA B d hB
  by_contra hne
  push_neg at hne
  have hcover : A ⊆ (A.filter fun p => ∃ i : Fin m, intl m p i ∈ Z) ∪
      (A.filter fun p : G.Walk x y => ∃ k ∈ Finset.range (m + 1),
        B.Adj (p.getVert k) (p.getVert (k + 1))) := by
    intro p hp
    have hp' := hp
    simp only [A, pathsIn, mem_filter] at hp'
    by_cases hZ : ∃ i : Fin m, intl m p i ∈ Z
    · exact mem_union_left _ (mem_filter.2 ⟨hp, hZ⟩)
    · push_neg at hZ
      obtain ⟨k, hk, hadj⟩ := hne p hp'.1 hp'.2 hZ
      exact mem_union_right _ (mem_filter.2 ⟨hp, k, Finset.mem_range.2 hk, hadj⟩)
  have h3 := (card_le_card hcover).trans (card_union_le _ _)
  have h4 : (A.card : ℝ) ≤ ((Z.card * m + (m + 1) * d : ℕ) : ℝ) *
      (Fintype.card V : ℝ) ^ (m - 1) := by
    have : A.card ≤ (Z.card * m + (m + 1) * d) * Fintype.card V ^ (m - 1) := by
      calc A.card ≤ _ := h3
        _ ≤ Z.card * m * Fintype.card V ^ (m - 1) + (m + 1) * d * Fintype.card V ^ (m - 1) :=
            add_le_add h1 h2
        _ = _ := by ring
    exact_mod_cast this
  linarith

/-! ### Probability bookkeeping -/

omit [DecidableEq V] in
lemma bprob_mono {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {E E' : Finset V → Prop}
    {iE : DecidablePred E} {iE' : DecidablePred E'} (h : ∀ W, E W → E' W) :
    bprob q univ E ≤ bprob q univ E' := by
  unfold bprob; apply bexp_mono hq0 hq1; intro W _
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h W h1) h2
  · norm_num
  · exact le_rfl

omit [DecidableEq V] in
lemma bprob_false {q : ℝ} {E : Finset V → Prop} {_ : DecidablePred E} (h : ∀ W, ¬ E W) :
    bprob q univ E = 0 := by
  unfold bprob; rw [bexp_congr (g := fun _ => 0)]; · exact bexp_const _ 0
  intro W _; rw [if_neg (h W)]

omit [Fintype V] in
lemma ccount_singleton (P W : Finset V) :
    ccount P (fun a => ({a} : Finset V)) W = (P ∩ W).card := by
  unfold ccount; congr 1; ext a; simp

lemma bexp_card {q : ℝ} : bexp q (univ : Finset V) (fun W => (W.card : ℝ)) =
    q * Fintype.card V := by
  have : (fun W : Finset V => (W.card : ℝ)) =
      fun W => ∑ a : V, (if ({a} : Finset V) ⊆ W then (1 : ℝ) else 0) := by
    ext W; rw [Finset.sum_boole]; congr 2; ext a; simp
  rw [this, bexp_sum]
  simp only [bexp_subset_ind univ _ (subset_univ _), card_singleton, pow_one,
    sum_const, card_univ, nsmul_eq_mul]; ring

/-- the exponential beats `4 n³` -/
lemma four_cube_exp_lt {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 96 / θ ^ 4 < n) :
    4 * (n : ℝ) ^ 3 * Real.exp (-(θ * n)) < 1 := by
  have hnpos : (0 : ℝ) < n := lt_trans (by positivity) hn
  have hx : 0 ≤ θ * n := by positivity
  have h1 := Real.pow_div_factorial_le_exp (θ * n) hx 4
  norm_num [Nat.factorial] at h1
  have hexp : Real.exp (-(θ * n)) ≤ 24 / (θ * n) ^ 4 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 24)]; linarith
  calc 4 * (n : ℝ) ^ 3 * Real.exp (-(θ * n)) ≤ 4 * (n : ℝ) ^ 3 * (24 / (θ * n) ^ 4) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 96 / (θ ^ 4 * n) := by field_simp; ring
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hn; linarith

/-- the decay rate (depends only on the constants) -/
noncomputable def thetaOf (a β q : ℝ) (m : ℕ) : ℝ :=
  min (a * q ^ (2 * m) / (16 * m ^ 2)) (min (β * q ^ 2 / 16) (q ^ 2 / 16))

/-- the threshold (depends only on the constants) -/
noncomputable def n0Core (a β q : ℝ) (m : ℕ) : ℕ := ⌈96 / thetaOf a β q m ^ 4⌉₊ + 1

/-- **S07 §2: one random core** (existence via the full finite Bernoulli process). -/
theorem random_core (a β q : ℝ) (m : ℕ) (ha : 0 < a) (hβ : 0 < β) (hq : 0 < q) (hq1 : q ≤ 1)
    (hm : 0 < m) (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) (hV : Fintype.card V = n)
    (hn : n0Core a β q m ≤ n)
    (L : V → SimpleGraph V) [∀ v, DecidableRel (L v).Adj]
    (adm : V → V → V → Prop) [∀ v x y, Decidable (adm v x y)]
    (hpaths : ∀ v x y, adm v x y → a * (n : ℝ) ^ m ≤ (pathsLen (L v) (m + 1) x y).card)
    (ι : Type*) [Fintype ι] (hι : Fintype.card ι ≤ n ^ 2) (P : ι → Finset V)
    (hP : ∀ i, β * n ≤ (P i).card) :
    ∃ W : Finset V, q * n / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * n ∧
      (∀ i, q * β * n / 2 ≤ (P i ∩ W).card) ∧
      ∀ v x y, adm v x y → a * q ^ m * (n : ℝ) ^ m / 2 ≤ (pathsIn (L v) m x y W).card := by
  set θ := thetaOf a β q m with hθdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ1 : 0 < a * q ^ (2 * m) / (16 * m ^ 2) := by positivity
  have hθpos : 0 < θ := lt_min hθ1 (lt_min (by positivity) (by positivity))
  have hθle1 : θ ≤ a * q ^ (2 * m) / (16 * m ^ 2) := min_le_left _ _
  have hθle2 : θ ≤ β * q ^ 2 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hθle3 : θ ≤ q ^ 2 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hnθ : 96 / θ ^ 4 < n := by
    have := Nat.le_ceil (96 / θ ^ 4)
    have h2 : ((n0Core a β q m : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    unfold n0Core at h2; push_cast at h2; rw [← hθdef] at h2; linarith
  have hnR : (0 : ℝ) < n := lt_trans (by positivity) hnθ
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by
    have : (0:ℝ) < n := hnR; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      intro h; rw [h] at this; simp at this))
  have hq0 := hq.le
  classical
  -- the bad events
  let Idx := (V × V × V) ⊕ (ι ⊕ Bool)
  let bad : Idx → Finset V → Prop := fun j W => match j with
    | Sum.inl (v, x, y) => adm v x y ∧
        ((pathsIn (L v) m x y W).card : ℝ) < a * (n : ℝ) ^ m * q ^ m / 2
    | Sum.inr (Sum.inl i) => (((P i) ∩ W).card : ℝ) < β * n * q ^ 1 / 2
    | Sum.inr (Sum.inr true) => (W.card : ℝ) < n * q ^ 1 / 2
    | Sum.inr (Sum.inr false) => q * n + q * n ≤ (W.card : ℝ)
  have hE : ∀ j, bprob q univ (bad j) ≤ Real.exp (-(θ * n)) := by
    intro j
    rcases j with ⟨v, x, y⟩ | i | b
    · refine (bprob_mono hq0 hq1 (E := bad (Sum.inl (v, x, y))) (E' := fun W => adm v x y ∧
        ((pathsIn (L v) m x y W).card : ℝ) < a * (n : ℝ) ^ m * q ^ m / 2)
        (iE' := fun W => instDecidableAnd) (fun W h => h)).trans ?_
      by_cases hadm : adm v x y
      · set I := pathsLen (L v) (m + 1) x y
        have hle : bprob q univ (fun W => adm v x y ∧
            ((pathsIn (L v) m x y W).card : ℝ) < a * (n : ℝ) ^ m * q ^ m / 2) ≤
            bprob q univ (fun W => (ccount I (fun p => intlSet m p) W : ℝ) <
              a * (n : ℝ) ^ m * q ^ m / 2) :=
          bprob_mono hq0 hq1 (fun W h => by simpa [ccount, pathsIn] using h.2)
        refine hle.trans ((count_tail hq hq1 I (fun p => intlSet m p) hm
          (fun p _ => (card_image_le).trans (by simp)) (Δ := m * (n : ℝ) ^ (m - 1))
          (by positivity) ?_ (hpaths v x y hadm)).trans ?_)
        · intro z
          have hA : ∀ p ∈ I, p.length = m + 1 := by
            intro p hp
            simp only [I, pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp
            exact hp.1
          have := card_through_le m x y I hA {z}
          have heq : (I.filter fun p => z ∈ intlSet m p) =
              I.filter fun p => ∃ i : Fin m, intl m p i ∈ ({z} : Finset V) := by
            apply Finset.filter_congr; intro p _; simp [mem_intlSet]
          rw [heq]
          have h2 : ((I.filter fun p => ∃ i : Fin m, intl m p i ∈ ({z} : Finset V)).card : ℝ) ≤
              (({z} : Finset V).card * m * Fintype.card V ^ (m - 1) : ℕ) := by exact_mod_cast this
          rw [hV] at h2; push_cast at h2; simpa using h2
        · apply Real.exp_le_exp.2
          have e : a * (n : ℝ) ^ m * q ^ (2 * m) / (16 * (m * (n : ℝ) ^ (m - 1)) * m) =
              a * q ^ (2 * m) / (16 * m ^ 2) * n := by
            have : (n : ℝ) ^ m = (n : ℝ) ^ (m - 1) * n := by
              rw [← pow_succ, Nat.sub_add_cancel hm]
            rw [this]; field_simp
          rw [e]; nlinarith
      · rw [bprob_false (fun W h => hadm h.1)]; exact (Real.exp_pos _).le
    · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inl i)))
        (E' := fun W => (((P i) ∩ W).card : ℝ) < β * n * q ^ 1 / 2)
        (iE' := fun W => inferInstance) (fun W h => h)).trans ?_
      have := count_tail hq hq1 (P i) (fun a => ({a} : Finset V)) one_pos
        (fun _ _ => by simp) (Δ := 1) one_pos (fun z => by
          have : ((P i).filter fun a => z ∈ ({a} : Finset V)) ⊆ {z} := by
            intro w hw; simp only [mem_filter, mem_singleton] at hw; simp [hw.2]
          exact_mod_cast (card_le_card this).trans (by simp)) (hP i)
      simp only [ccount_singleton] at this
      refine this.trans (Real.exp_le_exp.2 ?_)
      have e : β * n * q ^ (2 * 1) / (16 * 1 * ((1 : ℕ) : ℝ)) = β * q ^ 2 / 16 * n := by
        push_cast; ring
      rw [e]; nlinarith
    · cases b
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr false)))
          (E' := fun W => q * n + q * n ≤ (W.card : ℝ))
          (iE' := fun W => inferInstance) (fun W h => h)).trans ?_
        have ht := tail_upper hq0 hq1 (fun _ : V => (1 : ℝ)) (l := q / 2) (by positivity)
          (univ : Finset V)
          (fun W : Finset V => (W.card : ℝ)) (fun W _ a _ haW => by
            simp only [Finset.card_insert_of_notMem haW]; push_cast; simp)
          (fun _ _ => by linarith) (q * n)
        rw [bexp_card, hV] at ht
        refine ht.trans (Real.exp_le_exp.2 ?_)
        simp only [sum_const, card_univ, hV, nsmul_eq_mul]
        nlinarith
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr true)))
          (E' := fun W => (W.card : ℝ) < n * q ^ 1 / 2)
          (iE' := fun W => inferInstance) (fun W h => h)).trans ?_
        have := count_tail hq hq1 (univ : Finset V) (fun a => ({a} : Finset V)) one_pos
          (fun _ _ => by simp) (Δ := 1) one_pos (fun z => by
            have : ((univ : Finset V).filter fun a => z ∈ ({a} : Finset V)) ⊆ {z} := by
              intro w hw; simp only [mem_filter, mem_singleton] at hw; simp [hw.2]
            exact_mod_cast (card_le_card this).trans (by simp))
          (L := n) (by rw [card_univ, hV])
        simp only [ccount_singleton, univ_inter] at this
        refine this.trans (Real.exp_le_exp.2 ?_)
        have e : (n : ℝ) * q ^ (2 * 1) / (16 * 1 * ((1 : ℕ) : ℝ)) = q ^ 2 / 16 * n := by
          push_cast; ring
        rw [e]; nlinarith
  have hsum : ∑ j : Idx, bprob q univ (bad j) < 1 := by
    calc ∑ j : Idx, bprob q univ (bad j) ≤ ∑ _j : Idx, Real.exp (-(θ * n)) :=
          Finset.sum_le_sum fun j _ => hE j
      _ = Fintype.card Idx * Real.exp (-(θ * n)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-(θ * n)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have hc : Fintype.card Idx = n ^ 3 + (Fintype.card ι + 2) := by
            simp only [Idx, Fintype.card_sum, Fintype.card_prod, hV, Fintype.card_bool]; ring
          rw [hc]
          have h1 : ((n ^ 3 + (Fintype.card ι + 2) : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 + n ^ 2 + 2 := by
            have : (Fintype.card ι : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hι
            push_cast; linarith
          have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
          have h3 : (2 : ℝ) ≤ 2 * (n : ℝ) ^ 3 := by nlinarith [pow_le_pow_left₀ zero_le_one hn1R 3]
          linarith
      _ < 1 := four_cube_exp_lt hθpos hnθ
  obtain ⟨W, -, hW⟩ := exists_good hq0 hq1 univ univ bad hsum
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · have := hW (Sum.inr (Sum.inr true)) (mem_univ _)
    simp only [bad, not_lt] at this; linarith
  · have := hW (Sum.inr (Sum.inr false)) (mem_univ _)
    simp only [bad, not_le] at this; linarith
  · intro i; have := hW (Sum.inr (Sum.inl i)) (mem_univ _)
    simp only [bad, not_lt] at this; linarith
  · intro v x y hadm; have := hW (Sum.inl (v, x, y)) (mem_univ _)
    simp only [bad, not_and, not_lt] at this; have := this hadm; linarith

/-- the deletion window (depends only on the constants) -/
noncomputable def epsOf (a q : ℝ) (m : ℕ) : ℝ := a * q ^ m / (4 * (2 * m + 1))

/-- **S07 §2 consolidated**: ONE `W`, then EVERY later small deletion is paid deterministically. -/
theorem random_core_robust (a β q : ℝ) (m : ℕ) (ha : 0 < a) (hβ : 0 < β) (hq : 0 < q)
    (hq1 : q ≤ 1) (hm : 0 < m) (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ)
    (hV : Fintype.card V = n) (hn : n0Core a β q m ≤ n)
    (L : V → SimpleGraph V) [∀ v, DecidableRel (L v).Adj]
    (adm : V → V → V → Prop) [∀ v x y, Decidable (adm v x y)]
    (hpaths : ∀ v x y, adm v x y → a * (n : ℝ) ^ m ≤ (pathsLen (L v) (m + 1) x y).card)
    (ι : Type*) [Fintype ι] (hι : Fintype.card ι ≤ n ^ 2) (P : ι → Finset V)
    (hP : ∀ i, β * n ≤ (P i).card) :
    ∃ W : Finset V, q * n / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * n ∧
      (∀ i, q * β * n / 2 ≤ (P i ∩ W).card) ∧
      ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
        (Z.card : ℝ) ≤ epsOf a q m * n → (∀ u, B.degree u ≤ d) → (d : ℝ) ≤ epsOf a q m * n →
        ∀ v x y, adm v x y →
          ∃ p ∈ pathsLen (L v) (m + 1) x y, intlSet m p ⊆ W ∧ (∀ i : Fin m, intl m p i ∉ Z) ∧
            ∀ k < m + 1, ¬ B.Adj (p.getVert k) (p.getVert (k + 1)) := by
  obtain ⟨W, h1, h2, h3, h4⟩ :=
    random_core a β q m ha hβ hq hq1 hm V n hV hn L adm hpaths ι hι P hP
  refine ⟨W, h1, h2, h3, ?_⟩
  intro Z B _ d hZ hB hd v x y hadm
  refine pay_deterministic (L v) m x y W (h4 v x y hadm) Z B d hB ?_
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le (Nat.succ_pos _) hn
    exact_mod_cast this
  set ε := epsOf a q m
  have hε : ε * (2 * m + 1) = a * q ^ m / 4 := by
    simp only [ε, epsOf]; field_simp
  rw [hV]
  have hpow : (n : ℝ) ^ m = (n : ℝ) ^ (m - 1) * n := by rw [← pow_succ, Nat.sub_add_cancel hm]
  have hnm : 0 < (n : ℝ) ^ (m - 1) := by positivity
  have key : ((Z.card * m + (m + 1) * d : ℕ) : ℝ) ≤ ε * (2 * m + 1) * n := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hZ hmR.le, mul_le_mul_of_nonneg_left hd
      (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  rw [hε] at key
  have hq' : 0 < a * q ^ m := by positivity
  calc ((Z.card * m + (m + 1) * d : ℕ) : ℝ) * (n : ℝ) ^ (m - 1)
      ≤ a * q ^ m / 4 * n * (n : ℝ) ^ (m - 1) := mul_le_mul_of_nonneg_right key hnm.le
    _ < a * q ^ m * (n : ℝ) ^ m / 2 := by rw [hpow]; nlinarith [mul_pos hq' (mul_pos hnm hnR)]

end S07V24
