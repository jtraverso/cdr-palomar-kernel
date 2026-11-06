/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Pseudorandom.RandomMatching
public import RequestProject.Pseudorandom.EdgePartition
public import RequestProject.PaschEGJ13.TupleDefs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Step 3 of Theorem 1.3: random matchings and tuple weights

Vertex-disjoint parts `A i` (`i ∈ [p]`) are split into `q` classes `cls A fc i j` by an edge
colouring `fc`. For every class we have a random matching with exact marginals `x`. For each
part independently we pick a uniformly random class and a random matching of it; `M` is the
union. For an `ℓ`-tuple weight function `ω`:
* a set `S` of `ℓ` edges in pairwise distinct parts is contained in `M` with probability
  exactly `(x/q)^ℓ`;
* any other `S` is contained in `M` with probability at most `(x/q)^{k(S)}`, where `k(S)` is
  the number of parts met by `S`, and only if `S` lies in the parts and edges of `S` in the same
  part have the same colour;
* changing the choice in part `i` changes `ω(M)` by at most `c` if every `Γ_i(σ) ≤ c`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Setup

variable {p q : ℕ} (A : Fin p → Finset (Finset V)) (fc : Finset V → Fin q)

/-- The random matching for an outcome `z` (restricted to the chosen classes). -/
def tmM (z : Fin p → Fin q × Finset (Finset V)) : Finset (Finset V) :=
  univ.biUnion (fun i => (z i).2 ∩ cls A fc i (z i).1)

/-- `S` lies in the parts. -/
def InParts (S : Finset (Finset V)) : Prop := ∀ e ∈ S, ∃ i, e ∈ A i

/-- `S` lies in the parts, with all edges in pairwise distinct parts. -/
def DistinctParts (S : Finset (Finset V)) : Prop :=
  InParts A S ∧ ∀ e ∈ S, ∀ e' ∈ S, ∀ i, e ∈ A i → e' ∈ A i → e = e'

/-- Edges of `S` in the same part have the same colour. -/
def ConsCol (S : Finset (Finset V)) : Prop :=
  ∀ e ∈ S, ∀ e' ∈ S, ∀ i, e ∈ A i → e' ∈ A i → fc e = fc e'

/-- The parts met by `S`. -/
def partsMet (S : Finset (Finset V)) : Finset (Fin p) := univ.filter (fun i => ∃ e ∈ S, e ∈ A i)

/-- The product distribution. -/
noncomputable def tmP (ν : Fin p → Fin q → Finset (Finset V) → ℝ) :
    Fin p → Fin q × Finset (Finset V) → ℝ := fun i a => ν i a.1 a.2 / q

open Classical in
/-- Probability that a set `T ⊆ A i` is contained in the matching chosen in part `i`. -/
noncomputable def tmRho (ν : Fin p → Fin q → Finset (Finset V) → ℝ) (i : Fin p)
    (T : Finset (Finset V)) : ℝ :=
  ∑ a, tmP ν i a * if T ⊆ a.2 ∩ cls A fc i a.1 then 1 else 0

end Setup

section Main

variable {p q : ℕ} {A : Fin p → Finset (Finset V)} {fc : Finset V → Fin q}

theorem tmM_inParts (z : Fin p → Fin q × Finset (Finset V)) {e : Finset V} (he : e ∈ tmM A fc z) :
    ∃ i, e ∈ A i ∧ e ∈ (z i).2 ∧ fc e = (z i).1 := by
  simp only [tmM, mem_biUnion, mem_univ, true_and, mem_inter, cls, mem_filter] at he
  obtain ⟨i, h1, h2, h3⟩ := he
  exact ⟨i, h2, h1, h3⟩

/-- Disjointness of parts as edge sets. -/
theorem part_unique (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g) {e : Finset V} {i i' : Fin p}
    (h : e ∈ A i) (h' : e ∈ A i') : i = i' := by
  by_contra hii
  have := hdisj i i' hii e h e h'
  rw [disjoint_self_iff_empty] at this
  exact (hne i e h).ne_empty this

open Classical in
theorem subset_tmM_iff (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g) {S : Finset (Finset V)}
    (hS : InParts A S) (z : Fin p → Fin q × Finset (Finset V)) :
    S ⊆ tmM A fc z ↔ ∀ i, S.filter (· ∈ A i) ⊆ (z i).2 ∩ cls A fc i (z i).1 := by
  constructor
  · intro h i e he
    rw [mem_filter] at he
    obtain ⟨i', hi', hz, hc⟩ := tmM_inParts z (h he.1)
    have := part_unique hne hdisj he.2 hi'
    subst this
    exact mem_inter.mpr ⟨hz, mem_filter.mpr ⟨he.2, hc⟩⟩
  · intro h e he
    obtain ⟨i, hi⟩ := hS e he
    have := h i (mem_filter.mpr ⟨he, hi⟩)
    simp only [tmM, mem_biUnion, mem_univ, true_and]
    exact ⟨i, this⟩

variable {ν : Fin p → Fin q → Finset (Finset V) → ℝ}



theorem tmP_isPMF (hq : 0 < q) (hν0 : ∀ i j N, 0 ≤ ν i j N) (hν1 : ∀ i j, ∑ N, ν i j N = 1) :
    IsPMF (tmP ν) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨fun i a => div_nonneg (hν0 _ _ _) hqR.le, fun i => ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [tmP]
  simp_rw [← sum_div, hν1]
  simp [hqR.ne']

theorem tmRho_empty (hq : 0 < q) (hν1 : ∀ i j, ∑ N, ν i j N = 1) (i : Fin p) :
    tmRho A fc ν i ∅ = 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold tmRho
  simp only [empty_subset, if_true, mul_one, tmP]
  rw [Fintype.sum_prod_type]
  simp_rw [← sum_div, hν1]
  simp [hqR.ne']

theorem tmRho_single (hq : 0 < q) (hνsupp : ∀ i j N, ν i j N ≠ 0 → IsMatching N ∧ N ⊆ cls A fc i j)
    (x : ℝ) (hνmarg : ∀ i j, ∀ e ∈ cls A fc i j, marg (ν i j) e = x) {i : Fin p} {e : Finset V}
    (he : e ∈ A i) : tmRho A fc ν i {e} = x / q := by
  classical
  unfold tmRho tmP
  rw [Fintype.sum_prod_type]
  have hcls : ∀ j, e ∈ cls A fc i j ↔ fc e = j := fun j => by
    simp [cls, mem_filter, he]
  rw [Fintype.sum_eq_single (fc e)]
  · have h := hνmarg i (fc e) e ((hcls _).mpr rfl)
    unfold marg at h
    rw [← h, sum_div]
    refine sum_congr rfl fun N _ => ?_
    simp only [singleton_subset_iff, mem_inter, (hcls _).mpr rfl, and_true]
    split_ifs <;> ring
  · intro j hj
    refine sum_eq_zero fun N _ => ?_
    have : ¬ ({e} ⊆ N ∩ cls A fc i j) := by
      rw [singleton_subset_iff, mem_inter, hcls]; exact fun h => hj h.2.symm
    simp [this]

theorem tmRho_le (hq : 0 < q) (hν0 : ∀ i j N, 0 ≤ ν i j N)
    (hνsupp : ∀ i j N, ν i j N ≠ 0 → IsMatching N ∧ N ⊆ cls A fc i j)
    (x : ℝ) (hνmarg : ∀ i j, ∀ e ∈ cls A fc i j, marg (ν i j) e = x) {i : Fin p}
    {T : Finset (Finset V)} (hT : T ⊆ A i) (hTne : T.Nonempty) :
    tmRho A fc ν i T ≤ x / q * if ∀ e ∈ T, ∀ e' ∈ T, fc e = fc e' then 1 else 0 := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨e₀, he₀⟩ := hTne
  unfold tmRho tmP
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single (fc e₀)]
  · have h := hνmarg i (fc e₀) e₀ (by simp [cls, mem_filter, hT he₀])
    unfold marg at h
    split_ifs with hmono
    · rw [mul_one, ← h, sum_div]
      refine sum_le_sum fun N _ => ?_
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hqR]
      apply mul_le_mul_of_nonneg_left _ (hν0 _ _ _)
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (mem_inter.mp (h1 he₀)).1 h2
      · exact zero_le_one
      · exact le_rfl
    · rw [mul_zero]
      push_neg at hmono
      obtain ⟨e, he, e', he', hne⟩ := hmono
      refine le_of_eq (sum_eq_zero fun N _ => ?_)
      have : ¬ (T ⊆ N ∩ cls A fc i (fc e₀)) := by
        intro hsub
        have h1 := (mem_filter.mp (mem_inter.mp (hsub he)).2).2
        have h2 := (mem_filter.mp (mem_inter.mp (hsub he')).2).2
        exact hne (h1.trans h2.symm)
      simp [this]
  · intro j hj
    refine sum_eq_zero fun N _ => ?_
    have : ¬ (T ⊆ N ∩ cls A fc i j) := by
      intro hsub
      exact hj (mem_filter.mp (mem_inter.mp (hsub he₀)).2).2.symm
    simp [this]

open Classical in
/-- The probability that `S ⊆ M` factorises over the parts. -/
theorem prob_subset_tmM (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g)
    {S : Finset (Finset V)} (hS : InParts A S) :
    pE (tmP ν) (fun z => if S ⊆ tmM A fc z then 1 else 0) =
      ∏ i, tmRho A fc ν i (S.filter (· ∈ A i)) := by
  have : (fun z => if S ⊆ tmM A fc z then (1 : ℝ) else 0) =
      fun z => ∏ i, (fun i a => if S.filter (· ∈ A i) ⊆ a.2 ∩ cls A fc i a.1 then (1 : ℝ)
        else 0) i (z i) := by
    funext z
    by_cases h : S ⊆ tmM A fc z
    · rw [if_pos h]
      have h' := (subset_tmM_iff (fc := fc) hne hdisj hS z).mp h
      exact (prod_eq_one fun i _ => by simp [h' i]).symm
    · rw [if_neg h]
      have : ¬ ∀ i, S.filter (· ∈ A i) ⊆ (z i).2 ∩ cls A fc i (z i).1 :=
        fun h' => h ((subset_tmM_iff hne hdisj hS z).mpr h')
      push_neg at this
      obtain ⟨i, hi⟩ := this
      exact (prod_eq_zero (mem_univ i) (by simp [hi])).symm
  rw [this]
  refine (pE_prod (P := tmP ν) (fun i (a : Fin q × Finset (Finset V)) =>
    if S.filter (· ∈ A i) ⊆ a.2 ∩ cls A fc i a.1 then (1 : ℝ) else 0)).trans ?_
  unfold tmRho
  refine prod_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
  congr 1

omit [Fintype V] in
theorem filter_eq_singleton_of_distinct
    {S : Finset (Finset V)} (hS : DistinctParts A S) {e : Finset V} (he : e ∈ S) {i : Fin p}
    (hi : e ∈ A i) : S.filter (· ∈ A i) = {e} := by
  ext e'
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨he', hi'⟩; exact (hS.2 e he e' he' i hi hi').symm
  · rintro rfl; exact ⟨he, hi⟩

theorem card_partsMet_of_distinct (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g)
    {S : Finset (Finset V)} (hS : DistinctParts A S) : (partsMet A S).card = S.card := by
  classical
  symm
  apply card_bij (fun e he => (Classical.choose (hS.1 e he)))
  · intro e he
    simp only [partsMet, mem_filter, mem_univ, true_and]
    exact ⟨e, he, Classical.choose_spec (hS.1 e he)⟩
  · intro e he e' he' h
    have h1 := Classical.choose_spec (hS.1 e he)
    have h2 := Classical.choose_spec (hS.1 e' he')
    rw [h] at h1
    exact hS.2 e he e' he' _ h1 h2
  · intro i hi
    simp only [partsMet, mem_filter, mem_univ, true_and] at hi
    obtain ⟨e, he, hei⟩ := hi
    exact ⟨e, he, part_unique hne hdisj (Classical.choose_spec (hS.1 e he)) hei⟩

theorem prob_distinct (hq : 0 < q) (hν1 : ∀ i j, ∑ N, ν i j N = 1)
    (hνsupp : ∀ i j N, ν i j N ≠ 0 → IsMatching N ∧ N ⊆ cls A fc i j)
    (x : ℝ) (hνmarg : ∀ i j, ∀ e ∈ cls A fc i j, marg (ν i j) e = x)
    (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g)
    {S : Finset (Finset V)} (hS : DistinctParts A S) :
    pE (tmP ν) (fun z => if S ⊆ tmM A fc z then 1 else 0) = (x / q) ^ S.card := by
  classical
  rw [prob_subset_tmM hne hdisj hS.1, ← card_partsMet_of_distinct hne hdisj hS]
  rw [← prod_filter_mul_prod_filter_not univ (fun i => ∃ e ∈ S, e ∈ A i)]
  have h1 : ∀ i ∈ univ.filter (fun i => ∃ e ∈ S, e ∈ A i),
      tmRho A fc ν i (S.filter (· ∈ A i)) = x / q := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    obtain ⟨e, he, hei⟩ := hi
    rw [filter_eq_singleton_of_distinct hS he hei]
    exact tmRho_single hq hνsupp x hνmarg hei
  have h2 : ∀ i ∈ univ.filter (fun i => ¬ ∃ e ∈ S, e ∈ A i),
      tmRho A fc ν i (S.filter (· ∈ A i)) = 1 := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and, not_exists, not_and] at hi
    have : S.filter (· ∈ A i) = ∅ := filter_eq_empty_iff.mpr fun e he => hi e he
    rw [this]; exact tmRho_empty hq hν1 i
  rw [prod_congr rfl h1, prod_congr rfl h2, prod_const_one, mul_one, prod_const]
  rfl

theorem prob_le (hq : 0 < q) (hν0 : ∀ i j N, 0 ≤ ν i j N) (hν1 : ∀ i j, ∑ N, ν i j N = 1)
    (hνsupp : ∀ i j N, ν i j N ≠ 0 → IsMatching N ∧ N ⊆ cls A fc i j)
    (x : ℝ) (hνmarg : ∀ i j, ∀ e ∈ cls A fc i j, marg (ν i j) e = x)
    (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g)
    (S : Finset (Finset V)) [Decidable (InParts A S ∧ ConsCol A fc S)] :
    pE (tmP ν) (fun z => if S ⊆ tmM A fc z then 1 else 0) ≤
      (x / q) ^ (partsMet A S).card * if InParts A S ∧ ConsCol A fc S then 1 else 0 := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP := tmP_isPMF hq hν0 hν1
  by_cases hin : InParts A S
  · rw [prob_subset_tmM hne hdisj hin]
    have hb : ∀ i, tmRho A fc ν i (S.filter (· ∈ A i)) ≤
        if ∃ e ∈ S, e ∈ A i then x / q * (if ∀ e ∈ S.filter (· ∈ A i),
          ∀ e' ∈ S.filter (· ∈ A i), fc e = fc e' then 1 else 0) else 1 := by
      intro i
      split_ifs with h
      · obtain ⟨e, he, hei⟩ := h
        have := tmRho_le hq hν0 hνsupp x hνmarg (T := S.filter (· ∈ A i)) (i := i)
          (fun e he => (mem_filter.mp he).2) ⟨e, mem_filter.mpr ⟨he, hei⟩⟩
        rw [if_pos (by assumption)] at this
        exact this
      · obtain ⟨e, he, hei⟩ := h
        have := tmRho_le hq hν0 hνsupp x hνmarg (T := S.filter (· ∈ A i)) (i := i)
          (fun e he => (mem_filter.mp he).2) ⟨e, mem_filter.mpr ⟨he, hei⟩⟩
        rw [if_neg (by assumption)] at this
        exact this
      · have : S.filter (· ∈ A i) = ∅ := filter_eq_empty_iff.mpr fun e he hei => h ⟨e, he, hei⟩
        rw [this, tmRho_empty hq hν1 i]
    have hnn : ∀ i, 0 ≤ tmRho A fc ν i (S.filter (· ∈ A i)) := fun i =>
      sum_nonneg fun a _ => mul_nonneg (hP.1 i a) (by split_ifs <;> norm_num)
    refine (prod_le_prod₀ (fun i _ => hnn i) (fun i _ => hb i)).trans (le_of_eq ?_)
    rw [← prod_filter_mul_prod_filter_not univ (fun i => ∃ e ∈ S, e ∈ A i)]
    rw [prod_congr rfl (fun i hi => if_pos (mem_filter.mp hi).2),
      prod_congr rfl (fun i hi => if_neg (mem_filter.mp hi).2), prod_const_one, mul_one,
      prod_mul_distrib, prod_const]
    congr 1
    by_cases hc : ConsCol A fc S
    · rw [if_pos ⟨hin, hc⟩]
      refine prod_eq_one fun i _ => ?_
      rw [if_pos]
      intro e he e' he'
      exact hc e (mem_filter.mp he).1 e' (mem_filter.mp he').1 i (mem_filter.mp he).2
        (mem_filter.mp he').2
    · rw [if_neg (fun h => hc h.2)]
      unfold ConsCol at hc
      push_neg at hc
      obtain ⟨e, he, e', he', i, hi, hi', hne'⟩ := hc
      refine prod_eq_zero (mem_filter.mpr ⟨mem_univ i, e, he, hi⟩) ?_
      rw [if_neg]
      push_neg
      exact ⟨e, mem_filter.mpr ⟨he, hi⟩, e', mem_filter.mpr ⟨he', hi'⟩, hne'⟩
  · have h0 : (fun z => if S ⊆ tmM A fc z then (1 : ℝ) else 0) = fun _ => 0 := by
      funext z
      rw [if_neg]
      intro hsub
      exact hin fun e he => by
        obtain ⟨i, hi, -⟩ := tmM_inParts z (hsub he)
        exact ⟨i, hi⟩
    rw [h0, pE_const hP, if_neg (fun h => hin h.1), mul_zero]

end Main

end Pseudorandom
