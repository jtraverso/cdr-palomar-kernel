/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Extend
public import Plantholt.Core

/-!
# Edge-disjoint near 1-factors through prescribed matchings

Let `G'` be a graph on `V` (`|V| = 2n`) in which a vertex `w` is isolated and every other vertex has
degree at least `D₀`. Given matchings `C k ≤ G'` (`k < N`) covering at most `2b` vertices and
vertices `m k ≠ w` not covered by `C k`, if `n + b + N ≤ D₀` there are edge-disjoint matchings
`F k ≤ G'` (`k < N`) covering exactly `V − {w, m k}`, with every edge of `C k` in some `F j`,
`j ≤ k` (`exists_factors`). Each `F k` is the unused part of `C k` plus a perfect matching of the
rest (Dirac/Tutte, `Plantholt.exists_matchingOn`), as in Chetwynd–Hilton 1989, §4.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices covered by `M`. -/
noncomputable def cover (M : SimpleGraph V) : Finset V := univ.filter fun v => ∃ u, M.Adj v u

theorem mem_cover {M : SimpleGraph V} {v : V} : v ∈ cover M ↔ ∃ u, M.Adj v u := by
  simp [cover]

theorem degree_eq_one_of_matching {M : SimpleGraph V} (hM : IsMatchingGraph M) {v : V}
    (hv : v ∈ cover M) : M.degree v = 1 := by
  obtain ⟨u, hu⟩ := mem_cover.1 hv
  rw [← card_neighborFinset_eq_degree, card_eq_one]
  refine ⟨u, ?_⟩
  ext z
  rw [mem_neighborFinset, mem_singleton]
  exact ⟨fun h => hM v z u h hu, fun h => h ▸ hu⟩

theorem degree_eq_zero_of_not_cover {M : SimpleGraph V} {v : V} (hv : v ∉ cover M) :
    M.degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, card_eq_zero]
  ext z
  rw [mem_neighborFinset]
  simp only [notMem_empty, iff_false]
  exact fun h => hv (mem_cover.2 ⟨z, h⟩)

theorem even_card_cover {M : SimpleGraph V} (hM : IsMatchingGraph M) : Even #(cover M) := by
  have h := sum_degrees_eq_twice_card_edges M
  rw [← sum_filter_add_sum_filter_not univ (· ∈ cover M)] at h
  rw [sum_congr rfl (g := fun _ => 1) fun v hv =>
      degree_eq_one_of_matching hM (mem_filter.1 hv).2,
    sum_congr rfl (g := fun _ => 0) fun v hv =>
      degree_eq_zero_of_not_cover (mem_filter.1 hv).2] at h
  simp only [sum_const, smul_eq_mul, mul_one, mul_zero, add_zero] at h
  have : (univ.filter (· ∈ cover M)) = cover M := by ext; simp
  rw [this] at h
  exact ⟨#M.edgeFinset, by omega⟩

theorem degree_sup_le (A B : SimpleGraph V) (v : V) :
    (A ⊔ B).degree v ≤ A.degree v + B.degree v := by
  simp only [← card_neighborFinset_eq_degree]
  calc _ ≤ #(A.neighborFinset v ∪ B.neighborFinset v) := card_le_card fun u hu => by
        rw [mem_neighborFinset, sup_adj] at hu
        rw [mem_union, mem_neighborFinset, mem_neighborFinset]
        exact hu
    _ ≤ _ := card_union_le _ _

theorem degree_sup_range_le {F : ℕ → SimpleGraph V} (hF : ∀ j, IsMatchingGraph (F j))
    (t : ℕ) (v : V) : ((range t).sup F).degree v ≤ t := by
  induction t with
  | zero =>
    have h : (range 0).sup F ≤ ⊥ := by simp
    exact (degree_le_of_le (H := ⊥) h).trans (by simp)
  | succ t ih =>
    rw [range_add_one, sup_insert]
    refine (degree_sup_le _ _ v).trans ?_
    have h1 : (F t).degree v ≤ 1 := by
      by_cases hv : v ∈ cover (F t)
      · rw [degree_eq_one_of_matching (hF t) hv]
      · rw [degree_eq_zero_of_not_cover hv]; exact zero_le_one
    omega

theorem isMatchingGraph_of_degree {M : SimpleGraph V} (h : ∀ v, M.degree v ≤ 1) :
    IsMatchingGraph M := by
  intro v a b ha hb
  by_contra hab
  have : #({a, b} : Finset V) ≤ #(M.neighborFinset v) := card_le_card fun x hx => by
    rcases mem_insert.1 hx with rfl | hx
    · exact (mem_neighborFinset _ _ _).2 ha
    · rw [mem_singleton.1 hx]; exact (mem_neighborFinset _ _ _).2 hb
  rw [card_pair hab, card_neighborFinset_eq_degree] at this
  have := h v
  omega

theorem not_adj_of_degree_zero {M : SimpleGraph V} {v : V} (h : M.degree v = 0) (u : V) :
    ¬ M.Adj v u := fun hu => by
  have := card_pos.2 ⟨u, (mem_neighborFinset _ _ _).2 hu⟩
  rw [card_neighborFinset_eq_degree] at this
  omega

theorem exists_adj_of_degree_one {M : SimpleGraph V} {v : V} (h : M.degree v = 1) :
    ∃ u, M.Adj v u := by
  obtain ⟨u, hu⟩ := card_pos.1 (show 0 < #(M.neighborFinset v) by
    rw [card_neighborFinset_eq_degree, h]; exact one_pos)
  exact ⟨u, (mem_neighborFinset _ _ _).1 hu⟩

/-- One near 1-factor. -/
structure IsFactor (G' : SimpleGraph V) (w m : V) (F : SimpleGraph V) : Prop where
  le : F ≤ G'
  matching : IsMatchingGraph F
  covers : ∀ v, v ≠ w → v ≠ m → ∃ u, F.Adj v u
  miss_w : ∀ u, ¬ F.Adj w u
  miss_m : ∀ u, ¬ F.Adj m u

/-- **Edge-disjoint near 1-factors through prescribed matchings.** -/
theorem exists_factors (G' : SimpleGraph V) {n N b D₀ : ℕ} (hcard : Fintype.card V = 2 * n)
    (w : V) (hw : ∀ u, ¬ G'.Adj w u) (hdeg : ∀ v, v ≠ w → D₀ ≤ G'.degree v)
    (C : ℕ → SimpleGraph V) (m : ℕ → V) (hC : ∀ k, C k ≤ G') (hCm : ∀ k, IsMatchingGraph (C k))
    (hCb : ∀ k, #(cover (C k)) ≤ 2 * b) (hmw : ∀ k, m k ≠ w) (hmC : ∀ k u, ¬ (C k).Adj (m k) u)
    (hbound : n + b + N ≤ D₀) :
    ∃ F : ℕ → SimpleGraph V, (∀ k < N, IsFactor G' w (m k) (F k)) ∧
      (∀ j k, j < k → k < N → Disjoint (F j) (F k)) ∧
      (∀ k < N, C k ≤ (range (k + 1)).sup F) := by
  -- induction on the number of factors already built
  suffices key : ∀ t ≤ N, ∃ F : ℕ → SimpleGraph V, (∀ k < t, IsFactor G' w (m k) (F k)) ∧
      (∀ j k, j < k → k < t → Disjoint (F j) (F k)) ∧
      (∀ k < t, C k ≤ (range (k + 1)).sup F) ∧ (∀ k, t ≤ k → F k = ⊥) by
    obtain ⟨F, h1, h2, h3, -⟩ := key N le_rfl
    exact ⟨F, h1, fun j k hjk hk => h2 j k hjk hk, h3⟩
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun _ => ⊥, fun k hk => absurd hk (Nat.not_lt_zero _),
      fun j k _ hk => absurd hk (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _),
      fun _ _ => rfl⟩
  | succ t ih =>
    intro ht
    obtain ⟨F, hF, hdisj, hCF, hbot⟩ := ih (by omega)
    have hFm : ∀ j, IsMatchingGraph (F j) := fun j => by
      by_cases hj : j < t
      · exact (hF j hj).matching
      · rw [hbot j (by omega)]; intro v a b h; exact absurd h (by simp)
    set U := (range t).sup F
    set R := G' \ U
    set M := C t ⊓ R
    have hMm : IsMatchingGraph M := fun v a b ha hb => hCm t v a b ha.1 hb.1
    have hMR : M ≤ R := inf_le_right
    set W' := univ.filter fun v => v ≠ w ∧ v ≠ m t ∧ v ∉ cover M
    -- the complement of `W'`
    have hwS : w ∉ cover M := fun h => by
      obtain ⟨u, hu⟩ := mem_cover.1 h; exact hw u (hC t hu.1)
    have hmS : m t ∉ cover M := fun h => by
      obtain ⟨u, hu⟩ := mem_cover.1 h; exact hmC t u hu.1
    have hW'c : W'ᶜ = insert w (insert (m t) (cover M)) := by
      ext v; simp only [W', mem_compl, mem_filter, mem_univ, true_and, mem_insert, not_and_or,
        not_not, ne_eq]
    have hcW'c : #W'ᶜ = 2 + #(cover M) := by
      rw [hW'c, card_insert_of_notMem (by
        simp only [mem_insert, not_or]; exact ⟨fun h => hmw t h.symm, hwS⟩),
        card_insert_of_notMem hmS]
      omega
    have hSb : #(cover M) ≤ 2 * b := (card_le_card fun v hv => by
      obtain ⟨u, hu⟩ := mem_cover.1 hv; exact mem_cover.2 ⟨u, hu.1⟩).trans (hCb t)
    have hcW' : #W' + #W'ᶜ = 2 * n := by rw [card_add_card_compl, hcard]
    have hevW' : Even #W' := by
      obtain ⟨r, hr⟩ := even_card_cover hMm
      exact ⟨n - 1 - r, by omega⟩
    -- degrees in `R`
    have hdegR : ∀ v, v ≠ w → D₀ ≤ R.degree v + t := fun v hv => by
      have h1 : R.degree v + U.degree v = G'.degree v := Plantholt.degree_sdiff_add G' (M := U)
        (Finset.sup_le fun j hj => ?_) v
      · have h2 : U.degree v ≤ t := degree_sup_range_le hFm t v
        have := hdeg v hv
        omega
      · exact (hF j (mem_range.1 hj)).le
    obtain ⟨P, hP⟩ := Plantholt.exists_matchingOn R (W := W') hevW' fun v hv => by
      have h1 := Plantholt.deg_le_nbIn_add R W' v
      have hv' := (mem_filter.1 hv).2
      have := hdegR v hv'.1
      omega
    -- the new factor
    refine ⟨Function.update F t (M ⊔ P), fun k hk => ?_, fun j k hjk hk => ?_, fun k hk => ?_,
      fun k hk => ?_⟩
    · have hPm : IsMatchingGraph P := isMatchingGraph_of_degree fun v => by
        by_cases hv : v ∈ W'
        · rw [hP.2.1 v hv]
        · rw [hP.2.2 v hv]; exact zero_le_one
      have hPW : ∀ v u, P.Adj v u → v ∈ W' := fun v u h => by
        by_contra hv; exact not_adj_of_degree_zero (hP.2.2 v hv) u h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hkt
      · rw [Function.update_of_ne (by omega)]; exact hF k hk
      rw [hkt, Function.update_self]
      refine ⟨sup_le (hMR.trans sdiff_le) (hP.1.trans sdiff_le), fun v a b ha hb => ?_,
        fun v hv hvm => ?_, fun u h => ?_, fun u h => ?_⟩
      · rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact hMm v a b ha hb
        · exact absurd (hPW v b hb) fun h => (mem_filter.1 h).2.2.2 (mem_cover.2 ⟨a, ha⟩)
        · exact absurd (hPW v a ha) fun h => (mem_filter.1 h).2.2.2 (mem_cover.2 ⟨b, hb⟩)
        · exact hPm v a b ha hb
      · by_cases hS : v ∈ cover M
        · obtain ⟨u, hu⟩ := mem_cover.1 hS; exact ⟨u, Or.inl hu⟩
        · obtain ⟨u, hu⟩ := exists_adj_of_degree_one
            (hP.2.1 v (mem_filter.2 ⟨mem_univ _, hv, hvm, hS⟩))
          exact ⟨u, Or.inr hu⟩
      · rcases h with h | h
        · exact hw u (hC t h.1)
        · exact (mem_filter.1 (hPW w u h)).2.1 rfl
      · rcases h with h | h
        · exact hmC t u h.1
        · exact (mem_filter.1 (hPW (m t) u h)).2.2.1 rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hkt
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hdisj j k hjk hk'
      · rw [hkt] at hjk ⊢
        rw [Function.update_of_ne (by omega), Function.update_self]
        have hFU : F j ≤ U := le_sup (f := F) (mem_range.2 hjk)
        exact (disjoint_sdiff_self_right.mono_left hFU).mono_right
          (sup_le hMR hP.1)
    · have hsame : ∀ k' ≤ t, (range k').sup (Function.update F t (M ⊔ P)) = (range k').sup F :=
        fun k' hk' => sup_congr rfl fun j hj => Function.update_of_ne (by
          have := mem_range.1 hj; omega) _ _
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hkt
      · rw [hsame (k + 1) (by omega)]; exact hCF k hk'
      · rw [hkt, range_add_one, sup_insert, Function.update_self, hsame t le_rfl]
        intro a b h
        by_cases hU : U.Adj a b
        · exact Or.inr hU
        · exact Or.inl (Or.inl ⟨h, hC t h, hU⟩)
    · rw [Function.update_of_ne (by omega)]; exact hbot k (by omega)

end OneFactor
