/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Factors

/-!
# Near 1-factors through prescribed matchings, with a bound for each step

`exists_factors_var`: as `exists_factors`, with the bound `2n + |V(C k)| + 2k ≤ 2 D₀` for each
step `k` instead of a uniform bound (Chetwynd–Hilton's staircase matchings shrink as `k` grows).
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deg_le_nbIn_add_erase (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (v w : V)
    (hw : ¬ G.Adj v w) : G.degree v ≤ #(Plantholt.nbIn G W v) + #(Wᶜ.erase w) := by
  rw [← card_neighborFinset_eq_degree, ← card_filter_add_card_filter_not (p := (· ∈ W))]
  have : #((G.neighborFinset v).filter (· ∉ W)) ≤ #(Wᶜ.erase w) :=
    card_le_card fun u hu => mem_erase.2 ⟨fun h => hw (h ▸ (mem_neighborFinset _ _ _).1
      (mem_filter.1 hu).1), mem_compl.2 (mem_filter.1 hu).2⟩
  have e : #((G.neighborFinset v).filter (· ∈ W)) = #(Plantholt.nbIn G W v) := by
    unfold Plantholt.nbIn; congr 1; ext u; simp
  omega

/-- **Edge-disjoint near 1-factors through prescribed matchings**, with a bound for each step. -/
theorem exists_factors_var (G' : SimpleGraph V) {n N D₀ : ℕ} (hcard : Fintype.card V = 2 * n)
    (w : V) (hw : ∀ u, ¬ G'.Adj w u) (hdeg : ∀ v, v ≠ w → D₀ ≤ G'.degree v)
    (C : ℕ → SimpleGraph V) (m : ℕ → V) (hC : ∀ k, C k ≤ G') (hCm : ∀ k, IsMatchingGraph (C k))
    (hCb : ∀ k < N, 2 * n + #(cover (C k)) + 2 * k ≤ 2 * D₀) (hmw : ∀ k, m k ≠ w)
    (hmC : ∀ k u, ¬ (C k).Adj (m k) u) :
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
    have hSb : #(cover M) ≤ #(cover (C t)) := card_le_card fun v hv => by
      obtain ⟨u, hu⟩ := mem_cover.1 hv; exact mem_cover.2 ⟨u, hu.1⟩
    have hbt := hCb t (by omega)
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
      have h1 := deg_le_nbIn_add_erase R W' v w (fun h => hw v h.1.symm)
      have hwc : w ∈ W'ᶜ := by rw [hW'c]; exact mem_insert_self _ _
      have h1' := card_erase_of_mem hwc
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
