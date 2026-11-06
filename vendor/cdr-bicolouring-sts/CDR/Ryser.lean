/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.Matching

/-!
# Latin arrays and Ryser's theorem

A *latin array* on the cells `R × C` (`R C : Finset N`) is a filling `P : N → N → Y` in which no
symbol repeats in a row or a column. **Ryser's theorem** (H. J. Ryser, *A combinatorial theorem
with an application to latin rectangles*, Proc. AMS 2 (1951) 550–552): if `|Y| = |N| = n` and
every symbol occurs in at least `|R| + |C| − n` rows of the array, the array extends to a latin
square on `N × N` (`ryser`).

The proof adds one column at a time (`exists_add_column`): in the bipartite graph joining each
row to the symbols missing from it, rows have degree `n − |C|` and symbols degree at most
`n − |C|`, and a matching covering the vertices of degree `n − |C|`
(`exists_matching_cover_of_degree_le`, from Kőnig's theorem) fills the new column. Filling all
columns and then, by transposition, all rows gives the square.
-/

@[expose] public section

namespace CDR

open Finset

variable {N Y : Type*} [Fintype N] [DecidableEq N] [Fintype Y] [DecidableEq Y]

/-- `P` is a latin array on the cells `R × C`: no symbol repeats in a row or a column. -/
def IsLatinOn (R C : Finset N) (P : N → N → Y) : Prop :=
  (∀ i ∈ R, Set.InjOn (P i) C) ∧ ∀ j ∈ C, Set.InjOn (fun i => P i j) R

/-- A latin square: every row and every column is a bijection onto the symbols. -/
def IsLatinSquare (L : N → N → Y) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective (fun i => L i j)

/-- The number of rows of `R` in which `σ` occurs within the columns `C`. -/
def rowCount (R C : Finset N) (P : N → N → Y) (σ : Y) : ℕ :=
  #{i ∈ R | ∃ j ∈ C, P i j = σ}

/-- Ryser's condition: every symbol occurs in at least `|R| + |C| − n` rows. -/
def RyserCond (R C : Finset N) (P : N → N → Y) : Prop :=
  ∀ σ : Y, #R + #C ≤ Fintype.card N + rowCount R C P σ

theorem rowCount_le (R C : Finset N) (P : N → N → Y) (σ : Y) : rowCount R C P σ ≤ #R :=
  card_filter_le _ _

/-- The bipartite graph joining each row of `R` to the symbols missing from it in the columns
`C`. -/
def missingGraph (R C : Finset N) (P : N → N → Y) : SimpleGraph (N ⊕ Y) where
  Adj x y := (∃ i σ, x = .inl i ∧ y = .inr σ ∧ i ∈ R ∧ σ ∉ C.image (P i)) ∨
    (∃ i σ, y = .inl i ∧ x = .inr σ ∧ i ∈ R ∧ σ ∉ C.image (P i))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨i, σ, h1, h2, -⟩ | ⟨i, σ, h1, h2, -⟩ <;> exact Sum.inl_ne_inr (h1.symm.trans h2)⟩

noncomputable instance (R C : Finset N) (P : N → N → Y) :
    DecidableRel (missingGraph R C P).Adj :=
  Classical.decRel _

variable {R C : Finset N} {P : N → N → Y}

@[simp] theorem missingGraph_adj_inl_inr {i : N} {σ : Y} :
    (missingGraph R C P).Adj (.inl i) (.inr σ) ↔ i ∈ R ∧ σ ∉ C.image (P i) := by
  constructor
  · rintro (⟨i', σ', h1, h2, hi, hσ⟩ | ⟨i', σ', h1, h2, -⟩)
    · obtain rfl := Sum.inl_injective h1
      obtain rfl := Sum.inr_injective h2
      exact ⟨hi, hσ⟩
    · exact absurd h1 Sum.inr_ne_inl
  · exact fun h => Or.inl ⟨i, σ, rfl, rfl, h⟩

@[simp] theorem missingGraph_adj_inr_inl {i : N} {σ : Y} :
    (missingGraph R C P).Adj (.inr σ) (.inl i) ↔ i ∈ R ∧ σ ∉ C.image (P i) := by
  rw [(missingGraph R C P).adj_comm]
  exact missingGraph_adj_inl_inr

@[simp] theorem missingGraph_not_adj_inl_inl {i j : N} :
    ¬ (missingGraph R C P).Adj (.inl i) (.inl j) := by
  rintro (⟨i', σ', -, h2, -⟩ | ⟨i', σ', -, h2, -⟩)
  · exact Sum.inl_ne_inr h2
  · exact Sum.inl_ne_inr h2

@[simp] theorem missingGraph_not_adj_inr_inr {σ τ : Y} :
    ¬ (missingGraph R C P).Adj (.inr σ) (.inr τ) := by
  rintro (⟨i', σ', h1, -, -⟩ | ⟨i', σ', h1, -, -⟩)
  · exact Sum.inr_ne_inl h1
  · exact Sum.inr_ne_inl h1

variable (R C P) in
theorem missingGraph_colorable : (missingGraph R C P).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) fun {x y} h => by
    rcases x with i | σ <;> rcases y with j | τ <;> simp_all⟩

theorem missingGraph_degree_inl (hP : IsLatinOn R C P) {i : N} (hi : i ∈ R) :
    (missingGraph R C P).degree (.inl i) = Fintype.card Y - #C := by
  have hset : (missingGraph R C P).neighborFinset (.inl i) =
      (univ \ C.image (P i)).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext x
    rcases x with j | σ
    · simp
    · simp [hi]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, card_map, card_sdiff_of_subset
    (subset_univ _), card_univ, card_image_of_injOn (hP.1 i hi)]

theorem missingGraph_degree_inl_of_notMem {i : N} (hi : i ∉ R) :
    (missingGraph R C P).degree (.inl i) = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_zero]
  ext x
  rcases x with j | σ <;> simp [hi]

theorem missingGraph_degree_inr (σ : Y) :
    (missingGraph R C P).degree (.inr σ) = #R - rowCount R C P σ := by
  have hset : (missingGraph R C P).neighborFinset (.inr σ) =
      (R.filter fun i => ¬ ∃ j ∈ C, P i j = σ).map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    rcases x with i | τ
    · simp
    · simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, card_map, rowCount]
  have := card_filter_add_card_filter_not (s := R) (fun i => ∃ j ∈ C, P i j = σ)
  omega

/-- **One column.** A latin array on `R × C` satisfying Ryser's condition extends to a latin
array on `R × (C ∪ {j})` satisfying Ryser's condition. -/
theorem exists_add_column (hY : Fintype.card Y = Fintype.card N) {R C : Finset N}
    {P : N → N → Y} (hP : IsLatinOn R C P) (hcond : RyserCond R C P) {j : N} (hj : j ∉ C) :
    ∃ P' : N → N → Y, (∀ i, ∀ k ∈ C, P' i k = P i k) ∧ IsLatinOn R (insert j C) P' ∧
      RyserCond R (insert j C) P' := by
  set n := Fintype.card N
  have hCn : #C < n := by
    have := card_le_univ (insert j C)
    rw [card_insert_of_notMem hj] at this
    omega
  have hYne : Nonempty Y := by
    rw [← Fintype.card_pos_iff, hY]
    exact Fintype.card_pos_iff.2 ⟨j⟩
  set G := missingGraph R C P
  have hdeg : ∀ w, G.degree w ≤ n - #C := by
    intro w
    rcases w with i | σ
    · by_cases hi : i ∈ R
      · rw [missingGraph_degree_inl hP hi, hY]
      · rw [missingGraph_degree_inl_of_notMem hi]
        exact Nat.zero_le _
    · rw [missingGraph_degree_inr]
      have := hcond σ
      omega
  obtain ⟨M, hMG, hMuniq, hMcov⟩ :=
    exists_matching_cover_of_degree_le G (missingGraph_colorable R C P) (by omega) hdeg
  -- every row of `R` has a partner symbol
  have hrow : ∀ i, ∃ σ : Y, i ∈ R → M.Adj (.inl i) (.inr σ) := by
    intro i
    by_cases hi : i ∈ R
    · obtain ⟨u, hu⟩ := hMcov (.inl i) (by rw [missingGraph_degree_inl hP hi, hY])
      rcases u with i' | σ
      · exact absurd (hMG hu) (by simp [G, missingGraph])
      · exact ⟨σ, fun _ => hu⟩
    · exact ⟨Classical.arbitrary Y, fun h => absurd h hi⟩
  choose p hp using hrow
  have hpG : ∀ i ∈ R, p i ∉ C.image (P i) := fun i hi =>
    (missingGraph_adj_inl_inr.1 (hMG (hp i hi))).2
  refine ⟨fun i k => if k = j then p i else P i k, fun i k hk => ?_, ⟨?_, ?_⟩, ?_⟩
  · simp [show k ≠ j from fun h => hj (h ▸ hk)]
  · intro i hi k hk k' hk' h
    simp only at h
    have hk₁ := mem_insert.1 (mem_coe.1 hk)
    have hk₁' := mem_insert.1 (mem_coe.1 hk')
    by_cases hkj : k = j <;> by_cases hk'j : k' = j
    · rw [hkj, hk'j]
    · subst hkj
      have hk'C := hk₁'.resolve_left hk'j
      rw [if_pos rfl, if_neg hk'j] at h
      exact absurd (mem_image.2 ⟨k', hk'C, h.symm⟩) (hpG i hi)
    · subst hk'j
      have hkC := hk₁.resolve_left hkj
      rw [if_neg hkj, if_pos rfl] at h
      exact absurd (mem_image.2 ⟨k, hkC, h⟩) (hpG i hi)
    · rw [if_neg hkj, if_neg hk'j] at h
      exact hP.1 i hi (mem_coe.2 (hk₁.resolve_left hkj)) (mem_coe.2 (hk₁'.resolve_left hk'j)) h
  · intro k hk i hi i' hi' h
    simp only at h
    by_cases hkj : k = j
    · subst hkj
      have h' : p i = p i' := by simpa using h
      have h1 := (hp i hi).symm
      have h2 := (hp i' hi').symm
      rw [h'] at h1
      exact Sum.inl_injective (hMuniq _ _ _ h1 h2)
    · simp only [if_neg hkj] at h
      exact hP.2 k ((mem_insert.1 hk).resolve_left hkj) hi hi' h
  · intro σ
    rw [card_insert_of_notMem hj]
    have hmono : rowCount R C P σ ≤ rowCount R (insert j C) (fun i k => if k = j then p i else P i k) σ := by
      apply card_le_card
      intro i
      simp only [mem_filter]
      rintro ⟨hi, k, hk, hk'⟩
      exact ⟨hi, k, mem_insert_of_mem hk, by rw [if_neg (by rintro rfl; exact hj hk)]; exact hk'⟩
    have hle := rowCount_le R C P σ
    by_cases hcrit : G.degree (.inr σ) = n - #C
    · -- `σ` is matched to a row in which it does not occur yet
      obtain ⟨u, hu⟩ := hMcov (.inr σ) hcrit
      rcases u with i | τ
      · have hiG := missingGraph_adj_inl_inr.1 (hMG hu).symm
        have hpi : p i = σ := by
          have := hMuniq _ _ _ (hp i hiG.1) hu.symm
          exact Sum.inr_injective this
        have hnew : rowCount R C P σ + 1 ≤
            rowCount R (insert j C) (fun i k => if k = j then p i else P i k) σ := by
          rw [rowCount, rowCount, ← card_insert_of_notMem (a := i)]
          · apply card_le_card
            intro i'
            simp only [mem_insert, mem_filter]
            rintro (rfl | ⟨hi', k, hk, hk'⟩)
            · exact ⟨hiG.1, j, Or.inl rfl, by rw [if_pos rfl, hpi]⟩
            · exact ⟨hi', k, Or.inr hk, by rw [if_neg (by rintro rfl; exact hj hk)]; exact hk'⟩
          · simp only [mem_filter, not_and, not_exists]
            intro _ k hk hk'
            exact hiG.2 (mem_image.2 ⟨k, hk, hk'⟩)
        have := hcond σ
        omega
      · exact absurd (hMG hu) (by simp [G, missingGraph])
    · have hlt : G.degree (.inr σ) < n - #C := lt_of_le_of_ne (hdeg _) hcrit
      rw [missingGraph_degree_inr] at hlt
      omega

/-- Ryser's condition holds when the columns cover every column of `N` and the rows are
injective: each row then contains every symbol. -/
theorem ryserCond_transpose_of_full (hY : Fintype.card Y = Fintype.card N) {R : Finset N}
    {P : N → N → Y} (hP : IsLatinOn R univ P) :
    RyserCond univ R (fun j i => P i j) := by
  classical
  intro σ
  rw [card_univ]
  suffices h : #R ≤ rowCount univ R (fun j i => P i j) σ by omega
  have hsurj : ∀ i ∈ R, ∃ k, P i k = σ := by
    intro i hi
    have hinj : Function.Injective (P i) := fun a b h =>
      hP.1 i hi (mem_coe.2 (mem_univ a)) (mem_coe.2 (mem_univ b)) h
    exact ((Fintype.bijective_iff_injective_and_card (P i)).2 ⟨hinj, hY.symm⟩).2 σ
  choose! col hcol using hsurj
  have hinj : Set.InjOn col R := by
    intro i hi i' hi' h
    have h1 := hcol i hi
    have h2 := hcol i' hi'
    rw [h] at h1
    exact hP.2 (col i') (mem_univ _) hi hi' (h1.trans h2.symm)
  rw [rowCount, ← card_image_of_injOn hinj]
  apply card_le_card
  intro k hk
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hk
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨i, hi, hcol i hi⟩

/-- Fill all the columns. -/
theorem exists_fill_columns (hY : Fintype.card Y = Fintype.card N) :
    ∀ (m : ℕ) {R C : Finset N} {P : N → N → Y}, #(univ \ C) = m → IsLatinOn R C P →
      RyserCond R C P →
      ∃ P' : N → N → Y, (∀ i, ∀ k ∈ C, P' i k = P i k) ∧ IsLatinOn R univ P' := by
  classical
  intro m
  induction m with
  | zero =>
    intro R C P hm hP _
    have hC : C = univ := by
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hm
      exact eq_univ_of_forall fun x => hm (mem_univ x)
    subst hC
    exact ⟨P, fun _ _ _ => rfl, hP⟩
  | succ m ih =>
    intro R C P hm hP hcond
    obtain ⟨j, hj⟩ : (univ \ C).Nonempty := by
      rw [← card_pos, hm]
      exact Nat.succ_pos m
    have hjC : j ∉ C := (mem_sdiff.1 hj).2
    obtain ⟨P₁, hagree, hP₁, hcond₁⟩ := exists_add_column hY hP hcond hjC
    have hm₁ : #(univ \ insert j C) = m := by
      have : univ \ insert j C = (univ \ C).erase j := by
        ext x
        simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_erase, not_or]
      rw [this, card_erase_of_mem hj, hm, Nat.add_sub_cancel]
    obtain ⟨P₂, hagree₂, hP₂⟩ := ih hm₁ hP₁ hcond₁
    exact ⟨P₂, fun i k hk => (hagree₂ i k (mem_insert_of_mem hk)).trans (hagree i k hk), hP₂⟩

theorem isLatinOn_transpose {R C : Finset N} {P : N → N → Y} (hP : IsLatinOn R C P) :
    IsLatinOn C R (fun j i => P i j) :=
  ⟨fun j hj => hP.2 j hj, fun i hi => hP.1 i hi⟩

theorem isLatinSquare_of_isLatinOn (hY : Fintype.card Y = Fintype.card N) {L : N → N → Y}
    (hL : IsLatinOn univ univ L) : IsLatinSquare L := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun a b h => ?_, hY.symm⟩
    exact hL.1 i (mem_univ i) (mem_coe.2 (mem_univ a)) (mem_coe.2 (mem_univ b)) h
  · refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun a b h => ?_, hY.symm⟩
    exact hL.2 j (mem_univ j) (mem_coe.2 (mem_univ a)) (mem_coe.2 (mem_univ b)) h

/-- **Ryser's theorem (1951).** Let `|Y| = |N| = n`. A latin array on `R × C` in which every
symbol occurs in at least `|R| + |C| − n` rows extends to a latin square on `N × N`. -/
theorem ryser (hY : Fintype.card Y = Fintype.card N) {R C : Finset N} {P : N → N → Y}
    (hP : IsLatinOn R C P) (hcond : RyserCond R C P) :
    ∃ L : N → N → Y, IsLatinSquare L ∧ ∀ i ∈ R, ∀ j ∈ C, L i j = P i j := by
  classical
  obtain ⟨P₁, hagree₁, hP₁⟩ := exists_fill_columns hY _ rfl hP hcond
  obtain ⟨Q, hagreeQ, hQ⟩ := exists_fill_columns hY _ rfl (isLatinOn_transpose hP₁)
    (ryserCond_transpose_of_full hY hP₁)
  refine ⟨fun i j => Q j i, isLatinSquare_of_isLatinOn hY (isLatinOn_transpose hQ), ?_⟩
  intro i hi j hj
  exact (hagreeQ j i hi).trans (hagree₁ i j hj)

end CDR
