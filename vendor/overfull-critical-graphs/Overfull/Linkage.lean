/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.VAL
public import Mathlib.Data.Finset.Sort

/-!
# Restricting multifans, Kempe swaps, linkage (CCJS Lemma 2.3), Parity Lemma

* `kempeSwap_col_of_ne`, `kempeSwap_isFree_of_ne`: an `(α, β)`-swap changes neither edges nor
  missing colours outside `{α, β}`.
* `IsMultifan.restrict`: the fan vertices indexed by a set `T ∋ 0` in which every index has an
  earlier "parent" form a multifan (possibly for another colouring).
* `multifan_linked_of_lt` (CCJS Lemma 2.3 (b), in the form used): for `i < j`, `δ` missing at
  `yᵢ`, `λ` missing at `yⱼ`, if `yᵢ, yⱼ` are `(δ, λ)`-unlinked then `x` lies on the
  `(δ, λ)`-chain of `yⱼ`.
* `multifan_linked_of_closed` (CCJS Lemma 2.3 (a)): if `i, j` lie in a parent-closed index set
  none of whose fan edges is coloured `δ` or `λ`, then `yᵢ, yⱼ` are `(δ, λ)`-linked.
* `parity` (CCJS Lemma 3.1): the number of vertices missing a colour has the parity of `n`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Kempe swaps outside the two colours -/

theorem kempeSwap_col_of_ne {k : ℕ} (c : PEC G (Fin k)) (α β : Fin k) (w u v : V)
    {γ : Fin k} (hγ : c.col u v = some γ) (hα : γ ≠ α) (hβ : γ ≠ β) :
    (c.kempeSwap α β w).col u v = some γ := by
  rw [kempeSwap_col]
  by_cases hu : (c.kempeGraph α β).Reachable w u
  · rw [kempeSwapFun_of_reachable c α β hu v, hγ]
    simp [Equiv.swap_apply_of_ne_of_ne hα hβ]
  · rw [kempeSwapFun_of_not_reachable c α β hu v, hγ]

theorem kempeSwap_isFree_of_ne {k : ℕ} (c : PEC G (Fin k)) (α β : Fin k) (w v : V)
    {γ : Fin k} (hα : γ ≠ α) (hβ : γ ≠ β) :
    (c.kempeSwap α β w).IsFree v γ ↔ c.IsFree v γ := by
  by_cases hv : (c.kempeGraph α β).Reachable w v
  · rw [isFree_kempeSwap_of_reachable c α β hv, Equiv.swap_apply_of_ne_of_ne hα hβ]
  · exact isFree_kempeSwap_of_not_reachable c α β hv γ

/-! ### Restriction -/

/-- The fan vertices indexed by `T` (in increasing order). -/
noncomputable def restrictFan (y : ℕ → V) (T : Finset ℕ) (k : ℕ) : V :=
  if h : k < #T then y (T.orderEmbOfFin rfl ⟨k, h⟩) else y 0

theorem IsMultifan.restrict {k : ℕ} {c c' : PEC G (Fin k)} {x : V} {L : ℕ} {y : ℕ → V}
    (hF : IsMultifan c x L y) {T : Finset ℕ} (hT : T ⊆ range L) (h0 : 0 ∈ T)
    (huncol : c'.col x (y 0) = none)
    (hpar : ∀ m ∈ T, 0 < m → ∃ p ∈ T, p < m ∧ ∃ γ, c'.col x (y m) = some γ ∧ c'.IsFree (y p) γ) :
    IsMultifan c' x #T (restrictFan y T) := by
  have hTne : T.Nonempty := ⟨0, h0⟩
  have hcard : 0 < #T := card_pos.2 hTne
  set e := T.orderEmbOfFin rfl
  have he0 : e ⟨0, hcard⟩ = 0 := by
    rw [orderEmbOfFin_zero rfl hcard]
    exact le_antisymm (min'_le _ _ h0) (Nat.zero_le _)
  have hemem : ∀ i : Fin #T, e i ∈ T := fun i => orderEmbOfFin_mem T rfl i
  have hval : ∀ i (hi : i < #T), restrictFan y T i = y (e ⟨i, hi⟩) := fun i hi => by
    simp [restrictFan, hi, e]
  refine ⟨hcard, ?_, fun i hi => ?_, fun i hi j hj h => ?_, fun i hi0 hi => ?_⟩
  · rw [hval 0 hcard, he0]
    exact huncol
  · rw [hval i hi]
    exact hF.adj _ (mem_range.1 (hT (hemem _)))
  · rw [hval i hi, hval j hj] at h
    have := hF.inj _ (mem_range.1 (hT (hemem _))) _ (mem_range.1 (hT (hemem _))) h
    have := e.injective this
    simpa using this
  · have hm0 : 0 < e ⟨i, hi⟩ := by
      rw [← he0]
      exact e.strictMono (show (⟨0, hcard⟩ : Fin #T) < ⟨i, hi⟩ from hi0)
    obtain ⟨p, hpT, hpm, γ, hγ, hfree⟩ := hpar _ (hemem _) hm0
    have hprange : p ∈ Set.range e := by
      rw [range_orderEmbOfFin]
      exact hpT
    obtain ⟨⟨j, hj⟩, hje⟩ := hprange
    refine ⟨j, ?_, γ, by rw [hval i hi]; exact hγ, by rw [hval j hj, hje]; exact hfree⟩
    have : (⟨j, hj⟩ : Fin #T) < ⟨i, hi⟩ := by
      rw [← e.lt_iff_lt, hje]
      exact hpm
    exact this

/-! ### Linkage -/

/-- **CCJS Lemma 2.3 (b)** (in the form used). For `i < j`, `δ` missing at `yᵢ` and `λ` missing
at `yⱼ`: if `yᵢ` and `yⱼ` are `(δ, λ)`-unlinked, then `x` is on the `(δ, λ)`-chain of `yⱼ`. -/
theorem multifan_linked_of_lt (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {x : V}
    {L : ℕ} {y : ℕ → V} (hcm : IsColMinus c x (y 0)) (hF : IsMultifan c x L y) {i j : ℕ}
    (hij : i < j) (hj : j < L) {δ μ : Fin G.maxDegree} (hδ : c.IsFree (y i) δ)
    (hμ : c.IsFree (y j) μ) (hun : ¬ (c.kempeGraph δ μ).Reachable (y j) (y i)) :
    (c.kempeGraph δ μ).Reachable (y j) x := by
  obtain ⟨hA, hA', -⟩ := multifan_elementary hG L c x y hcm hF
  by_contra hx
  have hFj := hF.prefix (m := j + 1) (by omega) (by omega)
  have hsw := hFj.kempeSwap (α := δ) (β := μ) (by simpa using hx) (by
    intro q hq hr
    simp only [Nat.add_sub_cancel] at hr hq
    refine ⟨fun hqδ => ?_, fun hqm => hA' q (by omega) j hj (by omega) μ hqm hμ⟩
    by_cases hqi : q = i
    · subst hqi
      exact hun hr
    · exact hA' q (by omega) i (by omega) hqi δ hqδ hδ)
  simp only [Nat.add_sub_cancel] at hsw
  have hcm' := kempeSwap_isColMinus (α := δ) (β := μ) hcm (w := y j) hx
  obtain ⟨-, hA'', -⟩ := multifan_elementary hG (j + 1) _ x y hcm' hsw
  refine hA'' i (by omega) j (Nat.lt_succ_self j) (by omega) δ ?_ ?_
  · rw [isFree_kempeSwap_of_not_reachable c δ μ hun]
    exact hδ
  · rw [isFree_kempeSwap_of_reachable c δ μ (Reachable.refl _), Equiv.swap_apply_left]
    exact hμ

/-- **CCJS Lemma 2.3 (a)** (in the form used). Let `i ≠ j` lie in a set `T ∋ 0` of indices in
which every positive index has an earlier parent in `T` (for `c`), no fan edge `x yₘ`, `m ∈ T`,
being coloured `δ` or `λ`. If `δ` is missing at `yᵢ` and `λ` at `yⱼ`, then `yᵢ` and `yⱼ` are
`(δ, λ)`-linked. -/
theorem multifan_linked_of_closed (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {x : V}
    {L : ℕ} {y : ℕ → V} (hcm : IsColMinus c x (y 0)) (hF : IsMultifan c x L y)
    {T : Finset ℕ} (hT : T ⊆ range L) (h0 : 0 ∈ T)
    (hpar : ∀ m ∈ T, 0 < m → ∃ p ∈ T, p < m ∧ ∃ γ, c.col x (y m) = some γ ∧ c.IsFree (y p) γ)
    {δ μ : Fin G.maxDegree}
    (hcolT : ∀ m ∈ T, ∀ γ, c.col x (y m) = some γ → γ ≠ δ ∧ γ ≠ μ)
    {i j : ℕ} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j)
    (hδ : c.IsFree (y i) δ) (hμ : c.IsFree (y j) μ) :
    (c.kempeGraph δ μ).Reachable (y j) (y i) := by
  obtain ⟨hA, hA', -⟩ := multifan_elementary hG L c x y hcm hF
  have hiL := mem_range.1 (hT hi)
  have hjL := mem_range.1 (hT hj)
  have hdm : δ ≠ μ := fun h => hA' i hiL j hjL hij δ hδ (h ▸ hμ)
  by_contra hun
  set c' := c.kempeSwap δ μ (y j)
  -- the colouring of `G − x y₀` is preserved
  have hcm' : IsColMinus c' x (y 0) := by
    refine ⟨hcm.adj, ?_, fun u v huv hne => extends_kempeSwap c δ μ (y j) u v
      (hcm.total u v huv hne)⟩
    simp only [c', kempeSwap_col, kempeSwapFun]
    split_ifs <;> simp [hcm.uncol]
  -- the restricted fan is a multifan for `c'`
  have hres := hF.restrict (c' := c') hT h0 hcm'.uncol (by
    intro m hm hm0
    obtain ⟨p, hp, hpm, γ, hγ, hfree⟩ := hpar m hm hm0
    obtain ⟨h1, h2⟩ := hcolT m hm γ hγ
    exact ⟨p, hp, hpm, γ, kempeSwap_col_of_ne c δ μ (y j) x (y m) hγ h1 h2,
      (kempeSwap_isFree_of_ne c δ μ (y j) (y p) h1 h2).2 hfree⟩)
  obtain ⟨-, hA'', -⟩ := multifan_elementary hG #T c' x (restrictFan y T) (by
    have : restrictFan y T 0 = y 0 := by
      have hcard : 0 < #T := card_pos.2 ⟨0, h0⟩
      simp only [restrictFan, hcard, dite_true]
      congr 1
      rw [orderEmbOfFin_zero rfl hcard]
      exact le_antisymm (min'_le _ _ h0) (Nat.zero_le _)
    rw [this]
    exact hcm') hres
  -- positions of `i` and `j` in `T`
  have hpos : ∀ m ∈ T, ∃ a < #T, restrictFan y T a = y m := by
    intro m hm
    have : m ∈ Set.range (T.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hm
    obtain ⟨⟨a, ha⟩, hae⟩ := this
    exact ⟨a, ha, by simp [restrictFan, ha, hae]⟩
  obtain ⟨a, ha, hya⟩ := hpos i hi
  obtain ⟨b, hb, hyb⟩ := hpos j hj
  have hab : a ≠ b := fun h => hij (hF.inj i hiL j hjL (by rw [← hya, ← hyb, h]))
  refine hA'' a ha b hb hab δ ?_ ?_
  · rw [hya, isFree_kempeSwap_of_not_reachable c δ μ hun]
    exact hδ
  · rw [hyb, isFree_kempeSwap_of_reachable c δ μ (Reachable.refl _), Equiv.swap_apply_left]
    exact hμ

/-! ### Parity Lemma -/

open Classical in
/-- **Parity Lemma** (CCJS Lemma 3.1). For any partial edge colouring, the number of vertices
missing a given colour has the parity of the number of vertices. -/
theorem parity {k : ℕ} (c : PEC G (Fin k)) (α : Fin k) :
    #(univ.filter fun v => c.IsFree v α) % 2 = Fintype.card V % 2 := by
  -- the vertices where `α` is present are matched in pairs
  let S := univ.filter fun v => ¬ c.IsFree v α
  have hpart : ∀ v ∈ S, ∃! u, c.col v u = some α := by
    intro v hv
    simp only [S, mem_filter, mem_univ, true_and, IsFree, not_forall, not_not] at hv
    obtain ⟨u, hu⟩ := hv
    exact ⟨u, hu, fun u' hu' => c.col_proper hu' hu⟩
  choose! mate hmate hmateu using hpart
  have hmateS : ∀ v ∈ S, mate v ∈ S := by
    intro v hv
    simp only [S, mem_filter, mem_univ, true_and, IsFree, not_forall, not_not]
    exact ⟨v, show c.col (mate v) v = some α by rw [c.col_symm]; exact hmate v hv⟩
  have hinv : ∀ v ∈ S, mate (mate v) = v := by
    intro v hv
    exact (hmateu (mate v) (hmateS v hv) v
      (show c.col (mate v) v = some α by rw [c.col_symm]; exact hmate v hv)).symm
  have hne : ∀ v ∈ S, mate v ≠ v := by
    intro v hv h
    have := hmate v hv
    rw [h, c.col_self] at this
    simp at this
  have heven : Even #S := by
    rw [card_eq_sum_card_image (fun v => s(v, mate v)) S]
    have hfib : ∀ e ∈ S.image (fun v => s(v, mate v)),
        #(S.filter fun w => s(w, mate w) = e) = 2 := by
      intro e he
      obtain ⟨v, hv, rfl⟩ := mem_image.1 he
      have hfeq : S.filter (fun w => s(w, mate w) = s(v, mate v)) = {v, mate v} := by
        ext w
        simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨-, h⟩
          rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact Or.inl h1
          · exact Or.inr h1
        · rintro (rfl | rfl)
          · exact ⟨hv, rfl⟩
          · refine ⟨hmateS v hv, ?_⟩
            rw [hinv v hv, Sym2.eq_swap]
      rw [hfeq, card_pair (hne v hv).symm]
    rw [sum_congr rfl hfib, sum_const, smul_eq_mul]
    exact even_iff_two_dvd.2 (dvd_mul_left 2 _)
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset V)) fun v => c.IsFree v α
  rw [card_univ] at hsplit
  obtain ⟨r, hr⟩ := heven
  have hr' : #(univ.filter fun v => ¬ c.IsFree v α) = r + r := hr
  omega

end Overfull
