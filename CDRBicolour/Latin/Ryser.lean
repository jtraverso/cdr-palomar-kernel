/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalGraphColouring.Konig.Basic

/-!
# Ryser's theorem on completing Latin rectangles

Rows and columns are indexed by a finite type `α` (`n = |α|`), symbols by a finite type `β`
with `|β| = n`.  A partial array
`L` on `R × K` is a *Latin rectangle* if it is injective along rows and columns.

`ryser`: if every symbol occurs at least `|R| + |K| - n` times in `R × K`, then `L` extends to a
Latin square of order `n` (Ryser, Proc. AMS 1951; the statement used by Colbourn–Dinitz–Rosa,
Lemma 2.3).

Proof: add one column at a time.  In the bipartite graph *rows of `R`* versus *symbols*, joining a
row to the symbols it misses, rows have degree `n - |K|` and symbols at most `n - |K|`; one colour
class of a Kőnig colouring with `n - |K|` colours is a matching covering every row and every tight
symbol.  When `K` is full, transpose and add rows in the same way.
-/

@[expose] public section

namespace CDRBicolour.Latin

open Finset SimpleGraph

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `L` is a Latin rectangle on `R × K`. -/
def IsLatinRect (R K : Finset α) (L : α → α → β) : Prop :=
  (∀ r ∈ R, Set.InjOn (L r) K) ∧ (∀ g ∈ K, Set.InjOn (fun r => L r g) R)

/-- `L` is a Latin square. -/
def IsLatin (L : α → α → β) : Prop := IsLatinRect univ univ L

/-- Number of rows of `R` containing `σ` within the columns `K`. -/
def cnt (R K : Finset α) (L : α → α → β) (σ : β) : ℕ :=
  (R.filter fun r => σ ∈ K.image (L r)).card

/-- Ryser's condition. -/
def RyserCond (R K : Finset α) (L : α → α → β) : Prop :=
  ∀ σ, R.card + K.card ≤ Fintype.card α + cnt R K L σ

/-! ### Line-graph colourings -/

section LineGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

theorem colour_inj (C : G.lineGraph.Coloring (Fin k)) {e f : G.edgeSet} {v : V}
    (hve : v ∈ (e : Sym2 V)) (hvf : v ∈ (f : Sym2 V)) (h : C e = C f) : e = f := by
  by_contra hne
  exact C.valid (lineGraph_adj_iff_exists.2 ⟨hne, v, hve, hvf⟩) h

/-- At a vertex of degree `k`, a `k`-colouring of the line graph uses every colour. -/
theorem exists_colour_at (C : G.lineGraph.Coloring (Fin k)) {v : V} (hv : G.degree v = k)
    (i : Fin k) : ∃ w, ∃ h : G.Adj v w, C ⟨s(v, w), h⟩ = i := by
  classical
  let f : {w // w ∈ G.neighborFinset v} → Fin k :=
    fun w => C ⟨s(v, w.1), (G.mem_neighborFinset v w.1).1 w.2⟩
  have hinj : Function.Injective f := by
    intro w w' h
    have := colour_inj C (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _) h
    exact Subtype.ext (Sym2.congr_right.1 (congrArg Subtype.val this))
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_coe, card_neighborFinset_eq_degree, hv, Fintype.card_fin]
  obtain ⟨w, hw⟩ := hbij.2 i
  exact ⟨w.1, (G.mem_neighborFinset v w.1).1 w.2, hw⟩

end LineGraph

/-! ### The missing-symbol graph -/

section Bip

variable (R K : Finset α) (L : α → α → β)

/-- Rows of `R` against symbols, joined when the row misses the symbol. -/
def bip : SimpleGraph (α ⊕ β) :=
  SimpleGraph.fromRel fun u v => ∃ r σ, u = .inl r ∧ v = .inr σ ∧ r ∈ R ∧ σ ∉ K.image (L r)

noncomputable instance : DecidableRel (bip R K L).Adj := Classical.decRel _

variable {R K L}

theorem bip_adj_lr {r : α} {σ : β} : (bip R K L).Adj (.inl r) (.inr σ) ↔ r ∈ R ∧ σ ∉ K.image (L r) := by
  simp only [bip, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  constructor
  · rintro (⟨r', σ', h1, h2, h3, h4⟩ | ⟨r', σ', h1, h2, h3, h4⟩)
    · cases h1; cases h2; exact ⟨h3, h4⟩
    · cases h1
  · rintro ⟨h3, h4⟩; exact Or.inl ⟨r, σ, rfl, rfl, h3, h4⟩

theorem bip_not_ll {r r' : α} : ¬ (bip R K L).Adj (.inl r) (.inl r') := by
  simp only [bip, fromRel_adj]
  rintro ⟨-, ⟨_, _, h1, h2, _⟩ | ⟨_, _, h1, h2, _⟩⟩ <;> simp_all

theorem bip_not_rr {σ σ' : β} : ¬ (bip R K L).Adj (.inr σ) (.inr σ') := by
  simp only [bip, fromRel_adj]
  rintro ⟨-, ⟨_, _, h1, h2, _⟩ | ⟨_, _, h1, h2, _⟩⟩ <;> simp_all

theorem bip_colorable : (bip R K L).Colorable 2 :=
  ⟨Coloring.mk (fun v => Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) v) (by
    intro u v h
    cases u <;> cases v
    · exact absurd h bip_not_ll
    · simp
    · simp
    · exact absurd h bip_not_rr)⟩

theorem bip_degree_row {r : α} (hr : r ∈ R) (hL : Set.InjOn (L r) K) :
    (bip R K L).degree (.inl r) = Fintype.card β - K.card := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have : (bip R K L).neighborFinset (.inl r) =
      (univ.filter fun σ => σ ∉ K.image (L r)).map Function.Embedding.inr := by
    ext v
    rw [mem_neighborFinset, mem_map]
    cases v with
    | inl r' => simp only [Function.Embedding.inr_apply, reduceCtorEq, and_false, exists_false,
        iff_false]; exact bip_not_ll
    | inr σ =>
      rw [bip_adj_lr]
      simp [hr]
  have h2 : (univ.filter fun σ => σ ∉ K.image (L r)) = univ \ K.image (L r) := by
    ext σ; simp
  rw [this, card_map, h2, card_sdiff_of_subset (subset_univ _), card_univ,
    card_image_of_injOn hL]

theorem bip_degree_row_out {r : α} (hr : r ∉ R) : (bip R K L).degree (.inl r) = 0 := by
  rw [← card_neighborFinset_eq_degree, card_eq_zero]
  ext v
  simp only [mem_neighborFinset, notMem_empty, iff_false]
  cases v with
  | inl r' => exact bip_not_ll
  | inr σ => rw [bip_adj_lr]; exact fun h => hr h.1

theorem bip_degree_sym (σ : β) :
    (bip R K L).degree (.inr σ) + cnt R K L σ = R.card := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have : (bip R K L).neighborFinset (.inr σ) =
      (R.filter fun r => σ ∉ K.image (L r)).map Function.Embedding.inl := by
    ext v
    rw [mem_neighborFinset, mem_map]
    cases v with
    | inl r =>
      rw [(bip R K L).adj_comm, bip_adj_lr]
      simp
    | inr σ' => simp only [Function.Embedding.inl_apply, reduceCtorEq, and_false, exists_false,
        iff_false]; exact bip_not_rr
  rw [this, card_map, cnt, add_comm]
  exact card_filter_add_card_filter_not _

end Bip

/-! ### Adding a column -/

theorem extend_col (hβ : Fintype.card β = Fintype.card α) {R K : Finset α} {L : α → α → β}
    (hL : IsLatinRect R K L)
    (hc : RyserCond R K L) {g₀ : α} (hg₀ : g₀ ∉ K) :
    ∃ L₁ : α → α → β, IsLatinRect R (insert g₀ K) L₁ ∧ (∀ r g, g ∈ K → L₁ r g = L r g) ∧
      RyserCond R (insert g₀ K) L₁ := by
  classical
  have hKlt : K.card < Fintype.card α := card_lt_univ_of_notMem hg₀
  by_cases hR : R = ∅
  · subst hR
    refine ⟨L, ⟨fun r hr => absurd hr (notMem_empty r), fun g _ => by simp⟩,
      fun _ _ _ => rfl, fun σ => ?_⟩
    rw [card_insert_of_notMem hg₀]; simp; omega
  obtain ⟨r₀, hr₀⟩ := nonempty_iff_ne_empty.2 hR
  have hmax : (bip R K L).maxDegree = Fintype.card α - K.card := by
    refine le_antisymm ((bip R K L).maxDegree_le_of_forall_degree_le _ fun v => ?_) ?_
    · cases v with
      | inl r =>
        by_cases hr : r ∈ R
        · rw [bip_degree_row hr (hL.1 r hr), hβ]
        · rw [bip_degree_row_out hr]; omega
      | inr σ =>
        have h1 := bip_degree_sym (R := R) (K := K) (L := L) σ
        have h2 := hc σ
        omega
    · rw [← hβ, ← bip_degree_row hr₀ (hL.1 r₀ hr₀)]; exact (bip R K L).degree_le_maxDegree _
  have hΔpos : 0 < Fintype.card α - K.card := by omega
  have hcol := Konig.lineGraph_colorable_of_colorable_two (bip R K L) bip_colorable
  rw [hmax] at hcol
  have hrowdeg : ∀ r ∈ R, (bip R K L).degree (.inl r) = Fintype.card α - K.card :=
    fun r hr => by rw [bip_degree_row hr (hL.1 r hr), hβ]
  obtain ⟨C⟩ := hcol
  set i₀ : Fin (Fintype.card α - K.card) := ⟨0, hΔpos⟩
  -- the matching of colour `i₀`
  have hexists : ∀ r ∈ R, ∃ σ, ∃ h : (bip R K L).Adj (.inl r) (.inr σ), C ⟨s(.inl r, .inr σ), h⟩ = i₀ := by
    intro r hr
    obtain ⟨w, hw, hc⟩ := exists_colour_at C (hrowdeg r hr) i₀
    cases w with
    | inl r' => exact absurd hw bip_not_ll
    | inr σ => exact ⟨σ, hw, hc⟩
  have hβne : Nonempty β := Fintype.card_pos_iff.1 (by omega)
  let f : α → β := fun r =>
    if h : ∃ σ, ∃ h : (bip R K L).Adj (.inl r) (.inr σ), C ⟨s(.inl r, .inr σ), h⟩ = i₀ then
      Classical.choose h else Classical.arbitrary β
  have hf : ∀ r ∈ R, ∃ h : (bip R K L).Adj (.inl r) (.inr (f r)), C ⟨s(.inl r, .inr (f r)), h⟩ = i₀ := by
    intro r hr
    have hex := hexists r hr
    simp only [f, dif_pos hex]
    exact Classical.choose_spec hex
  have hfmiss : ∀ r ∈ R, f r ∉ K.image (L r) := fun r hr =>
    (bip_adj_lr.1 (hf r hr).1).2
  have hfinj : Set.InjOn f R := by
    intro r hr r' hr' h
    obtain ⟨h1, c1⟩ := hf r hr
    obtain ⟨h2, c2⟩ := hf r' hr'
    have hv : (Sum.inr (f r) : α ⊕ β) ∈ (s(.inl r', .inr (f r')) : Sym2 (α ⊕ β)) := by
      rw [← h]; exact Sym2.mem_mk_right _ _
    have := colour_inj C (e := ⟨_, h1⟩) (f := ⟨_, h2⟩) (Sym2.mem_mk_right _ _) hv
      (c1.trans c2.symm)
    have := congrArg Subtype.val this
    rcases Sym2.eq_iff.1 this with ⟨h3, -⟩ | ⟨h3, -⟩
    · exact Sum.inl_injective h3
    · exact absurd h3 Sum.inl_ne_inr
  -- tight symbols are hit
  have htight : ∀ σ, R.card + K.card = Fintype.card α + cnt R K L σ → ∃ r ∈ R, f r = σ := by
    intro σ hσ
    have hdeg : (bip R K L).degree (.inr σ) = Fintype.card α - K.card := by
      have := bip_degree_sym (R := R) (K := K) (L := L) σ; omega
    obtain ⟨w, hw, hcw⟩ := exists_colour_at C hdeg i₀
    cases w with
    | inr σ' => exact absurd hw bip_not_rr
    | inl r =>
      have hadj : (bip R K L).Adj (.inl r) (.inr σ) := hw.symm
      have hr : r ∈ R := (bip_adj_lr.1 hadj).1
      refine ⟨r, hr, ?_⟩
      obtain ⟨h1, c1⟩ := hf r hr
      have c' : C ⟨s(.inl r, .inr σ), hadj⟩ = i₀ := by
        rw [← hcw]; congr 1; exact Subtype.ext Sym2.eq_swap
      have := colour_inj C (v := .inl r) (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
        (c1.trans c'.symm)
      have := congrArg Subtype.val this
      simp only at this
      exact Sum.inr_injective (Sym2.congr_right.1 this)
  -- the new column
  let L₁ : α → α → β := fun r g => if g = g₀ then f r else L r g
  have hL₁K : ∀ r g, g ∈ K → L₁ r g = L r g := by
    intro r g hg
    simp only [L₁, if_neg (fun h : g = g₀ => hg₀ (h ▸ hg))]
  refine ⟨L₁, ⟨?_, ?_⟩, hL₁K, ?_⟩
  · intro r hr g hg g' hg' h
    rw [coe_insert, Set.mem_insert_iff] at hg hg'
    rcases hg with rfl | hg <;> rcases hg' with rfl | hg'
    · rfl
    · exfalso
      simp only [L₁, if_pos rfl, if_neg (fun h : g' = g => hg₀ (h ▸ hg'))] at h
      exact hfmiss r hr (mem_image.2 ⟨g', hg', h.symm⟩)
    · exfalso
      simp only [L₁, if_pos rfl, if_neg (fun h' : g = g' => hg₀ (h' ▸ hg))] at h
      exact hfmiss r hr (mem_image.2 ⟨g, hg, h⟩)
    · rw [hL₁K r g hg, hL₁K r g' hg'] at h
      exact hL.1 r hr hg hg' h
  · intro g hg
    rcases mem_insert.1 hg with rfl | hg
    · intro r hr r' hr' h
      simp only [L₁, if_pos rfl] at h
      exact hfinj hr hr' h
    · intro r hr r' hr' h
      simp only at h
      rw [hL₁K r g hg, hL₁K r' g hg] at h
      exact hL.2 g hg hr hr' h
  · intro σ
    rw [card_insert_of_notMem hg₀]
    have hsub : R.filter (fun r => σ ∈ K.image (L r)) ⊆
        R.filter fun r => σ ∈ (insert g₀ K).image (L₁ r) := by
      intro r hr
      rw [mem_filter] at hr ⊢
      refine ⟨hr.1, ?_⟩
      obtain ⟨g, hg, hgσ⟩ := mem_image.1 hr.2
      exact mem_image.2 ⟨g, mem_insert_of_mem hg, by rw [hL₁K r g hg]; exact hgσ⟩
    have hle : cnt R K L σ ≤ cnt R (insert g₀ K) L₁ σ := card_le_card hsub
    by_cases ht : R.card + K.card = Fintype.card α + cnt R K L σ
    · obtain ⟨r, hr, hrσ⟩ := htight σ ht
      have hnew : r ∈ R.filter (fun r => σ ∈ (insert g₀ K).image (L₁ r)) := by
        rw [mem_filter]
        refine ⟨hr, mem_image.2 ⟨g₀, mem_insert_self _ _, ?_⟩⟩
        simp only [L₁, if_pos rfl]; exact hrσ
      have hold : r ∉ R.filter (fun r => σ ∈ K.image (L r)) := by
        rw [mem_filter, not_and]
        intro _ hm; rw [← hrσ] at hm; exact hfmiss r hr hm
      have : cnt R K L σ < cnt R (insert g₀ K) L₁ σ :=
        card_lt_card ⟨hsub, fun h => hold (h hnew)⟩
      omega
    · have := hc σ; omega

/-- Fill all columns. -/
theorem fill_cols (hβ : Fintype.card β = Fintype.card α) {R : Finset α} :
    ∀ m (K : Finset α) (L : α → α → β), (univ \ K).card = m → IsLatinRect R K L →
      RyserCond R K L → ∃ L', IsLatinRect R univ L' ∧ (∀ r g, g ∈ K → L' r g = L r g) ∧
        RyserCond R univ L' := by
  intro m
  induction m with
  | zero =>
    intro K L hm hL hc
    have : K = univ := by
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hm
      exact eq_univ_of_forall fun g => hm (mem_univ g)
    subst this
    exact ⟨L, hL, fun _ _ _ => rfl, hc⟩
  | succ m ih =>
    intro K L hm hL hc
    obtain ⟨g₀, hg₀⟩ := card_pos.1 (by omega : 0 < (univ \ K).card)
    have hg₀K : g₀ ∉ K := (mem_sdiff.1 hg₀).2
    obtain ⟨L₁, hL₁, hagree, hc₁⟩ := extend_col hβ hL hc hg₀K
    have hm' : (univ \ insert g₀ K).card = m := by
      have : univ \ insert g₀ K = (univ \ K).erase g₀ := by
        ext g; simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_erase, not_or]
      rw [this, card_erase_of_mem hg₀, hm]; omega
    obtain ⟨L', hL', hagree', hc'⟩ := ih (insert g₀ K) L₁ hm' hL₁ hc₁
    exact ⟨L', hL', fun r g hg => (hagree' r g (mem_insert_of_mem hg)).trans (hagree r g hg),
      hc'⟩

/-- Transpose. -/
def tr (L : α → α → β) : α → α → β := fun r g => L g r

theorem isLatinRect_tr {R K : Finset α} {L : α → α → β} (h : IsLatinRect R K L) :
    IsLatinRect K R (tr L) :=
  ⟨fun g hg => h.2 g hg, fun r hr => h.1 r hr⟩

/-- **Ryser's theorem.** -/
theorem ryser (hβ : Fintype.card β = Fintype.card α) {R K : Finset α} {L : α → α → β}
    (hL : IsLatinRect R K L)
    (hc : RyserCond R K L) :
    ∃ L', IsLatin L' ∧ ∀ r ∈ R, ∀ g ∈ K, L' r g = L r g := by
  classical
  obtain ⟨L₁, hL₁, hag₁, -⟩ := fill_cols hβ _ K L rfl hL hc
  -- the transpose has all rows; every symbol occurs in each of the `R` columns
  have hc₂ : RyserCond univ R (tr L₁) := by
    intro σ
    rw [card_univ]
    have hrow : ∀ r ∈ R, ∃ g, L₁ r g = σ := by
      intro r hr
      have hinj : Function.Injective (L₁ r) := fun g g' h =>
        hL₁.1 r hr (mem_coe.2 (mem_univ g)) (mem_coe.2 (mem_univ g')) h
      exact ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hβ.symm⟩).2 σ
    let col : α → α := fun r => if h : ∃ g, L₁ r g = σ then Classical.choose h else r
    have hcol : ∀ r ∈ R, L₁ r (col r) = σ := by
      intro r hr
      have := hrow r hr
      simp only [col, dif_pos this]
      exact Classical.choose_spec this
    have hsub : R.image col ⊆ univ.filter fun g => σ ∈ R.image (tr L₁ g) := by
      intro g hg
      obtain ⟨r, hr, rfl⟩ := mem_image.1 hg
      rw [mem_filter]
      exact ⟨mem_univ _, mem_image.2 ⟨r, hr, hcol r hr⟩⟩
    have hinj : Set.InjOn col R := by
      intro r hr r' hr' h
      have h1 := hcol r hr
      have h2 := hcol r' hr'
      rw [h] at h1
      exact hL₁.2 (col r') (mem_univ _) hr hr' (h1.trans h2.symm)
    have := card_le_card hsub
    rw [card_image_of_injOn hinj] at this
    unfold cnt
    omega
  obtain ⟨L₂, hL₂, hag₂, -⟩ := fill_cols hβ _ R (tr L₁) rfl (isLatinRect_tr hL₁) hc₂
  refine ⟨tr L₂, isLatinRect_tr hL₂, fun r hr g hg => ?_⟩
  show L₂ g r = L r g
  rw [hag₂ g r hr]
  exact hag₁ r g hg

end CDRBicolour.Latin
