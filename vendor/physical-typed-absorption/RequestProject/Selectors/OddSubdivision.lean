/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.PositiveBridge

@[expose] public section

/-!
# Odd subdivisions of a finite abstract selector and the transfer of matching modes

An `OddSubdivision H Q` of a finite abstract edge set `Q : Finset (Sym2 α)` in a host graph
`H` on `V` consists of

* an injective placement `φ : α → V` of the abstract vertices;
* for every abstract edge `e ∈ Q` an orientation `e = s(src e, tgt e)` (`src e ≠ tgt e`),
  a number `t e` and internal vertices `int e 1, …, int e (2 t e)`;

such that the path `pathV e 0 = φ (src e), int e 1, …, int e (2 t e), pathV e (2 t e + 1) =
φ (tgt e)` has all its `2 t e + 1` consecutive pairs adjacent in `H`, internal vertices of all
paths are pairwise distinct (`int_inj`) and avoid every image `φ x` (`int_ne_φ`).  From this
we derive that no path repeats a vertex and that paths of distinct edges only meet at common
endpoint images.

**Mode transfer** (`modeEdges_isMode`).  For an abstract matching mode `F` of `Q` covering
exactly `W ∪ S` (`SelBridge.IsMode Q W S F`), the host edge set `modeEdges D F` (positions
`0,2,…,2t_e` on selected paths, `1,3,…,2t_e - 1` on unselected ones) is a matching mode of
the path edges covering exactly `φ(W) ∪ internals` together with `φ(S)`, in the very same
`SelBridge.IsMode` form.
-/

namespace SelSubdiv

open Finset SelBridge

variable {α V : Type*}

/-- The `j`-th vertex of the path replacing the abstract edge `e`. -/
def pv (φ : α → V) (src tgt : Sym2 α → α) (t : Sym2 α → ℕ) (int : Sym2 α → ℕ → V)
    (e : Sym2 α) (j : ℕ) : V :=
  if j = 0 then φ (src e) else if j = 2 * t e + 1 then φ (tgt e) else int e j

/-- An odd subdivision of the abstract edge set `Q` inside the host graph `H`. -/
structure OddSubdivision (H : SimpleGraph V) (Q : Finset (Sym2 α)) where
  /-- placement of abstract vertices -/
  φ : α → V
  /-- chosen first endpoint of each abstract edge -/
  src : Sym2 α → α
  /-- chosen second endpoint of each abstract edge -/
  tgt : Sym2 α → α
  /-- the path for `e` has `2 t e + 1` edges -/
  t : Sym2 α → ℕ
  /-- internal vertices, `int e j` for `1 ≤ j ≤ 2 t e` -/
  int : Sym2 α → ℕ → V
  φ_inj : Function.Injective φ
  ends : ∀ e ∈ Q, s(src e, tgt e) = e
  src_ne_tgt : ∀ e ∈ Q, src e ≠ tgt e
  int_inj : ∀ e ∈ Q, ∀ e' ∈ Q, ∀ j j', 1 ≤ j → j ≤ 2 * t e → 1 ≤ j' → j' ≤ 2 * t e' →
    int e j = int e' j' → e = e' ∧ j = j'
  int_ne_φ : ∀ e ∈ Q, ∀ j, 1 ≤ j → j ≤ 2 * t e → ∀ x, int e j ≠ φ x
  adj : ∀ e ∈ Q, ∀ j, j ≤ 2 * t e →
    H.Adj (pv φ src tgt t int e j) (pv φ src tgt t int e (j + 1))

namespace OddSubdivision

variable {H : SimpleGraph V} {Q : Finset (Sym2 α)} (D : OddSubdivision H Q)

/-- Path vertices. -/
def pathV (e : Sym2 α) (j : ℕ) : V := pv D.φ D.src D.tgt D.t D.int e j

/-- The `j`-th edge of the path of `e` (`0 ≤ j ≤ 2 t e`). -/
def pe (e : Sym2 α) (j : ℕ) : Sym2 V := s(D.pathV e j, D.pathV e (j + 1))

variable {D}

lemma pathV_zero (e : Sym2 α) : D.pathV e 0 = D.φ (D.src e) := by
  simp [pathV, pv]

lemma pathV_top (e : Sym2 α) : D.pathV e (2 * D.t e + 1) = D.φ (D.tgt e) := by
  simp [pathV, pv]

lemma pathV_mid (e : Sym2 α) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 2 * D.t e) :
    D.pathV e j = D.int e j := by
  simp only [pathV, pv]
  rw [if_neg (by omega), if_neg (by omega)]

lemma mem_iff_src_tgt {e : Sym2 α} (he : e ∈ Q) (x : α) :
    x ∈ e ↔ D.src e = x ∨ D.tgt e = x := by
  conv_lhs => rw [← D.ends e he]
  rw [Sym2.mem_iff]; tauto

lemma pathV_eq_φ {e : Sym2 α} (he : e ∈ Q) {j : ℕ} (hj : j ≤ 2 * D.t e + 1) {x : α}
    (h : D.pathV e j = D.φ x) :
    (j = 0 ∧ D.src e = x) ∨ (j = 2 * D.t e + 1 ∧ D.tgt e = x) := by
  by_cases h0 : j = 0
  · subst h0; rw [pathV_zero] at h; exact Or.inl ⟨rfl, D.φ_inj h⟩
  by_cases ht : j = 2 * D.t e + 1
  · subst ht; rw [pathV_top] at h; exact Or.inr ⟨rfl, D.φ_inj h⟩
  rw [pathV_mid e (by omega) (by omega)] at h
  exact absurd h (D.int_ne_φ e he j (by omega) (by omega) x)

lemma pathV_eq_int {e e₀ : Sym2 α} (he : e ∈ Q) (he₀ : e₀ ∈ Q) {j j₀ : ℕ}
    (hj : j ≤ 2 * D.t e + 1) (h1 : 1 ≤ j₀) (h2 : j₀ ≤ 2 * D.t e₀)
    (h : D.pathV e j = D.int e₀ j₀) : e = e₀ ∧ j = j₀ := by
  by_cases h0 : j = 0
  · subst h0; rw [pathV_zero] at h
    exact absurd h.symm (D.int_ne_φ e₀ he₀ j₀ h1 h2 _)
  by_cases ht : j = 2 * D.t e + 1
  · subst ht; rw [pathV_top] at h
    exact absurd h.symm (D.int_ne_φ e₀ he₀ j₀ h1 h2 _)
  rw [pathV_mid e (by omega) (by omega)] at h
  exact D.int_inj e he e₀ he₀ j j₀ (by omega) (by omega) h1 h2 h

/-- **No repeated vertex**: each path is simple. -/
theorem pathV_injOn {e : Sym2 α} (he : e ∈ Q) {j j' : ℕ} (hj : j ≤ 2 * D.t e + 1)
    (hj' : j' ≤ 2 * D.t e + 1) (h : D.pathV e j = D.pathV e j') : j = j' := by
  by_cases h0 : j' = 0
  · subst h0; rw [pathV_zero] at h
    rcases pathV_eq_φ he hj h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · exact absurd h2.symm (D.src_ne_tgt e he)
  by_cases ht : j' = 2 * D.t e + 1
  · subst ht; rw [pathV_top] at h
    rcases pathV_eq_φ he hj h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact absurd h2 (D.src_ne_tgt e he)
    · exact h1
  rw [pathV_mid e (j := j') (by omega) (by omega)] at h
  exact (pathV_eq_int he he hj (by omega) (by omega) h).2

/-- Every path vertex is an abstract image or an internal vertex of that path. -/
lemma pathV_cases (e : Sym2 α) {j : ℕ} (hj : j ≤ 2 * D.t e + 1) :
    (∃ x, D.pathV e j = D.φ x) ∨ (1 ≤ j ∧ j ≤ 2 * D.t e ∧ D.pathV e j = D.int e j) := by
  by_cases h0 : j = 0
  · subst h0; exact Or.inl ⟨_, pathV_zero e⟩
  by_cases ht : j = 2 * D.t e + 1
  · subst ht; exact Or.inl ⟨_, pathV_top e⟩
  exact Or.inr ⟨by omega, by omega, pathV_mid e (by omega) (by omega)⟩

/-- **Paths of distinct edges meet only at common endpoint images.** -/
theorem paths_meet_at_ends {e e' : Sym2 α} (he : e ∈ Q) (he' : e' ∈ Q) (hne : e ≠ e')
    {j j' : ℕ} (hj : j ≤ 2 * D.t e + 1) (hj' : j' ≤ 2 * D.t e' + 1)
    (h : D.pathV e j = D.pathV e' j') :
    ∃ x, x ∈ e ∧ x ∈ e' ∧ D.pathV e j = D.φ x := by
  rcases pathV_cases (D := D) e' hj' with ⟨x, hx⟩ | ⟨h1, h2, hx⟩
  · rw [hx] at h
    refine ⟨x, ?_, ?_, h⟩
    · rw [mem_iff_src_tgt he]
      rcases pathV_eq_φ he hj h with ⟨_, h⟩ | ⟨_, h⟩ <;> tauto
    · rw [mem_iff_src_tgt he']
      rcases pathV_eq_φ he' hj' hx with ⟨_, h⟩ | ⟨_, h⟩ <;> tauto
  · rw [hx] at h
    exact absurd (pathV_eq_int he he' hj h1 h2 h).1 hne

lemma mem_pe_iff (e : Sym2 α) (j : ℕ) (y : V) :
    y ∈ D.pe e j ↔ D.pathV e j = y ∨ D.pathV e (j + 1) = y := by
  rw [pe, Sym2.mem_iff]; tauto

lemma mem_pe_int {e e₀ : Sym2 α} (he : e ∈ Q) (he₀ : e₀ ∈ Q) {j j₀ : ℕ} (hj : j ≤ 2 * D.t e)
    (h1 : 1 ≤ j₀) (h2 : j₀ ≤ 2 * D.t e₀) :
    D.int e₀ j₀ ∈ D.pe e j ↔ e = e₀ ∧ (j = j₀ ∨ j + 1 = j₀) := by
  rw [mem_pe_iff]
  constructor
  · rintro (h | h)
    · obtain ⟨rfl, rfl⟩ := pathV_eq_int he he₀ (by omega) h1 h2 h; tauto
    · obtain ⟨rfl, h⟩ := pathV_eq_int he he₀ (by omega) h1 h2 h; tauto
  · rintro ⟨rfl, rfl | rfl⟩
    · exact Or.inl (pathV_mid e h1 h2)
    · exact Or.inr (pathV_mid e h1 h2)

lemma mem_pe_φ {e : Sym2 α} (he : e ∈ Q) {j : ℕ} (hj : j ≤ 2 * D.t e) (x : α) :
    D.φ x ∈ D.pe e j ↔ (j = 0 ∧ D.src e = x) ∨ (j = 2 * D.t e ∧ D.tgt e = x) := by
  rw [mem_pe_iff]
  constructor
  · rintro (h | h)
    · rcases pathV_eq_φ he (by omega) h with h | ⟨h, _⟩
      · exact Or.inl h
      · omega
    · rcases pathV_eq_φ he (by omega) h with ⟨h, _⟩ | ⟨h, h'⟩
      · omega
      · exact Or.inr ⟨by omega, h'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl (pathV_zero e)
    · exact Or.inr (pathV_top e)

lemma mem_pe_cases (e : Sym2 α) {j : ℕ} (hj : j ≤ 2 * D.t e) {y : V} (h : y ∈ D.pe e j) :
    (∃ x, y = D.φ x) ∨ ∃ k, 1 ≤ k ∧ k ≤ 2 * D.t e ∧ y = D.int e k := by
  rw [mem_pe_iff] at h
  rcases h with h | h
  · rcases pathV_cases (D := D) e (j := j) (by omega) with ⟨x, hx⟩ | ⟨h1, h2, hx⟩
    · exact Or.inl ⟨x, h ▸ hx⟩
    · exact Or.inr ⟨j, h1, h2, h ▸ hx⟩
  · rcases pathV_cases (D := D) e (j := j + 1) (by omega) with ⟨x, hx⟩ | ⟨h1, h2, hx⟩
    · exact Or.inl ⟨x, h ▸ hx⟩
    · exact Or.inr ⟨j + 1, h1, h2, h ▸ hx⟩

/-- The edge through which an abstract vertex image `φ x` leaves the path of `e`. -/
def endEdge [DecidableEq α] (x : α) (e : Sym2 α) : Sym2 V := if D.src e = x then D.pe e 0 else D.pe e (2 * D.t e)

/-- Edges of the subdivision containing `φ x`: one end edge per abstract edge at `x`. -/
lemma pe_mem_φ_iff [DecidableEq α] {e : Sym2 α} (he : e ∈ Q) {j : ℕ} (hj : j ≤ 2 * D.t e) (x : α) :
    D.φ x ∈ D.pe e j ↔ x ∈ e ∧ j % 2 = 0 ∧ D.pe e j = endEdge (D := D) x e := by
  rw [mem_pe_φ he hj, mem_iff_src_tgt he]
  have hne := D.src_ne_tgt e he
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl rfl, rfl, by simp [endEdge]⟩
    · exact ⟨Or.inr rfl, by omega, by simp [endEdge, hne]⟩
  · rintro ⟨hx | hx, -, hpe⟩
    · subst hx
      simp only [endEdge, if_true] at hpe
      by_cases h0 : j = 0
      · exact Or.inl ⟨h0, rfl⟩
      · exfalso
        have : D.pathV e 0 ∈ D.pe e j := hpe ▸ Sym2.mem_mk_left _ _
        rw [pathV_zero, mem_pe_φ he hj] at this
        rcases this with ⟨h, _⟩ | ⟨_, h⟩
        · exact h0 h
        · exact hne h.symm
    · subst hx
      by_cases hs : D.src e = D.tgt e
      · exact absurd hs hne
      simp only [endEdge, hs, if_false] at hpe
      have : D.pathV e (2 * D.t e + 1) ∈ D.pe e j := hpe ▸ Sym2.mem_mk_right _ _
      rw [pathV_top, mem_pe_φ he hj] at this
      rcases this with ⟨_, h⟩ | h
      · exact absurd h hne
      · exact Or.inr h

variable [DecidableEq α] [DecidableEq V]

section
variable (D)

/-- All edges of the subdivision (the base edges). -/
def pathEdges : Finset (Sym2 V) := Q.biUnion (fun e => (range (2 * D.t e + 1)).image (D.pe e))

/-- All internal subdivision vertices. -/
def internals : Finset V := Q.biUnion (fun e => (Icc 1 (2 * D.t e)).image (D.int e))

/-- The host edge set of an abstract mode `F`: even positions on selected paths, odd
positions on unselected ones. -/
def modeEdges (F : Finset (Sym2 α)) : Finset (Sym2 V) :=
  Q.biUnion (fun e => ((range (2 * D.t e + 1)).filter
    (fun j => (j % 2 = 0 ↔ e ∈ F))).image (D.pe e))

end

lemma mem_modeEdges (F : Finset (Sym2 α)) (f : Sym2 V) :
    f ∈ D.modeEdges F ↔ ∃ e ∈ Q, ∃ j, j ≤ 2 * D.t e ∧ (j % 2 = 0 ↔ e ∈ F) ∧ D.pe e j = f := by
  simp only [modeEdges, mem_biUnion, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨e, he, j, ⟨hj, hp⟩, rfl⟩; exact ⟨e, he, j, by omega, hp, rfl⟩
  · rintro ⟨e, he, j, hj, hp, rfl⟩; exact ⟨e, he, j, ⟨by omega, hp⟩, rfl⟩

omit [DecidableEq α] in
lemma mem_pathEdges (f : Sym2 V) :
    f ∈ D.pathEdges ↔ ∃ e ∈ Q, ∃ j, j ≤ 2 * D.t e ∧ D.pe e j = f := by
  simp only [pathEdges, mem_biUnion, mem_image, mem_range]
  constructor
  · rintro ⟨e, he, j, hj, rfl⟩; exact ⟨e, he, j, by omega, rfl⟩
  · rintro ⟨e, he, j, hj, rfl⟩; exact ⟨e, he, j, by omega, rfl⟩

omit [DecidableEq α] in
lemma mem_internals (y : V) :
    y ∈ D.internals ↔ ∃ e ∈ Q, ∃ j, 1 ≤ j ∧ j ≤ 2 * D.t e ∧ D.int e j = y := by
  simp only [internals, mem_biUnion, mem_image, mem_Icc]
  constructor
  · rintro ⟨e, he, j, ⟨h1, h2⟩, rfl⟩; exact ⟨e, he, j, h1, h2, rfl⟩
  · rintro ⟨e, he, j, h1, h2, rfl⟩; exact ⟨e, he, j, ⟨h1, h2⟩, rfl⟩

lemma modeEdges_subset (F : Finset (Sym2 α)) : D.modeEdges F ⊆ D.pathEdges := by
  intro f hf
  obtain ⟨e, he, j, hj, _, rfl⟩ := (mem_modeEdges F f).mp hf
  exact (mem_pathEdges _).mpr ⟨e, he, j, hj, rfl⟩

omit [DecidableEq α] in
lemma φ_not_mem_internals (x : α) : D.φ x ∉ D.internals := by
  intro h
  obtain ⟨e, he, j, h1, h2, hj⟩ := (mem_internals _).mp h
  exact D.int_ne_φ e he j h1 h2 x hj

lemma endEdge_mem_modeEdges {F : Finset (Sym2 α)} {e : Sym2 α} (he : e ∈ Q) (heF : e ∈ F)
    {x : α} (hx : x ∈ e) :
    endEdge (D := D) x e ∈ D.modeEdges F ∧ D.φ x ∈ endEdge (D := D) x e := by
  rw [mem_iff_src_tgt he] at hx
  by_cases hs : D.src e = x
  · simp only [endEdge, hs, if_true]
    refine ⟨(mem_modeEdges F _).mpr ⟨e, he, 0, by omega, by simp [heF], rfl⟩, ?_⟩
    rw [mem_pe_φ he (by omega)]; exact Or.inl ⟨rfl, hs⟩
  · simp only [endEdge, hs, if_false]
    have ht : D.tgt e = x := by tauto
    refine ⟨(mem_modeEdges F _).mpr ⟨e, he, 2 * D.t e, le_rfl, by simp [heF], rfl⟩, ?_⟩
    rw [mem_pe_φ he le_rfl]; exact Or.inr ⟨rfl, ht⟩

/-- **Mode transfer through the odd subdivision.**  An abstract matching mode `F` of `Q`
covering exactly `W ∪ S` gives the host matching mode `modeEdges D F` of the subdivision
edges, covering exactly `(φ(W) ∪ internals) ∪ φ(S)`. -/
theorem modeEdges_isMode {W S : Finset α} {F : Finset (Sym2 α)} (hM : IsMode Q W S F) :
    IsMode D.pathEdges (W.image D.φ ∪ D.internals) (S.image D.φ) (D.modeEdges F) := by
  refine ⟨modeEdges_subset F, ?_, ?_⟩
  · intro y hy
    have hy' : (∃ x ∈ W ∪ S, D.φ x = y) ∨ y ∈ D.internals := by
      simp only [mem_union, mem_image] at hy ⊢
      rcases hy with (⟨x, hx, h⟩ | h) | ⟨x, hx, h⟩
      · exact Or.inl ⟨x, Or.inl hx, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨x, Or.inr hx, h⟩
    rw [card_eq_one]
    rcases hy' with ⟨x, hx, rfl⟩ | hyI
    · have h1 := hM.2.1 x hx
      obtain ⟨e₀, he₀⟩ := card_eq_one.mp h1
      have he₀F : e₀ ∈ F ∧ x ∈ e₀ := by
        have : e₀ ∈ F.filter (fun e => x ∈ e) := by rw [he₀]; exact mem_singleton_self _
        exact mem_filter.mp this
      have he₀Q : e₀ ∈ Q := hM.1 he₀F.1
      refine ⟨endEdge (D := D) x e₀, ?_⟩
      ext f
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hf, hxf⟩
        obtain ⟨e, he, j, hj, hp, rfl⟩ := (mem_modeEdges F f).mp hf
        obtain ⟨hxe, hj0, hpe⟩ := (pe_mem_φ_iff he hj x).mp hxf
        have heF : e ∈ F := hp.mp hj0
        have : e ∈ F.filter (fun e => x ∈ e) := mem_filter.mpr ⟨heF, hxe⟩
        rw [he₀, mem_singleton] at this
        subst this; exact hpe
      · rintro rfl
        exact endEdge_mem_modeEdges he₀Q he₀F.1 he₀F.2
    · obtain ⟨e₀, he₀, j₀, h1, h2, rfl⟩ := (mem_internals _).mp hyI
      refine ⟨D.pe e₀ (if ((j₀ - 1) % 2 = 0 ↔ e₀ ∈ F) then j₀ - 1 else j₀), ?_⟩
      ext f
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hf, hyf⟩
        obtain ⟨e, he, j, hj, hp, rfl⟩ := (mem_modeEdges F f).mp hf
        obtain ⟨rfl, hj'⟩ := (mem_pe_int he he₀ hj h1 h2).mp hyf
        congr 1
        by_cases hF : e ∈ F
        · simp only [hF, iff_true] at hp ⊢
          split_ifs with hc <;> omega
        · simp only [hF, iff_false] at hp ⊢
          split_ifs with hc <;> omega
      · rintro rfl
        constructor
        · refine (mem_modeEdges F _).mpr ⟨e₀, he₀, _, ?_, ?_, rfl⟩
          · split_ifs <;> omega
          · by_cases hF : e₀ ∈ F
            · simp only [hF, iff_true]; split_ifs with hc <;> omega
            · simp only [hF, iff_false]; split_ifs with hc <;> omega
        · rw [mem_pe_int he₀ he₀ (by split_ifs <;> omega) h1 h2]
          refine ⟨rfl, ?_⟩
          split_ifs <;> omega
  · intro y hy f hf hyf
    obtain ⟨e, he, j, hj, hp, rfl⟩ := (mem_modeEdges F f).mp hf
    rcases mem_pe_cases e hj hyf with ⟨x, rfl⟩ | ⟨k, h1, h2, rfl⟩
    · obtain ⟨hxe, hj0, -⟩ := (pe_mem_φ_iff he hj x).mp hyf
      have hxWS := covered_of_mem hM (hp.mp hj0) hxe
      apply hy
      rcases mem_union.mp hxWS with h | h
      · exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ h))
      · exact mem_union_right _ (mem_image_of_mem _ h)
    · apply hy
      exact mem_union_left _ (mem_union_right _ ((mem_internals _).mpr ⟨e, he, k, h1, h2, rfl⟩))

/-! ### Counting: exact sizes and bounds -/

omit [DecidableEq α] [DecidableEq V] in
lemma pe_zero_of_t_zero {e : Sym2 α} (he : e ∈ Q) (ht : D.t e = 0) :
    D.pe e 0 = Sym2.map D.φ e := by
  have h1 : D.pathV e 1 = D.φ (D.tgt e) := by
    have := pathV_top (D := D) e; rwa [ht] at this
  rw [pe, pathV_zero, zero_add, h1]
  conv_rhs => rw [← D.ends e he]
  rfl

omit [DecidableEq α] [DecidableEq V] in
/-- Distinct positions give distinct edges. -/
theorem pe_inj {e e' : Sym2 α} (he : e ∈ Q) (he' : e' ∈ Q) {j j' : ℕ} (hj : j ≤ 2 * D.t e)
    (hj' : j' ≤ 2 * D.t e') (h : D.pe e j = D.pe e' j') : e = e' ∧ j = j' := by
  have hee : e = e' := by
    by_cases ht : 1 ≤ D.t e
    · have hk := (mem_pe_int (D := D) he he hj (j₀ := if j = 0 then 1 else j)
        (by split_ifs <;> omega) (by split_ifs <;> omega)).mpr ⟨rfl, by split_ifs <;> omega⟩
      rw [h, mem_pe_int he' he hj' (by split_ifs <;> omega) (by split_ifs <;> omega)] at hk
      exact hk.1.symm
    by_cases ht' : 1 ≤ D.t e'
    · have hk := (mem_pe_int (D := D) he' he' hj' (j₀ := if j' = 0 then 1 else j')
        (by split_ifs <;> omega) (by split_ifs <;> omega)).mpr ⟨rfl, by split_ifs <;> omega⟩
      rw [← h, mem_pe_int he he' hj (by split_ifs <;> omega) (by split_ifs <;> omega)] at hk
      exact hk.1
    have h0 : j = 0 := by omega
    have h0' : j' = 0 := by omega
    subst h0 h0'
    rw [pe_zero_of_t_zero he (by omega), pe_zero_of_t_zero he' (by omega)] at h
    exact Sym2.map.injective D.φ_inj h
  subst hee
  refine ⟨rfl, ?_⟩
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact pathV_injOn he (by omega) (by omega) h1
  · have := pathV_injOn he (by omega) (by omega) h1
    have := pathV_injOn he (by omega) (by omega) h2
    omega

omit [DecidableEq α] in
/-- **Exact base-edge count**: `|E(subdivision)| = ∑_e (2 t_e + 1)`. -/
theorem pathEdges_card : D.pathEdges.card = ∑ e ∈ Q, (2 * D.t e + 1) := by
  rw [pathEdges, card_biUnion]
  · refine sum_congr rfl (fun e he => ?_)
    rw [card_image_of_injOn, card_range]
    intro j hj j' hj' h
    simp only [coe_range, Set.mem_Iio] at hj hj'
    exact (pe_inj he he (by omega) (by omega) h).2
  · intro e he e' he' hne
    rw [Function.onFun, disjoint_left]
    intro f hf hf'
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hf
    obtain ⟨j', hj', h⟩ := mem_image.mp hf'
    rw [mem_range] at hj hj'
    exact hne (pe_inj he' he (by omega) (by omega) h).1.symm

omit [DecidableEq α] in
/-- **Exact internal-vertex count**: `|internals| = ∑_e 2 t_e`. -/
theorem internals_card : D.internals.card = ∑ e ∈ Q, 2 * D.t e := by
  rw [internals, card_biUnion]
  · refine sum_congr rfl (fun e he => ?_)
    rw [card_image_of_injOn, Nat.card_Icc]
    · omega
    intro j hj j' hj' h
    simp only [coe_Icc, Set.mem_Icc] at hj hj'
    exact (D.int_inj e he e he j j' hj.1 hj.2 hj'.1 hj'.2 h).2
  · intro e he e' he' hne
    rw [Function.onFun, disjoint_left]
    intro y hy hy'
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
    obtain ⟨j', hj', h⟩ := mem_image.mp hy'
    rw [mem_Icc] at hj hj'
    exact hne (D.int_inj e' he' e he j' j hj'.1 hj'.2 hj.1 hj.2 h).1.symm

omit [DecidableEq α] in
lemma disjoint_image_internals (W : Finset α) : Disjoint (W.image D.φ) D.internals := by
  rw [disjoint_left]
  intro y hy hy'
  obtain ⟨x, _, rfl⟩ := mem_image.mp hy
  exact φ_not_mem_internals x hy'

omit [DecidableEq α] in
/-- Exact count of the non-port covered set `φ(W) ∪ internals`. -/
theorem auxCover_card (W : Finset α) :
    (W.image D.φ ∪ D.internals).card = W.card + ∑ e ∈ Q, 2 * D.t e := by
  rw [card_union_of_disjoint (disjoint_image_internals W), internals_card,
    card_image_of_injective _ D.φ_inj]

omit [DecidableEq α] in
/-- **Edge bound** under path length `≤ ℓ`. -/
theorem pathEdges_card_le {ℓ : ℕ} (hℓ : ∀ e ∈ Q, 2 * D.t e + 1 ≤ ℓ) :
    D.pathEdges.card ≤ ℓ * Q.card := by
  rw [pathEdges_card, mul_comm]
  exact (sum_le_sum hℓ).trans (by simp)

omit [DecidableEq α] in
/-- **Internal-vertex bound** under path length `≤ ℓ`. -/
theorem internals_card_le {ℓ : ℕ} (hℓ : ∀ e ∈ Q, 2 * D.t e + 1 ≤ ℓ) :
    D.internals.card ≤ (ℓ - 1) * Q.card := by
  have h : ∀ e ∈ Q, 2 * D.t e ≤ ℓ - 1 := fun e he => by have := hℓ e he; omega
  rw [internals_card, mul_comm]
  exact (sum_le_sum h).trans (by simp)

/-- The vertex set of the subdivided selector. -/
def subdivVerts [Fintype α] : Finset V := univ.image D.φ ∪ D.internals

omit [DecidableEq α] in
/-- **Vertex count and bound**: `|V(subdivision)| = |α| + ∑ 2 t_e ≤ |α| + (ℓ-1) e(Q)`. -/
theorem subdivVerts_card [Fintype α] {ℓ : ℕ} (hℓ : ∀ e ∈ Q, 2 * D.t e + 1 ≤ ℓ) :
    D.subdivVerts.card = Fintype.card α + ∑ e ∈ Q, 2 * D.t e ∧
    D.subdivVerts.card ≤ Fintype.card α + (ℓ - 1) * Q.card := by
  have h := auxCover_card (D := D) univ
  rw [card_univ] at h
  refine ⟨h, ?_⟩
  rw [subdivVerts, h, ← internals_card]
  have := internals_card_le (D := D) hℓ
  omega

/-- **Degree bound** `max(2, Δ(Q))` in the subdivision: every host vertex lies in at most
`max 2 Δ` subdivision edges when every abstract vertex lies in at most `Δ` edges of `Q`. -/
theorem pathEdges_degree_le {Δ : ℕ} (hΔ : ∀ x, (Q.filter (fun e => x ∈ e)).card ≤ Δ) (y : V) :
    (D.pathEdges.filter (fun f => y ∈ f)).card ≤ max 2 Δ := by
  by_cases hy : ∃ x, D.φ x = y
  · obtain ⟨x, rfl⟩ := hy
    have hsub : D.pathEdges.filter (fun f => D.φ x ∈ f) ⊆
        (Q.filter (fun e => x ∈ e)).image (endEdge (D := D) x) := by
      intro f hf
      rw [mem_filter] at hf
      obtain ⟨e, he, j, hj, rfl⟩ := (mem_pathEdges _).mp hf.1
      obtain ⟨hxe, -, hpe⟩ := (pe_mem_φ_iff he hj x).mp hf.2
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨he, hxe⟩, hpe.symm⟩
    exact (card_le_card hsub).trans (card_image_le.trans ((hΔ x).trans (le_max_right _ _)))
  by_cases hyI : y ∈ D.internals
  · obtain ⟨e₀, he₀, j₀, h1, h2, rfl⟩ := (mem_internals _).mp hyI
    have hsub : D.pathEdges.filter (fun f => D.int e₀ j₀ ∈ f) ⊆
        {D.pe e₀ (j₀ - 1), D.pe e₀ j₀} := by
      intro f hf
      rw [mem_filter] at hf
      obtain ⟨e, he, j, hj, rfl⟩ := (mem_pathEdges _).mp hf.1
      obtain ⟨rfl, hj'⟩ := (mem_pe_int he he₀ hj h1 h2).mp hf.2
      rcases hj' with rfl | hj'
      · simp
      · have : j = j₀ - 1 := by omega
        subst this; simp
    exact (card_le_card hsub).trans (card_le_two.trans (le_max_left _ _))
  · have : D.pathEdges.filter (fun f => y ∈ f) = ∅ := by
      rw [filter_eq_empty_iff]
      intro f hf hyf
      obtain ⟨e, he, j, hj, rfl⟩ := (mem_pathEdges _).mp hf
      rcases mem_pe_cases e hj hyf with ⟨x, rfl⟩ | ⟨k, h1, h2, rfl⟩
      · exact hy ⟨x, rfl⟩
      · exact hyI ((mem_internals _).mpr ⟨e, he, k, h1, h2, rfl⟩)
    rw [this]; simp

/-! ### Degenerate cases -/

/-- `Q = ∅` (e.g. `r = 0`, empty selector): no edges, no internals, empty modes. -/
theorem empty_selector (hQ : Q = ∅) (F : Finset (Sym2 α)) :
    D.pathEdges = ∅ ∧ D.internals = ∅ ∧ D.modeEdges F = ∅ := by
  subst hQ; simp [pathEdges, internals, modeEdges]

/-- All `t_e = 0` (no subdivision): the host mode is the image of the abstract mode, recovering
the length-one placement. -/
theorem modeEdges_of_t_zero (ht : ∀ e ∈ Q, D.t e = 0) {F : Finset (Sym2 α)} (hF : F ⊆ Q) :
    D.modeEdges F = F.image (Sym2.map D.φ) ∧ D.internals = ∅ := by
  constructor
  · ext f
    rw [mem_modeEdges, mem_image]
    constructor
    · rintro ⟨e, he, j, hj, hp, rfl⟩
      have h0 : j = 0 := by have := ht e he; omega
      subst h0
      exact ⟨e, hp.mp rfl, (pe_zero_of_t_zero he (ht e he)).symm⟩
    · rintro ⟨e, heF, rfl⟩
      exact ⟨e, hF heF, 0, by omega, by simp [heF], pe_zero_of_t_zero (hF heF) (ht e (hF heF))⟩
  · rw [← card_eq_zero, internals_card]
    exact sum_eq_zero (fun e he => by simp [ht e he])

end OddSubdivision

end SelSubdiv
