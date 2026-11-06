/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Basic
public import Mathlib

/-!
# Block-type spectrum: necessary conditions (backlog item 3)

For a strictly bicoloured STS, every block has type `iij` (two points of colour `i`, one of
colour `j ≠ i`).  Write `typeCount S col i j` for the number of blocks of type `iij`.

**Per-vertex identity.**  For a point `x` of colour `i ≠ j`, the points of colour `j` are
partitioned by the blocks through `x`; such a block contains `0`, `1` or `2` of them, and it
contains exactly one iff it has type `iij`.  Hence

  `|class j| = m_x + 2 · m'_x`,

where `m_x` counts blocks of type `iij` through `x` (`localCount`), and so
`m_x ≡ |class j| (mod 2)` (`localCount_mod_two`).

**Double counting.**  `∑_{x ∈ class i} m_x = 2 · typeCount i j` (`sum_localCount`).

**Lower bound.**  If `|class j|` is odd, every `x` of colour `i` lies in a block of type
`iij`, so `|class i| ≤ 2 · typeCount i j` (`typeCount_lower`).  For admissible profiles
exactly one class is odd; if it is `C`, this gives `N_AAC ≥ a/2` and `N_BBC ≥ b/2`.
-/

@[expose] public section

namespace CDRBicolour.BlockTypes

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Number of points of colour `j` in `B`. -/
def cnt (col : V → Fin 3) (j : Fin 3) (B : Finset V) : ℕ := #(B.filter fun y => col y = j)

/-- Number of blocks of type `iij`: two points of colour `i`, one of colour `j`. -/
def typeCount (S : STS V) (col : V → Fin 3) (i j : Fin 3) : ℕ :=
  #(S.blocks.filter fun B => cnt col i B = 2 ∧ cnt col j B = 1)

/-- Blocks through `x` containing exactly one point of colour `j`. -/
def localCount (S : STS V) (col : V → Fin 3) (j : Fin 3) (x : V) : ℕ :=
  #(S.blocks.filter fun B => x ∈ B ∧ cnt col j B = 1)

/-- Blocks through `x` containing exactly two points of colour `j`. -/
def localCount₂ (S : STS V) (col : V → Fin 3) (j : Fin 3) (x : V) : ℕ :=
  #(S.blocks.filter fun B => x ∈ B ∧ cnt col j B = 2)

/-- The blocks through `x` partition the points of colour `j ≠ col x`. -/
theorem sum_cnt_through (S : STS V) (col : V → Fin 3) {j : Fin 3} {x : V} (hx : col x ≠ j) :
    ∑ B ∈ S.blocks.filter (fun B => x ∈ B), cnt col j B = classSize col j := by
  unfold classSize cnt
  rw [← card_biUnion]
  · congr 1
    ext y
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨B, _, _, hy⟩
      exact hy
    · intro hy
      have hne : x ≠ y := fun h => hx (h ▸ hy)
      obtain ⟨B, ⟨hB, hxB, hyB⟩, _⟩ := S.existsUnique_block x y hne
      exact ⟨B, ⟨hB, hxB⟩, hyB, hy⟩
  · intro B₁ h₁ B₂ h₂ hne
    simp only [mem_coe, mem_filter] at h₁ h₂
    refine Finset.disjoint_left.mpr fun y hy1 hy2 => ?_
    rw [mem_filter] at hy1 hy2
    have hxy : x ≠ y := fun h => hx (h ▸ hy1.2)
    obtain ⟨B, _, hu⟩ := S.existsUnique_block x y hxy
    exact hne ((hu B₁ ⟨h₁.1, h₁.2, hy1.1⟩).trans (hu B₂ ⟨h₂.1, h₂.2, hy2.1⟩).symm)

/-- A block through `x` contains at most two points of a colour different from `col x`. -/
theorem cnt_le_two (S : STS V) (col : V → Fin 3) {j : Fin 3} {x : V} (hx : col x ≠ j)
    {B : Finset V} (hB : B ∈ S.blocks) (hxB : x ∈ B) : cnt col j B ≤ 2 := by
  have hsub : B.filter (fun y => col y = j) ⊆ B.erase x := by
    intro y hy
    rw [mem_filter] at hy
    exact mem_erase.mpr ⟨fun h => hx (h ▸ hy.2), hy.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem hxB, S.card_eq_three B hB] at this
  exact this

/-- **Per-vertex identity**: `|class j| = m_x + 2 m'_x` for `col x ≠ j`. -/
theorem classSize_eq_local (S : STS V) (col : V → Fin 3) {j : Fin 3} {x : V}
    (hx : col x ≠ j) :
    classSize col j = localCount S col j x + 2 * localCount₂ S col j x := by
  rw [← sum_cnt_through S col hx]
  have hterm : ∀ B ∈ S.blocks.filter (fun B => x ∈ B),
      cnt col j B = (if cnt col j B = 1 then 1 else 0) + 2 * (if cnt col j B = 2 then 1 else 0) := by
    intro B hB
    rw [mem_filter] at hB
    have := cnt_le_two S col hx hB.1 hB.2
    interval_cases h : cnt col j B <;> simp
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, sum_boole, sum_boole, filter_filter,
    filter_filter]
  simp only [Nat.cast_id, localCount, localCount₂]

/-- **Parity**: the number of `iij` blocks through `x` has the parity of `|class j|`. -/
theorem localCount_mod_two (S : STS V) (col : V → Fin 3) {j : Fin 3} {x : V}
    (hx : col x ≠ j) : localCount S col j x % 2 = classSize col j % 2 := by
  rw [classSize_eq_local S col hx]
  omega

/-- Colour counts of a triple of distinct points. -/
theorem cnt_triple (col : V → Fin 3) (c : Fin 3) {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) :
    cnt col c {p, q, r} = (if col p = c then 1 else 0) + (if col q = c then 1 else 0) +
      (if col r = c then 1 else 0) := by
  rw [cnt, card_filter, sum_insert (by simp [hpq, hpr]), sum_insert (by simp [hqr]),
    sum_singleton, add_assoc]

/-- The colour pattern of a bicoloured triple. -/
theorem fin3_pattern : ∀ a b c i j : Fin 3, ({a, b, c} : Finset (Fin 3)).card = 2 → i ≠ j →
    ((if a = j then 1 else 0) + (if b = j then 1 else 0) + (if c = j then 1 else 0) : ℕ) = 1 →
    ((if a = i then 1 else 0) + (if b = i then 1 else 0) + (if c = i then 1 else 0) : ℕ) = 0 ∨
    ((if a = i then 1 else 0) + (if b = i then 1 else 0) + (if c = i then 1 else 0) : ℕ) = 2 := by
  decide

/-- In a bicoloured block with exactly one point of colour `j`, the colour `i ≠ j` occurs
`0` or `2` times. -/
theorem cnt_zero_or_two (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col)
    {i j : Fin 3} (hij : i ≠ j) {B : Finset V} (hB : B ∈ S.blocks) (h1 : cnt col j B = 1) :
    cnt col i B = 0 ∨ cnt col i B = 2 := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp (S.card_eq_three B hB)
  have himg := hcol _ hB
  simp only [image_insert, image_singleton] at himg
  rw [cnt_triple col j hpq hpr hqr] at h1
  rw [cnt_triple col i hpq hpr hqr]
  exact fin3_pattern _ _ _ i j himg hij h1

/-- Swapping the double sum over points of colour `i` and blocks with exactly `v` points of
colour `j`. -/
theorem sum_local_swap (S : STS V) (col : V → Fin 3) (i j : Fin 3) (v : ℕ) :
    ∑ x ∈ univ.filter (fun x => col x = i), #(S.blocks.filter fun B => x ∈ B ∧ cnt col j B = v) =
      ∑ B ∈ S.blocks.filter (fun B => cnt col j B = v), cnt col i B := by
  simp only [card_filter]
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun B _ => ?_
  by_cases h : cnt col j B = v
  · rw [if_pos h]
    simp only [h, and_true, ← ite_and]
    rw [← card_filter, cnt]
    congr 1
    ext x
    simp [and_comm]
  · rw [if_neg h]
    exact sum_eq_zero fun x _ => by simp [h]

/-- **Double counting**: `∑_{x ∈ class i} m_x = 2 · typeCount i j`. -/
theorem sum_localCount (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col)
    {i j : Fin 3} (hij : i ≠ j) :
    ∑ x ∈ univ.filter (fun x => col x = i), localCount S col j x = 2 * typeCount S col i j := by
  rw [show ∑ x ∈ univ.filter (fun x => col x = i), localCount S col j x =
    ∑ B ∈ S.blocks.filter (fun B => cnt col j B = 1), cnt col i B from sum_local_swap S col i j 1]
  rw [typeCount, card_eq_sum_ones, mul_sum, sum_filter, sum_filter]
  refine sum_congr rfl fun B hB => ?_
  by_cases h1 : cnt col j B = 1
  · rcases cnt_zero_or_two S col hcol hij hB h1 with h | h <;> simp [h, h1]
  · simp [h1]

/-- The colour pattern of a triple with two points of colour `j`. -/
theorem fin3_pattern₂ : ∀ a b c i j : Fin 3, i ≠ j →
    ((if a = j then 1 else 0) + (if b = j then 1 else 0) + (if c = j then 1 else 0) : ℕ) = 2 →
    ((if a = i then 1 else 0) + (if b = i then 1 else 0) + (if c = i then 1 else 0) : ℕ) ≤ 1 := by
  decide

/-- **Second double counting**: `∑_{x ∈ class i} m'_x = typeCount j i` (blocks `jji`). -/
theorem sum_localCount₂ (S : STS V) (col : V → Fin 3) {i j : Fin 3} (hij : i ≠ j) :
    ∑ x ∈ univ.filter (fun x => col x = i), localCount₂ S col j x = typeCount S col j i := by
  rw [show ∑ x ∈ univ.filter (fun x => col x = i), localCount₂ S col j x =
    ∑ B ∈ S.blocks.filter (fun B => cnt col j B = 2), cnt col i B from sum_local_swap S col i j 2]
  rw [typeCount, card_eq_sum_ones, sum_filter, sum_filter]
  refine sum_congr rfl fun B hB => ?_
  by_cases h2 : cnt col j B = 2
  · obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp (S.card_eq_three B hB)
    have hle : cnt col i {p, q, r} ≤ 1 := by
      have h2' := h2
      rw [cnt_triple col j hpq hpr hqr] at h2'
      rw [cnt_triple col i hpq hpr hqr]
      exact fin3_pattern₂ _ _ _ i j hij h2'
    interval_cases h : cnt col i {p, q, r} <;> simp [h, h2]
  · simp [h2]

/-- **Pair identity** between two classes: `|i| · |j| = 2 N_iij + 2 N_jji`. -/
theorem classSize_mul (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col)
    {i j : Fin 3} (hij : i ≠ j) :
    classSize col i * classSize col j = 2 * typeCount S col i j + 2 * typeCount S col j i := by
  have hsum : ∑ x ∈ univ.filter (fun x => col x = i), classSize col j =
      ∑ x ∈ univ.filter (fun x => col x = i),
        (localCount S col j x + 2 * localCount₂ S col j x) := by
    refine sum_congr rfl fun x hx => ?_
    rw [mem_filter] at hx
    exact classSize_eq_local S col (by rw [hx.2]; exact hij)
  rw [sum_const, smul_eq_mul, sum_add_distrib, ← mul_sum, sum_localCount S col hcol hij,
    sum_localCount₂ S col hij] at hsum
  rw [classSize]
  exact hsum

/-- Blocks through `x` partition the other points of colour `col x`. -/
theorem sum_cnt_erase_through (S : STS V) (col : V → Fin 3) (x : V) :
    ∑ B ∈ S.blocks.filter (fun B => x ∈ B), #((B.erase x).filter fun y => col y = col x) =
      classSize col (col x) - 1 := by
  unfold classSize
  rw [← card_erase_of_mem (s := univ.filter fun v => col v = col x) (a := x) (by simp),
    ← card_biUnion]
  · congr 1
    ext y
    simp only [mem_biUnion, mem_filter, mem_erase, mem_univ, true_and]
    constructor
    · rintro ⟨B, _, ⟨hyx, _⟩, hy⟩
      exact ⟨hyx, hy⟩
    · rintro ⟨hyx, hy⟩
      obtain ⟨B, ⟨hB, hxB, hyB⟩, _⟩ := S.existsUnique_block x y (Ne.symm hyx)
      exact ⟨B, ⟨hB, hxB⟩, ⟨hyx, hyB⟩, hy⟩
  · intro B₁ h₁ B₂ h₂ hne
    simp only [mem_coe, mem_filter] at h₁ h₂
    refine Finset.disjoint_left.mpr fun y hy1 hy2 => ?_
    rw [mem_filter, mem_erase] at hy1 hy2
    obtain ⟨B, _, hu⟩ := S.existsUnique_block x y (Ne.symm hy1.1.1)
    exact hne ((hu B₁ ⟨h₁.1, h₁.2, hy1.1.2⟩).trans (hu B₂ ⟨h₂.1, h₂.2, hy2.1.2⟩).symm)

/-- No colour fills a bicoloured triple. -/
theorem fin3_not_three : ∀ a b c i : Fin 3, ({a, b, c} : Finset (Fin 3)).card = 2 →
    ((if a = i then 1 else 0) + (if b = i then 1 else 0) + (if c = i then 1 else 0) : ℕ) ≠ 3 := by
  decide

/-- The third colour of a bicoloured triple with two points of colour `i`. -/
theorem fin3_third : ∀ a b c i j k : Fin 3, ({a, b, c} : Finset (Fin 3)).card = 2 →
    i ≠ j → i ≠ k → j ≠ k →
    ((if a = i then 1 else 0) + (if b = i then 1 else 0) + (if c = i then 1 else 0) : ℕ) = 2 →
    (((if a = j then 1 else 0) + (if b = j then 1 else 0) + (if c = j then 1 else 0) : ℕ) = 1 ↔
      ¬ ((if a = k then 1 else 0) + (if b = k then 1 else 0) + (if c = k then 1 else 0) : ℕ) = 1) := by
  decide

theorem cnt_ne_three (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col)
    (i : Fin 3) {B : Finset V} (hB : B ∈ S.blocks) : cnt col i B ≠ 3 := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp (S.card_eq_three B hB)
  have himg := hcol _ hB
  simp only [image_insert, image_singleton] at himg
  rw [cnt_triple col i hpq hpr hqr]
  exact fin3_not_three _ _ _ i himg

/-- **Within-class identity**: `|i| (|i| - 1) = 2 (N_iij + N_iik)` for distinct `i, j, k`. -/
theorem classSize_choose (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    classSize col i * (classSize col i - 1) =
      2 * (typeCount S col i j + typeCount S col i k) := by
  -- per vertex: `|i| - 1` = blocks through `x` with two points of colour `i`
  have hloc : ∀ x, col x = i →
      classSize col i - 1 = #(S.blocks.filter fun B => x ∈ B ∧ cnt col i B = 2) := by
    intro x hx
    have hE := sum_cnt_erase_through S col x
    rw [hx] at hE
    rw [← hE, card_filter, sum_filter]
    refine sum_congr rfl fun B hB => ?_
    by_cases hxB : x ∈ B
    · have hcard : #((B.erase x).filter fun y => col y = i) = cnt col i B - 1 := by
        rw [filter_erase, card_erase_of_mem (mem_filter.mpr ⟨hxB, hx⟩), cnt]
      have hpos : 1 ≤ cnt col i B := card_pos.mpr ⟨x, mem_filter.mpr ⟨hxB, hx⟩⟩
      have hle : cnt col i B ≤ 3 := by
        have := card_filter_le B (fun y => col y = i)
        rw [S.card_eq_three B hB] at this
        exact this
      have h3 := cnt_ne_three S col hcol i hB
      rw [if_pos hxB, hcard]
      by_cases h2 : cnt col i B = 2
      · simp [h2, hxB]
      · simp only [h2, and_false, if_false]; omega
    · simp [hxB]
  have hsum : ∑ x ∈ univ.filter (fun x => col x = i), (classSize col i - 1) =
      ∑ B ∈ S.blocks.filter (fun B => cnt col i B = 2), cnt col i B := by
    rw [← sum_local_swap S col i i 2]
    refine sum_congr rfl fun x hx => ?_
    exact hloc x (mem_filter.mp hx).2
  rw [sum_const, smul_eq_mul, sum_congr rfl (fun B hB => (mem_filter.mp hB).2), sum_const,
    smul_eq_mul] at hsum
  -- split the blocks with two points of colour `i` by their third colour
  have hsplit : #(S.blocks.filter fun B => cnt col i B = 2) =
      typeCount S col i j + typeCount S col i k := by
    rw [typeCount, typeCount, ← filter_filter, ← filter_filter,
      ← card_filter_add_card_filter_not (s := S.blocks.filter fun B => cnt col i B = 2)
        (p := fun B => cnt col j B = 1)]
    congr 1
    refine congrArg card (filter_congr fun B hB => ?_)
    rw [mem_filter] at hB
    obtain ⟨p, q, r, hpq, hpr, hqr, hBe⟩ := card_eq_three.mp (S.card_eq_three B hB.1)
    have himg := hcol _ hB.1
    rw [hBe] at himg hB ⊢
    simp only [image_insert, image_singleton] at himg
    have h2 := hB.2
    rw [cnt_triple col i hpq hpr hqr] at h2
    rw [cnt_triple col j hpq hpr hqr, cnt_triple col k hpq hpr hqr]
    exact (fin3_third _ _ _ i j k himg hij hik hjk h2).not.trans not_not
  rw [classSize] at hsum ⊢
  rw [hsum, ← hsplit, mul_comm]

/-- **Lower bound**: if `|class j|` is odd, then `|class i| ≤ 2 · typeCount i j`. -/
theorem typeCount_lower (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col)
    {i j : Fin 3} (hij : i ≠ j) (hodd : classSize col j % 2 = 1) :
    classSize col i ≤ 2 * typeCount S col i j := by
  rw [← sum_localCount S col hcol hij, classSize, card_eq_sum_ones]
  refine sum_le_sum fun x hx => ?_
  rw [mem_filter] at hx
  have := localCount_mod_two S col (x := x) (j := j) (by rw [hx.2]; exact hij)
  omega

/-- For a realised profile whose class `C` (colour `2`) is odd:
`a ≤ 2 N_AAC` and `b ≤ 2 N_BBC`. -/
theorem realised_lower_C_odd {a b c : ℕ} (S : STS (Fin (a + b + c)))
    (col : Fin (a + b + c) → Fin 3) (hcol : IsStrictBicolouring S col)
    (ha : classSize col 0 = a) (hb : classSize col 1 = b) (hc : classSize col 2 = c)
    (hodd : c % 2 = 1) :
    a ≤ 2 * typeCount S col 0 2 ∧ b ≤ 2 * typeCount S col 1 2 := by
  have hc' : classSize col 2 % 2 = 1 := by rw [hc]; exact hodd
  have h0 := typeCount_lower S col hcol (i := 0) (j := 2) (by decide) hc'
  have h1 := typeCount_lower S col hcol (i := 1) (j := 2) (by decide) hc'
  omega

/-- **The six pair identities** of a realised profile.  Writing `N i j = typeCount S col i j`
(blocks `iij`), the pairs inside each class and between each two classes are counted:
`a(a-1) = 2(N₀₁+N₀₂)`, `b(b-1) = 2(N₁₀+N₁₂)`, `c(c-1) = 2(N₂₀+N₂₁)`,
`ab = 2(N₀₁+N₁₀)`, `ac = 2(N₀₂+N₂₀)`, `bc = 2(N₁₂+N₂₁)`.  With the admissibility identity
they leave one free parameter, e.g. `t = N₀₂` (blocks `AAC`). -/
theorem realised_type_identities {a b c : ℕ} (S : STS (Fin (a + b + c)))
    (col : Fin (a + b + c) → Fin 3) (hcol : IsStrictBicolouring S col)
    (ha : classSize col 0 = a) (hb : classSize col 1 = b) (hc : classSize col 2 = c) :
    let N := typeCount S col
    a * (a - 1) = 2 * (N 0 1 + N 0 2) ∧ b * (b - 1) = 2 * (N 1 0 + N 1 2) ∧
    c * (c - 1) = 2 * (N 2 0 + N 2 1) ∧
    a * b = 2 * N 0 1 + 2 * N 1 0 ∧ a * c = 2 * N 0 2 + 2 * N 2 0 ∧
    b * c = 2 * N 1 2 + 2 * N 2 1 := by
  intro N
  have e1 := classSize_choose S col hcol (i := 0) (j := 1) (k := 2) (by decide) (by decide)
    (by decide)
  have e2 := classSize_choose S col hcol (i := 1) (j := 0) (k := 2) (by decide) (by decide)
    (by decide)
  have e3 := classSize_choose S col hcol (i := 2) (j := 0) (k := 1) (by decide) (by decide)
    (by decide)
  have e4 := classSize_mul S col hcol (i := 0) (j := 1) (by decide)
  have e5 := classSize_mul S col hcol (i := 0) (j := 2) (by decide)
  have e6 := classSize_mul S col hcol (i := 1) (j := 2) (by decide)
  rw [ha] at e1 e4 e5
  rw [hb] at e2 e4 e6
  rw [hc] at e3 e5 e6
  exact ⟨e1, e2, e3, e4, e5, e6⟩

end CDRBicolour.BlockTypes
