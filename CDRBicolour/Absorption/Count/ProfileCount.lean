/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Completion
public import CountingCone.VanDerWaerden.Full
public import CountingCone.LL.STSMain

/-!
# Counting the realisations of a profile (backlog item 4)

`realCount a b c`: the number of Steiner triple systems on `Fin (a+b+c)` strictly bicoloured by
the interval colouring `col3 a b c` (classes of sizes `a, b, c`).

* **Upper bound** (`realCount_le`): `realCount ≤ D(n)`, so Linial–Luria (Palomar
  PALOMAR-2026-10-22-000017) gives `log realCount ≤ (n(n−1)/6)(log n − 2 + 1200/√(n−3))`.
* **Lower bound** (`realCount_lower`): `log realCount ≥ c n² log n` for an absolute `c > 0`.
  A Latin square `l` of order `m ≈ λ n` gives the sparse packing of `AAB` triangles
  `{r_i, c_j, s_{l i j}}` (rows and columns in `A`, symbols in `B`); item 2a completes it to a
  realisation; a realisation contains at most `2^{n²}` such packings; and
  `log L(m) ≥ m² (log m − 2)` (van der Waerden, same Palomar entry).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

variable {a b c : ℕ}

open Classical in
/-- The block sets of the realisations of the profile `(a, b, c)`. -/
def realBlocks (a b c : ℕ) : Finset (Finset (Finset (Fin (a + b + c)))) :=
  univ.filter fun X => _root_.STS.IsSTS X ∧ ∀ B ∈ X, (B.image (col3 a b c)).card = 2

/-- **Number of realisations of a profile.** -/
def realCount (a b c : ℕ) : ℕ := #(realBlocks a b c)

theorem mem_realBlocks_of (S : CDRBicolour.STS (Fin (a + b + c)))
    (hS : IsStrictBicolouring S (col3 a b c)) : S.blocks ∈ realBlocks a b c := by
  classical
  unfold realBlocks
  rw [mem_filter]
  exact ⟨mem_univ _, ⟨S.card_eq_three, S.existsUnique_block⟩, hS⟩

/-- `realCount ≤ D(n)`. -/
theorem realCount_le : realCount a b c ≤ _root_.STS.D (a + b + c) := by
  classical
  unfold realCount _root_.STS.D
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_le_card fun X hX => by
    simp only [realBlocks, mem_filter, mem_univ, true_and] at hX ⊢; exact hX.1

/-- **Upper bound** (Linial–Luria, explicit). -/
theorem realCount_upper (hn : 4 ≤ a + b + c) :
    (realCount a b c : ℝ) ≤ Real.exp (((a + b + c : ℕ) * ((a + b + c : ℕ) - 1) / 6 : ℝ) *
      (Real.log (a + b + c : ℕ) - 2 + 1200 / Real.sqrt (((a + b + c : ℕ) : ℝ) - 3))) :=
  (Nat.cast_le.mpr realCount_le).trans (LinialLuria.sts_upper_bound_explicit _ hn)

/-! ### A Steiner triple system has at most `n²` blocks -/

theorem card_sts_blocks_le {X : Finset (Finset (Fin (a + b + c)))} (hX : _root_.STS.IsSTS X) :
    #X ≤ (a + b + c) ^ 2 := by
  classical
  -- each block contains an ordered pair of distinct points; the pair determines the block
  have hpair : ∀ B ∈ X, ∃ p : Fin (a + b + c) × Fin (a + b + c), p.1 ≠ p.2 ∧ p.1 ∈ B ∧ p.2 ∈ B := by
    intro B hB
    obtain ⟨x, y, z, hxy, -, -, rfl⟩ := card_eq_three.mp (hX.1 B hB)
    exact ⟨(x, y), hxy, by simp, by simp⟩
  rcases X.eq_empty_or_nonempty with rfl | ⟨B₀, hB₀⟩
  · simp
  obtain ⟨x₀, -⟩ := card_pos.mp (by rw [hX.1 B₀ hB₀]; norm_num : 0 < B₀.card)
  haveI : Nonempty (Fin (a + b + c) × Fin (a + b + c)) := ⟨(x₀, x₀)⟩
  choose! f hf using hpair
  have hinj : Set.InjOn f X := by
    intro B hB B' hB' he
    obtain ⟨h1, h2, h3⟩ := hf B hB
    obtain ⟨-, h2', h3'⟩ := hf B' hB'
    rw [he] at h2 h3
    obtain ⟨C, -, hC⟩ := hX.2 _ _ (he ▸ h1)
    exact (hC B ⟨hB, he ▸ h2, he ▸ h3⟩).trans (hC B' ⟨hB', h2', h3'⟩).symm
  calc #X = #(X.image f) := (card_image_of_injOn hinj).symm
    _ ≤ #(univ : Finset (Fin (a + b + c) × Fin (a + b + c))) := card_le_univ _
    _ = (a + b + c) ^ 2 := by simp [sq]

/-! ### Latin squares give sparse packings -/

/-- Row `i`, column `j` (both in class `A`) and symbol `k` (class `B`). -/
def rowV (m : ℕ) (h : 2 * m ≤ a) (i : Fin m) : Fin (a + b + c) := ⟨i.val, by omega⟩
def colV (m : ℕ) (h : 2 * m ≤ a) (j : Fin m) : Fin (a + b + c) := ⟨m + j.val, by omega⟩
def symV (m : ℕ) (h : m ≤ b) (k : Fin m) : Fin (a + b + c) := ⟨a + k.val, by omega⟩

/-- The packing of a Latin square. -/
def latPack (m : ℕ) (ha : 2 * m ≤ a) (hb : m ≤ b) (l : Fin m → Fin m → Fin m) :
    Finset (Finset (Fin (a + b + c))) :=
  (univ : Finset (Fin m × Fin m)).image fun p =>
    {rowV m ha p.1, colV m ha p.2, symV m hb (l p.1 p.2)}

section Lat

variable {m : ℕ} (ha : 2 * m ≤ a) (hb : m ≤ b)

theorem rc_ne (i j : Fin m) : rowV m ha i ≠ colV (a := a) (b := b) (c := c) m ha j := by
  intro h; have := congrArg Fin.val h; simp [rowV, colV] at this; omega

theorem rs_ne (i : Fin m) (k : Fin m) : rowV m ha i ≠ symV (a := a) (b := b) (c := c) m hb k := by
  intro h; have := congrArg Fin.val h; simp [rowV, symV] at this; omega

theorem cs_ne (j : Fin m) (k : Fin m) : colV m ha j ≠ symV (a := a) (b := b) (c := c) m hb k := by
  intro h; have := congrArg Fin.val h; simp [colV, symV] at this; omega

theorem rowV_inj : Function.Injective (rowV (a := a) (b := b) (c := c) m ha) := by
  intro i i' h; have := congrArg Fin.val h; simp [rowV] at this; exact Fin.ext this

theorem colV_inj : Function.Injective (colV (a := a) (b := b) (c := c) m ha) := by
  intro i i' h; have := congrArg Fin.val h; simp [colV] at this; exact Fin.ext this

theorem symV_inj : Function.Injective (symV (a := a) (b := b) (c := c) m hb) := by
  intro i i' h; have := congrArg Fin.val h; simp [symV] at this; exact Fin.ext this

theorem col3_rowV (i : Fin m) : col3 a b c (rowV m ha i) = 0 := by
  unfold col3 rowV; simp; omega

theorem col3_colV (j : Fin m) : col3 a b c (colV m ha j) = 0 := by
  unfold col3 colV; simp; omega

theorem col3_symV (k : Fin m) : col3 a b c (symV m hb k) = 1 := by
  unfold col3 symV
  have := k.isLt
  simp only [show ¬ a + k.val < a by omega, if_false, show a + k.val < a + b by omega, if_true]

theorem latPack_allowed (l : Fin m → Fin m → Fin m) :
    ∀ T ∈ latPack m ha hb l, IsAllowed (cdrHost a b c) cdrF T := by
  intro T hT
  obtain ⟨⟨i, j⟩, -, rfl⟩ := mem_image.mp hT
  refine isAllowed_triple (col3 a b c) (rc_ne ha i j) (rs_ne ha hb i _) (cs_ne ha hb j _) ?_
  rw [col3_rowV, col3_colV, col3_symV]
  exact ⟨rfl, by decide⟩

/-- Membership in a placed triangle. -/
theorem mem_tri_iff {i j : Fin m} {k : Fin m} {i' j' : Fin m} {k' : Fin m}
    (he : ({rowV m ha i, colV m ha j, symV m hb k} : Finset (Fin (a + b + c))) =
      {rowV m ha i', colV m ha j', symV m hb k'}) : i = i' ∧ j = j' ∧ k = k' := by
  have h1 : rowV m ha i ∈ ({rowV m ha i', colV m ha j', symV m hb k'} : Finset (Fin (a + b + c))) := by
    rw [← he]; simp
  have h2 : colV m ha j ∈ ({rowV m ha i', colV m ha j', symV m hb k'} : Finset (Fin (a + b + c))) := by
    rw [← he]; simp
  have h3 : symV m hb k ∈ ({rowV m ha i', colV m ha j', symV m hb k'} : Finset (Fin (a + b + c))) := by
    rw [← he]; simp
  simp only [mem_insert, mem_singleton] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · rcases h1 with h | h | h
    · exact rowV_inj ha h
    · exact absurd h (rc_ne ha i j')
    · exact absurd h (rs_ne ha hb i k')
  · rcases h2 with h | h | h
    · exact absurd h.symm (rc_ne ha i' j)
    · exact colV_inj ha h
    · exact absurd h (cs_ne ha hb j k')
  · rcases h3 with h | h | h
    · exact absurd h.symm (rs_ne ha hb i' k)
    · exact absurd h.symm (cs_ne ha hb j' k)
    · exact symV_inj hb h

theorem latPack_injective : Function.Injective (latPack (a := a) (b := b) (c := c) m ha hb) := by
  intro l l' he
  funext i j
  have : ({rowV m ha i, colV m ha j, symV m hb (l i j)} : Finset (Fin (a + b + c))) ∈
      latPack m ha hb l' := by rw [← he]; exact mem_image.mpr ⟨(i, j), mem_univ _, rfl⟩
  obtain ⟨⟨i', j'⟩, -, h⟩ := mem_image.mp this
  obtain ⟨rfl, rfl, hk⟩ := mem_tri_iff ha hb h
  exact hk.symm

end Lat

section Lat2

variable {m : ℕ} (ha : 2 * m ≤ a) (hb : m ≤ b)

/-- A point lying in two placed triangles is of the same kind in both, with the same index. -/
theorem vtype {u : Fin (a + b + c)} {i j k i' j' k' : Fin m}
    (h1 : u ∈ ({rowV m ha i, colV m ha j, symV m hb k} : Finset (Fin (a + b + c))))
    (h2 : u ∈ ({rowV m ha i', colV m ha j', symV m hb k'} : Finset (Fin (a + b + c)))) :
    (u = rowV m ha i ∧ i = i') ∨ (u = colV m ha j ∧ j = j') ∨ (u = symV m hb k ∧ k = k') := by
  simp only [mem_insert, mem_singleton] at h1 h2
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with h | h | h
  · exact Or.inl ⟨rfl, rowV_inj ha h⟩
  · exact absurd h (rc_ne ha i j')
  · exact absurd h (rs_ne ha hb i k')
  · exact absurd h.symm (rc_ne ha i' j)
  · exact Or.inr (Or.inl ⟨rfl, colV_inj ha h⟩)
  · exact absurd h (cs_ne ha hb j k')
  · exact absurd h.symm (rs_ne ha hb i' k)
  · exact absurd h.symm (cs_ne ha hb j' k)
  · exact Or.inr (Or.inr ⟨rfl, symV_inj hb h⟩)

theorem latPack_disj {l : Fin m → Fin m → Fin m} (hl : _root_.STS.IsLatin l) :
    ((latPack m ha hb l : Finset (Finset (Fin (a + b + c)))) :
      Set (Finset (Fin (a + b + c)))).PairwiseDisjoint triEdges := by
  intro T hT T' hT' hne
  simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range, latPack] at hT hT'
  obtain ⟨⟨i, j⟩, rfl⟩ := hT
  obtain ⟨⟨i', j'⟩, rfl⟩ := hT'
  show Disjoint (triEdges _) (triEdges _)
  rw [Finset.disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | _ u v =>
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he he'
  obtain ⟨⟨hu, hv⟩, huv⟩ := he
  obtain ⟨⟨hu', hv'⟩, -⟩ := he'
  apply hne
  have key : i = i' ∧ j = j' := by
    rcases vtype ha hb hu hu' with ⟨eu, h1⟩ | ⟨eu, h1⟩ | ⟨eu, h1⟩ <;>
    rcases vtype ha hb hv hv' with ⟨ev, h2⟩ | ⟨ev, h2⟩ | ⟨ev, h2⟩
    · exact absurd (eu.trans ev.symm) huv
    · exact ⟨h1, h2⟩
    · exact ⟨h1, (hl.1 i).1 (by rw [← h1] at h2; exact h2)⟩
    · exact ⟨h2, h1⟩
    · exact absurd (eu.trans ev.symm) huv
    · exact ⟨(hl.2 j).1 (by rw [← h1] at h2; exact h2), h1⟩
    · exact ⟨h2, (hl.1 i).1 (by rw [← h2] at h1; exact h1)⟩
    · exact ⟨(hl.2 j).1 (by rw [← h2] at h1; exact h1), h2⟩
    · exact absurd (eu.trans ev.symm) huv
  obtain ⟨rfl, rfl⟩ := key
  rfl

/-- Leave degree of a Latin packing. -/
theorem latPack_deg {l : Fin m → Fin m → Fin m} (hl : _root_.STS.IsLatin l)
    (v : Fin (a + b + c)) : degL ((latPack m ha hb l).biUnion triEdges) v ≤ 9 * m := by
  classical
  set cell : Fin m × Fin m → Finset (Fin (a + b + c)) :=
    fun p => {rowV m ha p.1, colV m ha p.2, symV m hb (l p.1 p.2)}
  set I := (univ : Finset (Fin m × Fin m)).filter fun p => v ∈ cell p
  have hsub : nbL ((latPack m ha hb l).biUnion triEdges) v ⊆ I.biUnion cell := by
    intro w hw
    simp only [nbL, mem_filter, mem_univ, true_and, mem_biUnion, latPack, mem_image] at hw
    obtain ⟨T, ⟨p, -, rfl⟩, he⟩ := hw
    simp only [triEdges, mem_filter, mk_mem_sym2_iff] at he
    exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, he.1.2⟩, he.1.1⟩
  have hI : #I ≤ 3 * m := by
    have h3 : I ⊆ (univ.filter fun p : Fin m × Fin m => rowV m ha p.1 = v) ∪
        (univ.filter fun p : Fin m × Fin m => colV m ha p.2 = v) ∪
        (univ.filter fun p : Fin m × Fin m => symV m hb (l p.1 p.2) = v) := by
      intro p hp
      simp only [I, cell, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hp
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases hp with h | h | h
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h.symm
    have c1 : #(univ.filter fun p : Fin m × Fin m => rowV m ha p.1 = v) ≤ m := by
      refine (card_le_card_of_injOn (fun p => p.2) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_).trans
        (by simp)
      intro p hp q hq he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      exact Prod.ext (rowV_inj ha (hp.trans hq.symm)) he
    have c2 : #(univ.filter fun p : Fin m × Fin m => colV m ha p.2 = v) ≤ m := by
      refine (card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_).trans
        (by simp)
      intro p hp q hq he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      exact Prod.ext he (colV_inj ha (hp.trans hq.symm))
    have c3 : #(univ.filter fun p : Fin m × Fin m => symV m hb (l p.1 p.2) = v) ≤ m := by
      refine (card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_).trans
        (by simp)
      intro p hp q hq he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      have hpq := symV_inj hb (hp.trans hq.symm)
      simp only at he
      rw [he] at hpq
      exact Prod.ext he ((hl.1 q.1).1 hpq)
    calc #I ≤ _ := card_le_card h3
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ m + m + m := add_le_add (add_le_add c1 c2) c3
      _ = 3 * m := by ring
  calc degL ((latPack m ha hb l).biUnion triEdges) v ≤ #(I.biUnion cell) := card_le_card hsub
    _ ≤ ∑ p ∈ I, #(cell p) := card_biUnion_le
    _ ≤ ∑ _p ∈ I, 3 := by gcongr; exact card_le_three
    _ = 3 * #I := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ 9 * m := by omega

end Lat2

/-! ### The lower bound -/

open Classical in
/-- `L(m) ≤ 2^{n²} · realCount` for Latin packings that complete. -/
theorem latin_le_realCount {m : ℕ} (ha : 2 * m ≤ a) (hb : m ≤ b)
    (hcomp : ∀ l : Fin m → Fin m → Fin m, _root_.STS.IsLatin l →
      ∃ S : CDRBicolour.STS (Fin (a + b + c)), latPack m ha hb l ⊆ S.blocks ∧
        IsStrictBicolouring S (col3 a b c)) :
    _root_.STS.L m ≤ 2 ^ ((a + b + c) ^ 2) * realCount a b c := by
  set Lat := (univ : Finset (Fin m → Fin m → Fin m)).filter _root_.STS.IsLatin
  have hL : _root_.STS.L m = #Lat := by
    unfold _root_.STS.L; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set f : (Fin m → Fin m → Fin m) → Finset (Finset (Fin (a + b + c))) := fun l =>
    if hl : _root_.STS.IsLatin l then (Classical.choose (hcomp l hl)).blocks else ∅
  have hf : ∀ l ∈ Lat, latPack m ha hb l ⊆ f l ∧ f l ∈ realBlocks a b c := by
    intro l hl
    have hl' := (mem_filter.mp hl).2
    have hs := Classical.choose_spec (hcomp l hl')
    simp only [f, dif_pos hl']
    exact ⟨hs.1, mem_realBlocks_of _ hs.2⟩
  have hfib : ∀ X ∈ Lat.image f, #(Lat.filter fun l => f l = X) ≤ 2 ^ ((a + b + c) ^ 2) := by
    intro X hX
    obtain ⟨l₀, hl₀, rfl⟩ := mem_image.mp hX
    have hXr := (hf l₀ hl₀).2
    have hXsts : _root_.STS.IsSTS (f l₀) := (mem_filter.mp hXr).2.1
    calc #(Lat.filter fun l => f l = f l₀) ≤ #(f l₀).powerset := by
          refine card_le_card_of_injOn (latPack m ha hb) (fun l hl => ?_)
            (fun l _ l' _ he => latPack_injective ha hb he)
          simp only [coe_filter, Set.mem_ofPred_eq] at hl
          rw [mem_coe, mem_powerset, ← hl.2]
          exact (hf l hl.1).1
      _ = 2 ^ #(f l₀) := card_powerset _
      _ ≤ 2 ^ ((a + b + c) ^ 2) := Nat.pow_le_pow_right (by norm_num) (card_sts_blocks_le hXsts)
  rw [hL]
  calc #Lat ≤ 2 ^ ((a + b + c) ^ 2) * #(Lat.image f) := card_le_mul_card_image Lat _ hfib
    _ ≤ 2 ^ ((a + b + c) ^ 2) * realCount a b c := by
        gcongr
        exact card_le_card fun X hX => by
          obtain ⟨l, hl, rfl⟩ := mem_image.mp hX; exact (hf l hl).2

set_option maxHeartbeats 2000000 in
/-- **Lower bound for the number of realisations** (`c = λ²/16`, `λ = 1/(9 · 6656000)`). -/
theorem realCount_lower :
    ∃ cst : ℝ, 0 < cst ∧ ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      cst * ((a + b + c : ℕ) : ℝ) ^ 2 * Real.log (a + b + c : ℕ) ≤
        Real.log (realCount a b c) := by
  obtain ⟨nC, hC⟩ := cdr_completion
  set lam : ℝ := 1 / (9 * 6656000) with hlam
  have hlam0 : 0 < lam := by positivity
  set K₀ : ℝ := Real.log 2 - lam ^ 2 / 4 * (Real.log (lam / 2) - 2) with hK₀
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, Real.exp (16 * |K₀| / (3 * lam ^ 2)) ≤ N1 := exists_nat_ge _
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, 64 / lam ≤ N2 := exists_nat_ge _
  refine ⟨lam ^ 2 / 16, by positivity, max nC (max 400 (max N1 N2)), fun a b c h hn => ?_⟩
  have hnC : nC ≤ a + b + c := le_of_max_le_left hn
  have h400 : 400 ≤ a + b + c := le_trans (le_max_left _ _) (le_of_max_le_right hn)
  have hN1n : N1 ≤ a + b + c :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_max_le_right hn)
  have hN2n : N2 ≤ a + b + c :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_max_le_right hn)
  set N : ℝ := ((a + b + c : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by simp only [hN]; exact_mod_cast (show 0 < a + b + c by omega)
  have hlamN : 64 ≤ lam * N := by
    have : 64 / lam ≤ N := hN2.trans (by simp only [hN]; exact_mod_cast hN2n)
    rw [div_le_iff₀ hlam0] at this; linarith
  set m : ℕ := ⌊lam * N⌋₊ with hm
  have hm1 : lam * N - 1 < m := Nat.sub_one_lt_floor _
  have hm2 : (m : ℝ) ≤ lam * N := Nat.floor_le (by positivity)
  clear_value m K₀ N lam
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  have haR : N + 8 ≤ 4 * (a : ℝ) := by simp only [hN]; exact_mod_cast ha4
  have hbR : N + 8 ≤ 4 * (b : ℝ) := by simp only [hN]; exact_mod_cast hb4
  have hlsmall : lam ≤ 1 / 8 := by rw [hlam]; norm_num
  have hlN : lam * N ≤ N / 8 := by nlinarith
  have ha : 2 * m ≤ a := by
    have : (2 * m : ℝ) ≤ a := by linarith
    exact_mod_cast this
  have hb : m ≤ b := by
    have : (m : ℝ) ≤ b := by linarith
    exact_mod_cast this
  have hdegN : 6656000 * (9 * m) ≤ a + b + c := by
    have : (6656000 * (9 * m) : ℝ) ≤ N := by
      have : (6656000 * 9 : ℝ) * lam = 1 := by rw [hlam]; norm_num
      nlinarith
    simp only [hN] at this; exact_mod_cast this
  -- every Latin packing completes
  have hcomp : ∀ l : Fin m → Fin m → Fin m, _root_.STS.IsLatin l →
      ∃ S : CDRBicolour.STS (Fin (a + b + c)), latPack m ha hb l ⊆ S.blocks ∧
        IsStrictBicolouring S (col3 a b c) := by
    intro l hl
    obtain ⟨S, hS, hcol, -⟩ := hC a b c h hnC (latPack m ha hb l) (9 * m)
      (latPack_allowed ha hb l) (latPack_disj ha hb hl) (latPack_deg ha hb hl) hdegN
    exact ⟨S, hS, hcol⟩
  have hLm := latin_le_realCount ha hb hcomp
  -- logarithms
  have hm8 : (8 : ℝ) ≤ m := by linarith
  have hmpos : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hlogL := _root_.STS.hL_one _root_.STS.van_der_waerden m hmpos
  have hLpos : (0 : ℝ) < _root_.STS.L m := by
    by_contra hz
    push_neg at hz
    have h0 : (_root_.STS.L m : ℝ) = 0 := le_antisymm hz (Nat.cast_nonneg _)
    rw [h0, Real.log_zero] at hlogL
    have : (2 : ℝ) < Real.log m := by
      have h82 : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          _ < 2.7182818286 * 2.7182818286 := by gcongr
          _ < 8 := by norm_num
      rw [Real.lt_log_iff_exp_lt (by linarith)]; linarith
    have hp : 0 < (m : ℝ) ^ 2 * (Real.log m - 2) := mul_pos (by positivity) (by linarith)
    linarith
  have hRpos : (0 : ℝ) < realCount a b c := by
    have hle : (_root_.STS.L m : ℝ) ≤ 2 ^ ((a + b + c) ^ 2) * realCount a b c := by exact_mod_cast hLm
    by_contra hz; push_neg at hz
    have h0 : (realCount a b c : ℝ) = 0 := le_antisymm hz (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hle
    linarith
  have hlogR : Real.log (_root_.STS.L m) ≤ N ^ 2 * Real.log 2 + Real.log (realCount a b c) := by
    have h1 : (_root_.STS.L m : ℝ) ≤ 2 ^ ((a + b + c) ^ 2) * realCount a b c := by exact_mod_cast hLm
    have h2 := Real.log_le_log hLpos h1
    rw [Real.log_mul (by positivity) hRpos.ne', Real.log_pow] at h2
    simp only [hN]; push_cast at h2 ⊢; linarith
  -- `log m ≥ log N + log (λ/2)` and `m² ≥ λ² N² / 4`
  have hmhalf : lam * N / 2 ≤ m := by linarith
  have hlogm : Real.log N + Real.log (lam / 2) ≤ Real.log m := by
    rw [← Real.log_mul hN0.ne' (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hm2sq : lam ^ 2 * N ^ 2 / 4 ≤ (m : ℝ) ^ 2 := by nlinarith
  have hlogm2 : 2 ≤ Real.log m := by
    have h82 : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ < 2.7182818286 * 2.7182818286 := by gcongr
        _ < 8 := by norm_num
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith)
  have hlogN : 16 * |K₀| / (3 * lam ^ 2) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hN1.trans (by simp only [hN]; exact_mod_cast hN1n)
  have hlogN0 : 0 ≤ Real.log N := le_trans (by positivity) hlogN
  have hmain : lam ^ 2 * N ^ 2 / 4 * (Real.log N + Real.log (lam / 2) - 2) ≤
      (m : ℝ) ^ 2 * (Real.log m - 2) := by
    have hA : 0 ≤ Real.log m - 2 := by linarith
    calc lam ^ 2 * N ^ 2 / 4 * (Real.log N + Real.log (lam / 2) - 2)
        ≤ lam ^ 2 * N ^ 2 / 4 * (Real.log m - 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (m : ℝ) ^ 2 * (Real.log m - 2) := mul_le_mul_of_nonneg_right hm2sq hA
  have hK : K₀ ≤ 3 * lam ^ 2 / 16 * Real.log N := by
    have h1 : K₀ ≤ |K₀| := le_abs_self _
    have h2 : 16 * |K₀| ≤ 3 * lam ^ 2 * Real.log N := by
      rw [div_le_iff₀ (by positivity)] at hlogN; linarith
    nlinarith
  have hfin : lam ^ 2 / 16 * N ^ 2 * Real.log N ≤
      lam ^ 2 * N ^ 2 / 4 * (Real.log N + Real.log (lam / 2) - 2) - N ^ 2 * Real.log 2 := by
    have hN2 : 0 ≤ N ^ 2 := by positivity
    have : lam ^ 2 / 16 * Real.log N ≤
        lam ^ 2 / 4 * (Real.log N + Real.log (lam / 2) - 2) - Real.log 2 := by
      rw [hK₀] at hK; linarith
    nlinarith
  simp only [hN] at hlogL hmain hfin hlogR ⊢
  linarith

end CDRBicolour.Absorption.Count
