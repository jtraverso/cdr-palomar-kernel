/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Completion

/-!
# Counting `k`-bicoloured Steiner triple systems

**`kbicolour_count`**: for `k ≥ 3`, `0 < δ ≤ 1`, `η > 0` and `ε > 0` there are `c > 0` and `n₀`
such that every admissible labelling of `n ≥ n₀` points with classes `≥ δ n` and seed data
`a ≥ η` has

    c n² log n ≤ log kCount(lab) ≤ (1/6 + ε) n² log n.

* Upper bound: Linial–Luria (`kCount_upper`).
* Lower bound: a Latin square `l` of order `m ≈ λ n` gives the packing of triangles
  `{r_i, c_j, s_{l(i,j)}}` (rows and columns in a class `X`, symbols in a class `Y`); it completes
  (`kbicolour_completion`); a system contains at most `2^{n²}` such packings; van der Waerden
  gives `log L(m) ≥ m² (log m − 2)`.

The sharp lower constant `1/6` for `k = 3` uses Wilson's construction with the class pattern
`τ = [[B,A,C],[A,C,B],[C,B,A]]`; for `k ≥ 4` there is no Latin pattern `τ` with
`τ(P,Q) ∈ {P,Q}` for `P ≠ Q` and `τ(P,P) ≠ P`, so the sharp constant needs another construction.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption

variable {k n : ℕ}

/-! ### Latin packings -/

/-- Rows `r`, columns `c` (class `X`) and symbols `s` (class `Y`). -/
structure LatPlace (lab : Fin n → Fin k) (X Y : Fin k) {m : ℕ} (r c s : Fin m → Fin n) : Prop where
  rinj : Function.Injective r
  cinj : Function.Injective c
  sinj : Function.Injective s
  rc : ∀ i j, r i ≠ c j
  lr : ∀ i, lab (r i) = X
  lc : ∀ j, lab (c j) = X
  ls : ∀ q, lab (s q) = Y
  hXY : X ≠ Y

/-- The packing of a Latin square. -/
def latPackK {m : ℕ} (r c s : Fin m → Fin n) (l : Fin m → Fin m → Fin m) :
    Finset (Finset (Fin n)) :=
  (univ : Finset (Fin m × Fin m)).image fun p => {r p.1, c p.2, s (l p.1 p.2)}

section Lat

variable {lab : Fin n → Fin k} {X Y : Fin k} {m : ℕ} {r c s : Fin m → Fin n}
  (h : LatPlace lab X Y r c s)
include h

theorem LatPlace.rs (i q : Fin m) : r i ≠ s q := fun e => h.hXY (by rw [← h.lr i, ← h.ls q, e])

theorem LatPlace.cs (j q : Fin m) : c j ≠ s q := fun e => h.hXY (by rw [← h.lc j, ← h.ls q, e])

theorem latPackK_allowed (l : Fin m → Fin m → Fin m) :
    ∀ T ∈ latPackK r c s l, IsAllowed (kHost lab) (bicF k) T := by
  intro T hT
  obtain ⟨⟨i, j⟩, -, rfl⟩ := mem_image.mp hT
  refine isAllowed_triple lab (h.rc i j) (h.rs i _) (h.cs j _) ?_
  rw [h.lr, h.lc, h.ls]
  exact xxy_mem_bicF h.hXY

theorem mem_tri_iffK {i j q i' j' q' : Fin m}
    (he : ({r i, c j, s q} : Finset (Fin n)) = {r i', c j', s q'}) :
    i = i' ∧ j = j' ∧ q = q' := by
  have h1 : r i ∈ ({r i', c j', s q'} : Finset (Fin n)) := by rw [← he]; simp
  have h2 : c j ∈ ({r i', c j', s q'} : Finset (Fin n)) := by rw [← he]; simp
  have h3 : s q ∈ ({r i', c j', s q'} : Finset (Fin n)) := by rw [← he]; simp
  simp only [mem_insert, mem_singleton] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · rcases h1 with e | e | e
    · exact h.rinj e
    · exact absurd e (h.rc i j')
    · exact absurd e (h.rs i q')
  · rcases h2 with e | e | e
    · exact absurd e.symm (h.rc i' j)
    · exact h.cinj e
    · exact absurd e (h.cs j q')
  · rcases h3 with e | e | e
    · exact absurd e.symm (h.rs i' q)
    · exact absurd e.symm (h.cs j' q)
    · exact h.sinj e

theorem latPackK_injective : Function.Injective (latPackK r c s) := by
  intro l l' he
  funext i j
  have : ({r i, c j, s (l i j)} : Finset (Fin n)) ∈ latPackK r c s l' := by
    rw [← he]; exact mem_image.mpr ⟨(i, j), mem_univ _, rfl⟩
  obtain ⟨⟨i', j'⟩, -, e⟩ := mem_image.mp this
  obtain ⟨rfl, rfl, hq⟩ := mem_tri_iffK h e
  exact hq.symm

theorem vtypeK {u : Fin n} {i j q i' j' q' : Fin m}
    (h1 : u ∈ ({r i, c j, s q} : Finset (Fin n))) (h2 : u ∈ ({r i', c j', s q'} : Finset (Fin n))) :
    (u = r i ∧ i = i') ∨ (u = c j ∧ j = j') ∨ (u = s q ∧ q = q') := by
  simp only [mem_insert, mem_singleton] at h1 h2
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with e | e | e
  · exact Or.inl ⟨rfl, h.rinj e⟩
  · exact absurd e (h.rc i j')
  · exact absurd e (h.rs i q')
  · exact absurd e.symm (h.rc i' j)
  · exact Or.inr (Or.inl ⟨rfl, h.cinj e⟩)
  · exact absurd e (h.cs j q')
  · exact absurd e.symm (h.rs i' q)
  · exact absurd e.symm (h.cs j' q)
  · exact Or.inr (Or.inr ⟨rfl, h.sinj e⟩)

theorem latPackK_disj {l : Fin m → Fin m → Fin m} (hl : _root_.STS.IsLatin l) :
    ((latPackK r c s l : Finset (Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint
      triEdges := by
  intro T hT T' hT' hne
  simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range, latPackK] at hT hT'
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
    rcases vtypeK h hu hu' with ⟨eu, h1⟩ | ⟨eu, h1⟩ | ⟨eu, h1⟩ <;>
    rcases vtypeK h hv hv' with ⟨ev, h2⟩ | ⟨ev, h2⟩ | ⟨ev, h2⟩
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

theorem latPackK_deg {l : Fin m → Fin m → Fin m} (hl : _root_.STS.IsLatin l) (v : Fin n) :
    degL ((latPackK r c s l).biUnion triEdges) v ≤ 9 * m := by
  classical
  set cell : Fin m × Fin m → Finset (Fin n) := fun p => {r p.1, c p.2, s (l p.1 p.2)}
  set I := (univ : Finset (Fin m × Fin m)).filter fun p => v ∈ cell p
  have hsub : nbL ((latPackK r c s l).biUnion triEdges) v ⊆ I.biUnion cell := by
    intro w hw
    simp only [nbL, mem_filter, mem_univ, true_and, mem_biUnion, latPackK, mem_image] at hw
    obtain ⟨T, ⟨p, -, rfl⟩, he⟩ := hw
    simp only [triEdges, mem_filter, mk_mem_sym2_iff] at he
    exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, he.1.2⟩, he.1.1⟩
  have hI : #I ≤ 3 * m := by
    have h3 : I ⊆ (univ.filter fun p : Fin m × Fin m => r p.1 = v) ∪
        (univ.filter fun p : Fin m × Fin m => c p.2 = v) ∪
        (univ.filter fun p : Fin m × Fin m => s (l p.1 p.2) = v) := by
      intro p hp
      simp only [I, cell, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hp
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases hp with e | e | e
      · exact Or.inl (Or.inl e.symm)
      · exact Or.inl (Or.inr e.symm)
      · exact Or.inr e.symm
    have c1 : #(univ.filter fun p : Fin m × Fin m => r p.1 = v) ≤ m := by
      refine (card_le_card_of_injOn (fun p => p.2) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_).trans
        (by simp)
      intro p hp q hq he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      exact Prod.ext (h.rinj (hp.trans hq.symm)) he
    have c2 : #(univ.filter fun p : Fin m × Fin m => c p.2 = v) ≤ m := by
      refine (card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_).trans
        (by simp)
      intro p hp q hq he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      exact Prod.ext he (h.cinj (hp.trans hq.symm))
    have c3 : #(univ.filter fun p : Fin m × Fin m => s (l p.1 p.2) = v) ≤ m := by
      refine (card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_).trans
        (by simp)
      intro p hp q hq he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      have hpq := h.sinj (hp.trans hq.symm)
      simp only at he
      rw [he] at hpq
      exact Prod.ext he ((hl.1 q.1).1 hpq)
    calc #I ≤ _ := card_le_card h3
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ m + m + m := add_le_add (add_le_add c1 c2) c3
      _ = 3 * m := by ring
  calc degL ((latPackK r c s l).biUnion triEdges) v ≤ #(I.biUnion cell) := card_le_card hsub
    _ ≤ ∑ p ∈ I, #(cell p) := card_biUnion_le
    _ ≤ ∑ _p ∈ I, 3 := by gcongr; exact card_le_three
    _ = 3 * #I := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ 9 * m := by omega

open Classical in
/-- `L(m) ≤ 2^{n²} · kCount` when every Latin packing completes. -/
theorem latin_le_kCount
    (hcomp : ∀ l : Fin m → Fin m → Fin m, _root_.STS.IsLatin l →
      ∃ D, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧ latPackK r c s l ⊆ D) :
    _root_.STS.L m ≤ 2 ^ (n ^ 2) * kCount lab := by
  set Lat := (univ : Finset (Fin m → Fin m → Fin m)).filter _root_.STS.IsLatin
  have hL : _root_.STS.L m = #Lat := by
    unfold _root_.STS.L; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set f : (Fin m → Fin m → Fin m) → Finset (Finset (Fin n)) := fun l =>
    if hl : _root_.STS.IsLatin l then Classical.choose (hcomp l hl) else ∅
  have hf : ∀ l ∈ Lat, latPackK r c s l ⊆ f l ∧ f l ∈ kBlocks lab := by
    intro l hl
    have hl' := (mem_filter.mp hl).2
    have hs := Classical.choose_spec (hcomp l hl')
    simp only [f, dif_pos hl']
    exact ⟨hs.2, mem_kBlocks_of_decomp lab hs.1⟩
  have hfib : ∀ Z ∈ Lat.image f, #(Lat.filter fun l => f l = Z) ≤ 2 ^ (n ^ 2) := by
    intro Z hZ
    obtain ⟨l₀, hl₀, rfl⟩ := mem_image.mp hZ
    have hZr := (hf l₀ hl₀).2
    have hZsts : _root_.STS.IsSTS (f l₀) := by
      unfold kBlocks at hZr; exact (mem_filter.mp hZr).2.1
    calc #(Lat.filter fun l => f l = f l₀) ≤ #(f l₀).powerset := by
          refine card_le_card_of_injOn (latPackK r c s) (fun l hl => ?_)
            (fun l _ l' _ he => latPackK_injective h he)
          simp only [coe_filter, Set.mem_ofPred_eq] at hl
          rw [mem_coe, mem_powerset, ← hl.2]
          exact (hf l hl.1).1
      _ = 2 ^ #(f l₀) := card_powerset _
      _ ≤ 2 ^ (n ^ 2) := Nat.pow_le_pow_right (by norm_num) (card_sts_le_sq hZsts)
  rw [hL]
  calc #Lat ≤ 2 ^ (n ^ 2) * #(Lat.image f) := card_le_mul_card_image Lat _ hfib
    _ ≤ 2 ^ (n ^ 2) * kCount lab := by
        gcongr
        exact card_le_card fun Z hZ => by
          obtain ⟨l, hl, rfl⟩ := mem_image.mp hZ; exact (hf l hl).2

end Lat

/-- Latin placements exist when the classes are large enough. -/
theorem exists_latPlace (lab : Fin n → Fin k) {X Y : Fin k} (hXY : X ≠ Y) {m : ℕ}
    (hX : 2 * m ≤ ksz lab X) (hY : m ≤ ksz lab Y) :
    ∃ r c s : Fin m → Fin n, LatPlace lab X Y r c s := by
  classical
  have cX : Fintype.card (Fin (2 * m)) ≤ Fintype.card {v // lab v = X} := by
    rw [Fintype.card_fin, Fintype.card_subtype]; exact hX
  have cY : Fintype.card (Fin m) ≤ Fintype.card {v // lab v = Y} := by
    rw [Fintype.card_fin, Fintype.card_subtype]; exact hY
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le cX
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le cY
  refine ⟨fun i => (e ⟨i.val, by omega⟩).1, fun j => (e ⟨m + j.val, by omega⟩).1,
    fun q => (f q).1, ⟨?_, ?_, ?_, ?_, fun i => (e _).2, fun j => (e _).2, fun q => (f q).2, hXY⟩⟩
  · intro i i' hii
    have := e.injective (Subtype.ext hii)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro j j' hjj
    have := e.injective (Subtype.ext hjj)
    exact Fin.ext (by have := congrArg Fin.val this; simp at this; omega)
  · intro q q' hqq
    exact f.injective (Subtype.ext hqq)
  · intro i j hij
    have := e.injective (Subtype.ext hij)
    have h2 := congrArg Fin.val this
    simp at h2
    omega

/-! ### Logarithms -/

theorem log_upper_of {N ε Kr : ℝ} (hε : 0 < ε) (hN : 360004 ≤ N) (hK : 0 ≤ Kr)
    (hup : Kr ≤ Real.exp (N * (N - 1) / 6 * (Real.log N - 2 + 1200 / Real.sqrt (N - 3)))) :
    Real.log Kr ≤ (1 / 6 + ε) * N ^ 2 * Real.log N := by
  have hsq : 600 ≤ Real.sqrt (N - 3) := by
    rw [show (600 : ℝ) = Real.sqrt (600 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hfrac : 1200 / Real.sqrt (N - 3) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hfrac0 : 0 ≤ 1200 / Real.sqrt (N - 3) := by positivity
  have hlog2 : 2 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h82 : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ < 2.7182818286 * 2.7182818286 := by gcongr
        _ < 8 := by norm_num
    linarith
  have hX0 : 0 ≤ Real.log N - 2 + 1200 / Real.sqrt (N - 3) := by linarith
  have hXl : Real.log N - 2 + 1200 / Real.sqrt (N - 3) ≤ Real.log N := by linarith
  have hA : 0 ≤ N * (N - 1) / 6 := by
    have : 0 ≤ N * (N - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hA2 : N * (N - 1) / 6 ≤ N ^ 2 / 6 := by nlinarith
  have hlogR : Real.log Kr ≤ N * (N - 1) / 6 * (Real.log N - 2 + 1200 / Real.sqrt (N - 3)) := by
    rcases hK.eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero]; exact mul_nonneg hA hX0
    · have := Real.log_le_log hpos hup
      rwa [Real.log_exp] at this
  have hL : 0 ≤ Real.log N := by linarith
  calc Real.log Kr ≤ N * (N - 1) / 6 * (Real.log N - 2 + 1200 / Real.sqrt (N - 3)) := hlogR
    _ ≤ N ^ 2 / 6 * Real.log N := mul_le_mul hA2 hXl hX0 (by positivity)
    _ ≤ (1 / 6 + ε) * N ^ 2 * Real.log N := by
        nlinarith [mul_nonneg (mul_nonneg hε.le (sq_nonneg N)) hL]

theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have := Real.exp_one_lt_d9
  calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ < 2.7182818286 * 2.7182818286 := by gcongr
    _ < 8 := by norm_num

theorem log_lower_of {N lam m Lr Kr : ℝ} (hlam0 : 0 < lam) (hN0 : 0 < N)
    (hmhalf : lam * N / 2 ≤ m) (hm8 : 8 ≤ m) (hlogL : m ^ 2 * (Real.log m - 2) ≤ Real.log Lr)
    (hlogR : Real.log Lr ≤ N ^ 2 * Real.log 2 + Real.log Kr)
    (hlogN : 16 * |Real.log 2 - lam ^ 2 / 4 * (Real.log (lam / 2) - 2)| / (3 * lam ^ 2) ≤
      Real.log N) :
    lam ^ 2 / 16 * N ^ 2 * Real.log N ≤ Real.log Kr := by
  set K₀ := Real.log 2 - lam ^ 2 / 4 * (Real.log (lam / 2) - 2) with hK₀
  have hlogm : Real.log N + Real.log (lam / 2) ≤ Real.log m := by
    rw [← Real.log_mul hN0.ne' (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hm2sq : lam ^ 2 * N ^ 2 / 4 ≤ m ^ 2 := by
    have h0 : 0 ≤ lam * N / 2 := by positivity
    have := pow_le_pow_left₀ h0 hmhalf 2
    nlinarith
  have hlogm2 : 2 ≤ Real.log m :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [exp_two_lt_eight])
  have hlogN0 : 0 ≤ Real.log N := le_trans (by positivity) hlogN
  have hmain : lam ^ 2 * N ^ 2 / 4 * (Real.log N + Real.log (lam / 2) - 2) ≤
      m ^ 2 * (Real.log m - 2) := by
    have hA : 0 ≤ Real.log m - 2 := by linarith
    calc lam ^ 2 * N ^ 2 / 4 * (Real.log N + Real.log (lam / 2) - 2)
        ≤ lam ^ 2 * N ^ 2 / 4 * (Real.log m - 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ m ^ 2 * (Real.log m - 2) := mul_le_mul_of_nonneg_right hm2sq hA
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
  linarith

/-! ### The counting theorem -/

set_option maxHeartbeats 4000000 in
/-- **Counting `k`-bicoloured Steiner triple systems.** -/
theorem kbicolour_count (k : ℕ) (hk : 3 ≤ k) {δ η ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ cst : ℝ, 0 < cst ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      (∃ a, SeedData (ksz lab) η a) →
      cst * (n : ℝ) ^ 2 * Real.log n ≤ Real.log (kCount lab) ∧
        Real.log (kCount lab) ≤ (1 / 6 + ε) * (n : ℝ) ^ 2 * Real.log n := by
  obtain ⟨γ, hγ0, hγδ, nC, hC⟩ := kbicolour_completion k hk hδ hδ1 hη
  set lam : ℝ := γ / 9 with hlam
  have hlam0 : 0 < lam := by positivity
  set K₀ : ℝ := Real.log 2 - lam ^ 2 / 4 * (Real.log (lam / 2) - 2) with hK₀
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, Real.exp (16 * |K₀| / (3 * lam ^ 2)) ≤ N1 := exists_nat_ge _
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, 64 / lam ≤ N2 := exists_nat_ge _
  refine ⟨lam ^ 2 / 16, by positivity, max nC (max 360004 (max N1 N2)),
    fun n lab hn hodd hcls heven hdiv hseed => ⟨?_, ?_⟩⟩
  · have hnC : nC ≤ n := le_of_max_le_left hn
    have hN1n : N1 ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_max_le_right hn)
    have hN2n : N2 ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_max_le_right hn)
    have h360 : 360004 ≤ n := le_trans (le_max_left _ _) (le_of_max_le_right hn)
    have hN0 : (0 : ℝ) < n := by
      have : (0 : ℝ) < 360004 := by norm_num
      exact lt_of_lt_of_le this (by exact_mod_cast h360)
    have hlamN : 64 ≤ lam * n := by
      have : 64 / lam ≤ (n : ℝ) := hN2.trans (by exact_mod_cast hN2n)
      rw [div_le_iff₀ hlam0] at this; linarith
    set m : ℕ := ⌊lam * n⌋₊ with hm
    have hm1 : lam * n - 1 < m := Nat.sub_one_lt_floor _
    have hm2 : (m : ℝ) ≤ lam * n := Nat.floor_le (by positivity)
    -- two classes
    set X : Fin k := ⟨0, by omega⟩
    set Y : Fin k := ⟨1, by omega⟩
    have hXY : X ≠ Y := by simp [X, Y, Fin.ext_iff]
    have hmX : 2 * m ≤ ksz lab X := by
      have : (2 * m : ℝ) ≤ ksz lab X := by
        have := hcls X
        have : 2 * lam ≤ δ := by rw [hlam]; linarith
        nlinarith
      exact_mod_cast this
    have hmY : m ≤ ksz lab Y := by
      have : (m : ℝ) ≤ ksz lab Y := by
        have := hcls Y
        have : lam ≤ δ := by rw [hlam]; linarith
        nlinarith
      exact_mod_cast this
    obtain ⟨r, c, s, hpl⟩ := exists_latPlace lab hXY hmX hmY
    have hdeg9 : ((9 * m : ℕ) : ℝ) ≤ γ * n := by
      push_cast
      have : 9 * lam = γ := by rw [hlam]; ring
      nlinarith
    have hcomp : ∀ l : Fin m → Fin m → Fin m, _root_.STS.IsLatin l →
        ∃ D, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧
          latPackK r c s l ⊆ D := fun l hl =>
      hC n lab hnC hodd hcls heven hdiv hseed (latPackK r c s l) (9 * m)
        (latPackK_allowed hpl l) (latPackK_disj hpl hl) (latPackK_deg hpl hl) hdeg9
    have hLm := latin_le_kCount hpl hcomp
    -- logarithms
    have hm8 : (8 : ℝ) ≤ m := by linarith
    have hmpos : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
    have hlogL := _root_.STS.hL_one _root_.STS.van_der_waerden m hmpos
    have hlogm2 : (2 : ℝ) < Real.log m := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]; linarith [exp_two_lt_eight]
    have hLpos : (0 : ℝ) < _root_.STS.L m := by
      by_contra hz
      push Not at hz
      have h0 : (_root_.STS.L m : ℝ) = 0 := le_antisymm hz (Nat.cast_nonneg _)
      rw [h0, Real.log_zero] at hlogL
      have hp : 0 < (m : ℝ) ^ 2 * (Real.log m - 2) := mul_pos (by positivity) (by linarith)
      linarith
    have hle : (_root_.STS.L m : ℝ) ≤ 2 ^ (n ^ 2) * kCount lab := by exact_mod_cast hLm
    have hRpos : (0 : ℝ) < kCount lab := by
      by_contra hz; push Not at hz
      have h0 : (kCount lab : ℝ) = 0 := le_antisymm hz (Nat.cast_nonneg _)
      rw [h0, mul_zero] at hle
      linarith
    have hlogR : Real.log (_root_.STS.L m) ≤ (n : ℝ) ^ 2 * Real.log 2 + Real.log (kCount lab) := by
      have h2 := Real.log_le_log hLpos hle
      rw [Real.log_mul (by positivity) hRpos.ne', Real.log_pow] at h2
      push_cast at h2; linarith
    have hlogN : 16 * |K₀| / (3 * lam ^ 2) ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hN0]
      exact hN1.trans (by exact_mod_cast hN1n)
    rw [one_mul] at hlogL
    exact log_lower_of hlam0 hN0 (by linarith) hm8 hlogL hlogR hlogN
  · have h360 : 360004 ≤ n := le_trans (le_max_left _ _) (le_of_max_le_right hn)
    have hup := kCount_upper lab (by omega)
    exact log_upper_of hε (by exact_mod_cast h360) (Nat.cast_nonneg _) hup

end CDRBicolour.KBicolor
