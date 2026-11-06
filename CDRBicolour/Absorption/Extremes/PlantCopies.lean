/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Exact.Copies
public import CDRBicolour.Absorption.Extremes.Lattice5

/-!
# Planting `AAC` blocks, part 1: copies of an `AAC` triangle (item 3, extremes)

The *`AAC` triangle* on the nine-point model is `{A₀A₁C₆, A₁A₂C₇, A₀A₂C₈}`: three `AAC` blocks,
every model point of `A` in exactly two of them.  Copies indexed by `q ∈ Q ⊆ ℤ_m²` (the
transversal design of `Exact/Copies`) are edge-disjoint, contain `3|Q|` blocks, put every point
of `A` in an even number of blocks, and their leave has degree `≤ 81 m`.  All their vertices lie
in the first `3m` points of each class, and their `AA` edges join different blocks of `m`.

General facts about `AAC` packings: an `AAC` block `{u,u',w}` meets the `C` class only in `w`,
so in an edge-disjoint `AAC` packing the `C`-neighbours of `u ∈ A` in the leave correspond to the
blocks through `u` (`card_Cnbr_leave`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Extremes

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Exact

/-! ### `AAC` packings in general -/

section General

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

/-- The `C` vertex of an `AAC` block. -/
theorem aac_C_unique {T : Finset V} (hT : T.val.map lab = aac) {w w' : V} (hw : w ∈ T)
    (hw' : w' ∈ T) (h2 : lab w = 2) (h2' : lab w' = 2) : w = w' := by
  by_contra hne
  have hc : (T.filter fun x => lab x = 2).card = (T.val.map lab).count 2 := by
    rw [Multiset.count_map, card_def, filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  rw [hT] at hc
  have h1 : (T.filter fun x => lab x = 2).card = 1 := by rw [hc]; simp [aac]
  have hsub : ({w, w'} : Finset V) ⊆ T.filter fun x => lab x = 2 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_filter.mpr ⟨hw, h2⟩
    · exact mem_filter.mpr ⟨hw', h2'⟩
  have := card_le_card hsub
  rw [card_pair hne, h1] at this
  omega

/-- In an edge-disjoint `AAC` packing, the `C`-neighbours of `u ∈ A` in the leave correspond
to the blocks through `u`. -/
theorem card_Cnbr_leave (P : Finset (Finset V)) (hP : ∀ T ∈ P, T.val.map lab = aac)
    (hPd : (P : Set (Finset V)).PairwiseDisjoint triEdges) {u : V} (hu : lab u = 0) :
    (univ.filter fun w => lab w = 2 ∧ s(u, w) ∈ P.biUnion triEdges).card =
      (P.filter (u ∈ ·)).card := by
  classical
  -- each block through `u` has a unique `C` vertex
  have hC : ∀ T ∈ P, ∃ w ∈ T, lab w = 2 := by
    intro T hT
    have : 0 < (T.val.map lab).count 2 := by rw [hP T hT]; simp [aac]
    obtain ⟨w, hw, hw2⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp this)
    exact ⟨w, hw, hw2⟩
  symm
  refine card_bij (fun T hT => (hC T (mem_filter.mp hT).1).choose) ?_ ?_ ?_
  · intro T hT
    obtain ⟨hTP, huT⟩ := mem_filter.mp hT
    obtain ⟨hw, hw2⟩ := (hC T hTP).choose_spec
    refine mem_filter.mpr ⟨mem_univ _, hw2, mem_biUnion.mpr ⟨T, hTP, ?_⟩⟩
    rw [mem_triEdges_pair]
    exact ⟨huT, hw, fun h => by rw [← h, hu] at hw2; exact absurd hw2 (by decide)⟩
  · intro T₁ h₁ T₂ h₂ heq
    obtain ⟨hT₁, hu₁⟩ := mem_filter.mp h₁
    obtain ⟨hT₂, hu₂⟩ := mem_filter.mp h₂
    obtain ⟨hw₁, hw2₁⟩ := (hC T₁ hT₁).choose_spec
    obtain ⟨hw₂, -⟩ := (hC T₂ hT₂).choose_spec
    by_contra hne
    set w := (hC T₁ hT₁).choose
    have huw : u ≠ w := fun h => by rw [← h, hu] at hw2₁; exact absurd hw2₁ (by decide)
    have e1 : s(u, w) ∈ triEdges T₁ := mem_triEdges_pair.mpr ⟨hu₁, hw₁, huw⟩
    have e2 : s(u, w) ∈ triEdges T₂ := mem_triEdges_pair.mpr ⟨hu₂, heq ▸ hw₂, huw⟩
    exact disjoint_left.mp (hPd hT₁ hT₂ hne) e1 e2
  · intro w hw
    obtain ⟨-, hw2, hwL⟩ := mem_filter.mp hw
    obtain ⟨T, hTP, he⟩ := mem_biUnion.mp hwL
    obtain ⟨huT, hwT, -⟩ := mem_triEdges_pair.mp he
    refine ⟨T, mem_filter.mpr ⟨hTP, huT⟩, ?_⟩
    obtain ⟨hw', hw2'⟩ := (hC T hTP).choose_spec
    exact aac_C_unique (hP T hTP) hw' hwT hw2' hw2

open Classical in
/-- The `C`-degree of `u ∈ A` in the residual graph. -/
theorem card_Cnbr_res (P : Finset (Finset V)) (hP : ∀ T ∈ P, T.val.map lab = aac)
    (hPd : (P : Set (Finset V)).PairwiseDisjoint triEdges) {u : V} (hu : lab u = 0) :
    (univ.filter fun w => lab w = 2 ∧ (rG (P.biUnion triEdges)).Adj u w).card +
      (P.filter (u ∈ ·)).card = (univ.filter fun w => lab w = 2).card := by
  classical
  rw [← card_Cnbr_leave P hP hPd hu, ← card_union_of_disjoint]
  · congr 1
    ext w
    simp only [mem_union, mem_filter, mem_univ, true_and, rG_adj]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hL : s(u, w) ∈ P.biUnion triEdges
      · exact Or.inr ⟨h, hL⟩
      · refine Or.inl ⟨h, hL, fun e => ?_⟩
        rw [e, h] at hu; exact absurd hu (by decide)
  · rw [disjoint_left]
    intro w h1 h2
    exact (rG_adj.mp (mem_filter.mp h1).2.2).1 (mem_filter.mp h2).2.2

end General

/-! ### Copies of the `AAC` triangle -/

/-- The `AAC` triangle on the model. -/
def tgM : Finset (Finset (Fin 9)) := {{0, 1, 6}, {1, 2, 7}, {0, 2, 8}}

set_option maxRecDepth 100000 in
theorem tgM_facts : (∀ T ∈ tgM, T.card = 3 ∧ T.val.map mcol = aac) ∧
    (∀ T ∈ tgM, ∀ T' ∈ tgM, T ≠ T' → Disjoint (te T) (te T')) ∧
    (∀ i : Fin 9, mcol i = 0 → (tgM.filter (i ∈ ·)).card = 2) := by
  unfold aac; decide +kernel

variable {a b c m : ℕ}

/-- The copies indexed by `Q`. -/
def tcopies [NeZero m] (h : CopyCond a b c m) (Q : Finset (ZMod m × ZMod m)) :
    Finset (Finset (Fin (a + b + c))) :=
  Q.biUnion fun q => tgM.image fun T => T.map (phiE h q)

theorem mem_tcopies [NeZero m] (h : CopyCond a b c m) {Q : Finset (ZMod m × ZMod m)}
    {T : Finset (Fin (a + b + c))} (hT : T ∈ tcopies h Q) :
    ∃ q ∈ Q, ∃ T₀ ∈ tgM, T = T₀.map (phiE h q) := by
  obtain ⟨q, hq, hT⟩ := mem_biUnion.mp hT
  obtain ⟨T₀, h₀, rfl⟩ := mem_image.mp hT
  exact ⟨q, hq, T₀, h₀, rfl⟩

theorem map_aac [NeZero m] (h : CopyCond a b c m) (q : ZMod m × ZMod m) {T₀ : Finset (Fin 9)}
    (h₀ : T₀ ∈ tgM) : (T₀.map (phiE h q)).val.map (col3 a b c) = aac := by
  rw [map_val, Multiset.map_map]
  have : (col3 a b c ∘ (phiE h q)) = mcol := funext fun i => col3_phi h q i
  rw [this]; exact (tgM_facts.1 T₀ h₀).2

theorem tcopies_allowed [NeZero m] (h : CopyCond a b c m) (Q : Finset (ZMod m × ZMod m)) :
    ∀ T ∈ tcopies h Q, IsAllowed (cdrHost a b c) cdrF T ∧ T.val.map (col3 a b c) = aac := by
  intro T hT
  obtain ⟨q, -, T₀, h₀, rfl⟩ := mem_tcopies h hT
  have haac := map_aac h q h₀
  refine ⟨⟨by rw [card_map]; exact (tgM_facts.1 T₀ h₀).1, fun x _ y _ hxy => hxy, ?_⟩, haac⟩
  show (T₀.map (phiE h q)).val.map (col3 a b c) ∈ cdrF
  rw [haac]; unfold aac cdrF; decide

theorem tcopies_disj [Fact m.Prime] (h : CopyCond a b c m) (Q : Finset (ZMod m × ZMod m)) :
    ((tcopies h Q : Finset (Finset (Fin (a + b + c)))) : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint
      triEdges := by
  intro T hT T' hT' hne
  obtain ⟨q, -, T₀, h₀, rfl⟩ := mem_tcopies h hT
  obtain ⟨q', -, T₀', h₀', rfl⟩ := mem_tcopies h hT'
  by_cases hqq : q = q'
  · subst hqq
    have hne₀ : T₀ ≠ T₀' := fun e => hne (by rw [e])
    show Disjoint (triEdges (T₀.map (phiE h q))) (triEdges (T₀'.map (phiE h q)))
    rw [triEdges_map, triEdges_map, disjoint_map, ← te_eq, ← te_eq]
    exact tgM_facts.2.1 T₀ h₀ T₀' h₀' hne₀
  · show Disjoint (triEdges (T₀.map (phiE h q))) (triEdges (T₀'.map (phiE h q')))
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨i, j, hij, -, -, rfl⟩ := edge_of_map h he
    obtain ⟨i', j', -, -, -, he2⟩ := edge_of_map h he'
    exact hqq (copy_edge h hij he2)

theorem tcopies_card [Fact m.Prime] (h : CopyCond a b c m) (Q : Finset (ZMod m × ZMod m)) :
    (tcopies h Q).card = 3 * Q.card := by
  unfold tcopies
  rw [card_biUnion]
  · have : ∀ q ∈ Q, (tgM.image fun T => T.map (phiE h q)).card = 3 := by
      intro q _
      rw [card_image_of_injective _ (map_inj (phiE h q))]; rfl
    rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm]
  · intro q _ q' _ hqq
    rw [Function.onFun, Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨T₀, h₀, rfl⟩ := mem_image.mp hT
    obtain ⟨T₀', -, he⟩ := mem_image.mp hT'
    obtain ⟨x, y, z, hxy, -, -, hT₀⟩ := card_eq_three.mp (tgM_facts.1 T₀ h₀).1
    have hmem : s(phiE h q x, phiE h q y) ∈ triEdges (T₀.map (phiE h q)) := by
      rw [triEdges_map, mem_map, hT₀]
      exact ⟨s(x, y), by simp [triEdges, hxy], rfl⟩
    rw [← he] at hmem
    obtain ⟨i', j', -, -, -, he2⟩ := edge_of_map h hmem
    exact hqq (copy_edge h hxy he2)

/-- Every point of `A` lies in an even number of copy blocks. -/
theorem tcopies_parity [Fact m.Prime] (h : CopyCond a b c m) (Q : Finset (ZMod m × ZMod m))
    {u : Fin (a + b + c)} (hu : col3 a b c u = 0) :
    Even ((tcopies h Q).filter (u ∈ ·)).card := by
  unfold tcopies
  rw [filter_biUnion, card_biUnion]
  · refine Finset.even_sum _ fun q _ => ?_
    by_cases hr : ∃ i, Exact.phi h q i = u
    · obtain ⟨i, rfl⟩ := hr
      have hi : mcol i = 0 := by rw [← col3_phi h q i]; exact hu
      have : ((tgM.image fun T => T.map (phiE h q)).filter (Exact.phi h q i ∈ ·)) =
          (tgM.filter (i ∈ ·)).image fun T => T.map (phiE h q) := by
        rw [filter_image]
        congr 1
        refine filter_congr fun T _ => ?_
        constructor
        · intro hT
          obtain ⟨j, hj, hji⟩ := mem_map.mp hT
          rwa [show j = i from phi_inj h q hji] at hj
        · intro hT; exact mem_map.mpr ⟨i, hT, rfl⟩
      rw [this, card_image_of_injective _ (map_inj (phiE h q)), tgM_facts.2.2 i hi]
      exact even_two
    · push Not at hr
      rw [card_eq_zero.mpr]
      · exact ⟨0, rfl⟩
      · ext T
        simp only [mem_filter, mem_image, notMem_empty, iff_false, not_and]
        rintro ⟨T₀, -, rfl⟩ hT
        obtain ⟨j, -, hj⟩ := mem_map.mp hT
        exact hr j hj
  · intro q _ q' _ hqq
    rw [Function.onFun]
    refine disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨T₀, h₀, rfl⟩ := mem_image.mp hT
    obtain ⟨T₀', -, he⟩ := mem_image.mp hT'
    obtain ⟨x, y, z, hxy, -, -, hT₀⟩ := card_eq_three.mp (tgM_facts.1 T₀ h₀).1
    have hmem : s(phiE h q x, phiE h q y) ∈ triEdges (T₀.map (phiE h q)) := by
      rw [triEdges_map, mem_map, hT₀]
      exact ⟨s(x, y), by simp [triEdges, hxy], rfl⟩
    rw [← he] at hmem
    obtain ⟨i', j', -, -, -, he2⟩ := edge_of_map h hmem
    exact hqq (copy_edge h hxy he2)

/-- Vertices of the copies lie in the first `3m` points of their class. -/
theorem tcopies_region [NeZero m] (h : CopyCond a b c m) {Q : Finset (ZMod m × ZMod m)}
    {T : Finset (Fin (a + b + c))} (hT : T ∈ tcopies h Q) {x : Fin (a + b + c)} (hx : x ∈ T) :
    (col3 a b c x = 0 → x.val < 3 * m) ∧ (col3 a b c x = 2 → x.val < a + b + 3 * m) := by
  obtain ⟨q, -, T₀, h₀, rfl⟩ := mem_tcopies h hT
  obtain ⟨i, -, rfl⟩ := mem_map.mp hx
  have hv := phi_val h q i
  have x1 := ZMod.val_lt (q.1 + (i.val : ZMod m) * q.2)
  have hc := col3_phi h q i
  change (col3 a b c (Exact.phi h q i) = 0 → (Exact.phi h q i).val < 3 * m) ∧
    (col3 a b c (Exact.phi h q i) = 2 → (Exact.phi h q i).val < a + b + 3 * m)
  rw [hc, hv]
  have hi := i.isLt
  have hr : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  constructor
  · intro h0
    have h0' : i.val / 3 = 0 := by simpa [mcol, Fin.ext_iff] using h0
    simp only [kst, h0', if_true]
    rcases hr with hr | hr | hr <;> rw [hr] <;> omega
  · intro h2
    have h2' : i.val / 3 = 2 := by simpa [mcol, Fin.ext_iff] using h2
    simp only [kst, h2', show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, if_false]
    rcases hr with hr | hr | hr <;> rw [hr] <;> omega

/-- The excluded copy: the only one with an `AA` edge `{m − 1, m}`. -/
def qStar (m : ℕ) : ZMod m × ZMod m := ((m - 1 : ℕ), 1)

/-- `AA` edges of the copies (outside `q*`) never join `x` and `x + 1` with `x` even. -/
theorem tcopies_AA [Fact m.Prime] (h : CopyCond a b c m) {Q : Finset (ZMod m × ZMod m)}
    (hQ : qStar m ∉ Q) (hodd : Odd m) {T : Finset (Fin (a + b + c))} (hT : T ∈ tcopies h Q)
    {x y : Fin (a + b + c)} (hx : x ∈ T) (hy : y ∈ T) (hx0 : col3 a b c x = 0)
    (hy0 : col3 a b c y = 0) (hxy : y.val = x.val + 1) : Odd x.val := by
  obtain ⟨q, hq, T₀, h₀, rfl⟩ := mem_tcopies h hT
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
  have hvi := phi_val h q i
  have hvj := phi_val h q j
  have xi := ZMod.val_lt (q.1 + (i.val : ZMod m) * q.2)
  have xj := ZMod.val_lt (q.1 + (j.val : ZMod m) * q.2)
  have ci : mcol i = 0 := by rw [← col3_phi h q i]; exact hx0
  have cj : mcol j = 0 := by rw [← col3_phi h q j]; exact hy0
  change (Exact.phi h q j).val = (Exact.phi h q i).val + 1 at hxy
  change Odd (Exact.phi h q i).val
  rw [hvi, hvj] at hxy
  rw [hvi]
  have m8 := h.m8
  have hi3 : i.val / 3 = 0 := by simpa [mcol, Fin.ext_iff] using ci
  have hj3 : j.val / 3 = 0 := by simpa [mcol, Fin.ext_iff] using cj
  simp only [kst, hi3, hj3, if_true, zero_add] at hxy ⊢
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
    simp only [hi, hj, Nat.zero_mod, Nat.one_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, zero_mul, one_mul, add_zero] at hxy xi xj ⊢
  all_goals try omega
  all_goals try (exact ⟨m - 1, by omega⟩)
  · -- `i = 0`, `j = 1`: the excluded copy
    exfalso
    have h1 : q.1.val = m - 1 := by omega
    have h2 : (q.1 + q.2).val = 0 := by omega
    apply hQ
    have e1 : q.1 = ((m - 1 : ℕ) : ZMod m) := by rw [← h1, ZMod.natCast_zmod_val]
    have e2 : q.1 + q.2 = 0 := (ZMod.val_eq_zero _).mp h2
    have hm1 : ((m - 1 : ℕ) : ZMod m) + 1 = 0 := by
      have := congrArg (fun k : ℕ => (k : ZMod m)) (Nat.sub_add_cancel (show 1 ≤ m by omega))
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at this
      exact this
    have e3 : q.2 = 1 := by linear_combination e2 - e1 - hm1
    have : q = qStar m := Prod.ext e1 e3
    rw [this] at hq; exact hq

end CDRBicolour.Absorption.Extremes
