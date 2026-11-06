/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Steps67
public import OneFactor.Main
public import OneFactor.Factors2

/-!
# Regular graphs of degree at least `6/7` of the order are 1-factorizable

**Theorem** (`colorable_of_regular67`). A `d`-regular graph on `2n` vertices with `12 n ≤ 7 d` is
`d`-edge-colourable (Chetwynd–Hilton, *Regular graphs of high degree are 1-factorizable*, Proc.
London Math. Soc. 50 (1985)).

The proof is that of Chetwynd–Hilton 1989, Theorem 1, §4, with `p ≥ 0` (any `w`, `v*`): remove `w`,
take a maximal matching `M` of `H = G[(X ∪ W) − v*]`, label `H* = H + v*` by the staircase
(`stairOf`), and peel off the staircase classes as near 1-factors of `G − w − M`. The `v* y` edges
of the pairs `(y, σ y)` whose `x = σ y` is not left uncovered by its class (at most `|Y|/2`,
`exists_pairing`) get one extra factor each; this replaces the ordering claim of the article. The
rest has the core of Theorem 5 (`core_colorable`); then add the factors missing `v*`, re-insert
`v*`, add the other factors and re-insert `w`, as in `colorable_of_regular`.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Regular graphs of degree at least `6/7` of the (even) order are 1-factorizable.** -/
theorem colorable_of_regular67 {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : ∀ v, G.degree v = d) (hd : 12 * n ≤ 7 * d) : G.lineGraph.Colorable d := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.1 (by omega)
    exact colorable_of_full_indep _ G le_rfl (fun v => (hreg v).le) fun u => isEmptyElim u
  haveI : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨w⟩ := ‹Nonempty V›
  obtain ⟨vs, hvsw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) w
  have hwv : w ≠ vs := Ne.symm hvsw
  -- the sets
  have hXY : #(setX G w vs) = #(setY G w vs) := card_X_eq_card_Y (G := G) hreg hwv
  have hr : #(setW G w) + d + 1 = 2 * n := by rw [← hcard]; exact card_nonNbr G hreg w
  have hYW : (setY G w vs) ⊆ (setW G w) := filter_subset _ _
  have hYle : #(setY G w vs) ≤ #(setW G w) := card_le_card hYW
  have hHVc : #((setX G w vs ∪ setW G w).erase vs) ≤ #(setX G w vs) + #(setW G w) := card_erase_le.trans (card_union_le _ _)
  have hvsHV : vs ∉ ((setX G w vs ∪ setW G w).erase vs) := notMem_erase vs _
  have hXHV : (setX G w vs) ⊆ ((setX G w vs ∪ setW G w).erase vs) := fun x hx =>
    mem_erase.2 ⟨(mem_setX.1 hx).2.1, mem_union_left _ hx⟩
  have hYHV : (setY G w vs) ⊆ ((setX G w vs ∪ setW G w).erase vs) := fun y hy =>
    mem_erase.2 ⟨fun e => (mem_setY.1 hy).2.ne e.symm, mem_union_right _ (hYW hy)⟩
  have hXYd : Disjoint (setX G w vs) (setY G w vs) := Finset.disjoint_left.2 fun a ha hb =>
    (mem_setY.1 hb).1.2 (mem_setX.1 ha).1
  have hwHV : w ∉ ((setX G w vs ∪ setW G w).erase vs) := fun h => by
    rcases mem_union.1 (mem_erase.1 h).2 with h | h
    · exact (mem_setX.1 h).1.ne rfl
    · exact (mem_setW.1 h).1 rfl
  have hwHS : w ∉ insert vs ((setX G w vs ∪ setW G w).erase vs) := fun h => (mem_insert.1 h).elim hwv hwHV
  -- the maximal matching and the labelling
  obtain ⟨M, hMG, hM, hMS, hMmax⟩ := exists_maximal_matching (keepAt G w ∅) ((setX G w vs ∪ setW G w).erase vs)
  obtain ⟨D, hD⟩ : ∃ D, D = stairOf (X := (setX G w vs)) (Y := (setY G w vs)) (hM' := hM) (hMS' := hMS)
      (hvs' := hvsHV) := ⟨_, rfl⟩
  have hside : ∀ v, D.side v = sideOf M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs) vs v := fun v => by subst hD; rfl
  have hidx : ∀ v, D.idx v = idxOf M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs) vs v := fun v => by subst hD; rfl
  have hDm : D.m = #(leftM M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs)) := by subst hD; rfl
  have hDq : D.q = #((setX G w vs ∪ setW G w).erase vs) := by subst hD; exact stairOf_q
  have hsvs : D.side vs = true := by rw [hside]; exact side_vs
  have hivs : D.idx vs = D.m + 1 := by rw [hidx, hDm]; exact idx_vs
  have hsideH : ∀ v ∈ ((setX G w vs ∪ setW G w).erase vs), D.side v = true ↔ v ∈ leftM M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs) := fun v hv => by
    rw [hside]; exact side_of_mem hv hvsHV
  -- matching edges: opposite sides, equal indices, not in the staircase
  have hMside : ∀ u v, M.Adj u v →
      u ∈ ((setX G w vs ∪ setW G w).erase vs) ∧ v ∈ ((setX G w vs ∪ setW G w).erase vs) ∧ D.idx u = D.idx v ∧ D.side u ≠ D.side v := by
    intro u v huv
    obtain ⟨hu, hv⟩ := hMS u v huv
    by_cases hL : u ∈ leftM M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs)
    · obtain ⟨h1, h2⟩ := idx_eq_of_adj (hM := hM) (hMS := hMS) hvsHV hL huv
      refine ⟨hu, hv, by rw [hidx, hidx, h2], ?_⟩
      rw [(hsideH u hu).2 hL, hside, h1]; simp
    · have hcu : u ∈ cover M := mem_cover.2 ⟨v, huv⟩
      have hpv : partner M u = v := partner_eq hM huv
      have hvL : v ∈ leftM M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs) := hpv ▸ partner_mem_leftM hM hMS hu hcu hL
      obtain ⟨h1, h2⟩ := idx_eq_of_adj (hM := hM) (hMS := hMS) hvsHV hvL huv.symm
      refine ⟨hu, hv, by rw [hidx, hidx, h2], ?_⟩
      rw [(hsideH v hv).2 hvL, hside, h1]; simp
  have hMnotE : ∀ u v, M.Adj u v → ¬ D.Eplus G u v := by
    intro u v huv hE
    obtain ⟨-, -, he, hne⟩ := hMside u v huv
    obtain ⟨-, -, -, h⟩ := hE
    rcases h with ⟨h1, h2⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact hne (h1.trans h2.symm)
    · omega
    · omega
  -- the staircase edges at `v*`
  have hEvs : ∀ y, D.Eplus G vs y ↔ y ∈ (setY G w vs) := by
    intro y
    constructor
    · rintro ⟨-, hy, hadj, -⟩
      have hyH : y ∈ ((setX G w vs ∪ setW G w).erase vs) := (mem_insert.1 hy).resolve_left fun e => hadj.ne e.symm
      rcases mem_union.1 (mem_erase.1 hyH).2 with h | h
      · exact absurd hadj (mem_setX.1 h).2.2
      · exact mem_setY.2 ⟨mem_setW.1 h, hadj⟩
    · intro hy
      refine ⟨mem_insert_self _ _, mem_insert_of_mem (hYHV hy), (mem_setY.1 hy).2, ?_⟩
      cases hs : D.side y
      · have := D.hR y (mem_insert_of_mem (hYHV hy)) hs
        exact Or.inr (Or.inl ⟨hsvs, rfl, by omega⟩)
      · exact Or.inl ⟨hsvs, rfl⟩
  -- the pairing
  have hA2 : 2 * #((setY G w vs) \ (setY G w vs).filter fun y => D.side y = true ∨ y ∈ unm M ((setX G w vs ∪ setW G w).erase vs)) ≤ #(setY G w vs) := by
    set A := (setY G w vs).filter fun y => D.side y = true ∨ y ∈ unm M ((setX G w vs ∪ setW G w).erase vs)
    have hAY : A ⊆ (setY G w vs) := filter_subset _ _
    have hcov : ∀ a ∈ (setY G w vs) \ A, a ∈ cover M := fun a ha => by
      by_contra hc
      exact (mem_sdiff.1 ha).2 (mem_filter.2 ⟨(mem_sdiff.1 ha).1,
        Or.inr (mem_unm.2 ⟨hYHV (mem_sdiff.1 ha).1, hc⟩)⟩)
    have hsub : ((setY G w vs) \ A).image (partner M) ⊆ A := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hz
      have hyY := (mem_sdiff.1 hy).1
      have hyA := (mem_sdiff.1 hy).2
      have hyH := hYHV hyY
      have hc := hcov y hy
      have hyL : y ∉ leftM M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs) := fun h =>
        hyA (mem_filter.2 ⟨hyY, Or.inl ((hsideH y hyH).2 h)⟩)
      obtain ⟨h1, h2⟩ := Y_right (hM := hM) (hMS := hMS) hXYd hyY hyH hc hyL
      exact mem_filter.2 ⟨h1, Or.inl ((hsideH _ (partner_mem hMS hc)).2 h2)⟩
    have hinj : Set.InjOn (partner M) ((setY G w vs) \ A : Finset V) := by
      intro a ha b hb e
      have hca := hcov a ha
      have hcb := hcov b hb
      rw [← partner_partner hM hca, ← partner_partner hM hcb]
      exact congrArg (partner M) e
    have h1 := card_le_card hsub
    rw [card_image_of_injOn hinj] at h1
    have h2 := card_sdiff_add_card_eq_card hAY
    omega
  have hB2 : 2 * #((setX G w vs) \ (setX G w vs).filter fun x => D.side x = false) ≤ #(setX G w vs) := by
    set B := (setX G w vs).filter fun x => D.side x = false
    have hBX : B ⊆ (setX G w vs) := filter_subset _ _
    have hL : ∀ x ∈ (setX G w vs) \ B, x ∈ leftM M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs) := fun x hx => by
      have hxX := (mem_sdiff.1 hx).1
      have hxB := (mem_sdiff.1 hx).2
      have hs : D.side x = true := by
        by_contra h
        exact hxB (mem_filter.2 ⟨hxX, by simpa using h⟩)
      exact (hsideH x (hXHV hxX)).1 hs
    have hsub : ((setX G w vs) \ B).image (partner M) ⊆ B := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
      have hxL := hL x hx
      obtain ⟨h1, h2⟩ := X_left (hM := hM) (mem_sdiff.1 hx).1 hxL
      have hpH := partner_mem hMS (mem_leftM.1 hxL).2.1
      refine mem_filter.2 ⟨h1, ?_⟩
      by_contra h
      exact h2 ((hsideH _ hpH).1 (by simpa using h))
    have hinj : Set.InjOn (partner M) ((setX G w vs) \ B : Finset V) := by
      intro a ha b hb e
      have hca := (mem_leftM.1 (hL a ha)).2.1
      have hcb := (mem_leftM.1 (hL b hb)).2.1
      rw [← partner_partner hM hca, ← partner_partner hM hcb]
      exact congrArg (partner M) e
    have h1 := card_le_card hsub
    rw [card_image_of_injOn hinj] at h1
    have h2 := card_sdiff_add_card_eq_card hBX
    omega
  obtain ⟨σ, Bad, hBadY, hBad2, hσX, hσinj, hgood⟩ := exists_pairing (setX G w vs) (setY G w vs) _ _ hXY
    (filter_subset _ _) (filter_subset _ _) hA2 hB2
  have hσsurj : ∀ x ∈ (setX G w vs), ∃ y ∈ (setY G w vs), σ y = x := by
    have himg : (setY G w vs).image σ = (setX G w vs) := by
      apply eq_of_subset_of_card_le
      · intro x hx; obtain ⟨y, hy, rfl⟩ := mem_image.1 hx; exact hσX y hy
      · rw [card_image_of_injOn (fun a ha b hb e => hσinj a ha b hb e), hXY]
    intro x hx
    rw [← himg] at hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    exact ⟨y, hy, rfl⟩
  -- the good pairs leave `σ y` uncovered in the class of `v* y`
  have hgood' : ∀ y ∈ (setY G w vs), y ∉ Bad → σ y ∉ D.cls G (D.stair vs y) := by
    intro y hy hb
    obtain ⟨hyA, hσB⟩ := hgood y hy hb
    have hyA' := (mem_filter.1 hyA).2
    have hxX := (mem_filter.1 hσB).1
    have hxR := (mem_filter.1 hσB).2
    refine D.not_cls_of_good (mem_insert_self _ _) hsvs hivs ((hEvs y).2 hy)
      (mem_insert_of_mem (hXHV hxX)) hxR ?_
    rcases hyA' with h | h
    · exact Or.inl h
    · right
      by_cases hcx : σ y ∈ cover M
      · have h1 := idx_matched_pos (M := M) (X := (setX G w vs)) (Y := (setY G w vs)) hvsHV (hXHV hxX) hcx
        have h2 := idx_unm_le (M := M) (X := (setX G w vs)) (Y := (setY G w vs)) hvsHV h
        rw [hidx, hidx]; omega
      · have := idx_unm_lt (M := M) hvsHV hXYd h hy (mem_unm.2 ⟨hXHV hxX, hcx⟩) hxX
        rw [hidx, hidx]; exact this
  -- the bad vertices, enumerated
  obtain ⟨e, he⟩ : ∃ e, e = #Bad := ⟨_, rfl⟩
  let β : ℕ → V := fun j => if h : j < #Bad then (Bad.equivFin.symm ⟨j, h⟩ : V) else vs
  let βi : V → ℕ := fun y => if h : y ∈ Bad then (Bad.equivFin ⟨y, h⟩ : ℕ) else 0
  have hβ : ∀ j < e, β j ∈ Bad := fun j hj => by
    have hj' : j < #Bad := he ▸ hj
    simp only [β, dif_pos hj']; exact (Bad.equivFin.symm ⟨j, hj'⟩).2
  have hβi : ∀ y ∈ Bad, βi y < e ∧ β (βi y) = y := fun y hy => by
    have h1 : βi y = (Bad.equivFin ⟨y, hy⟩ : ℕ) := by simp only [βi, dif_pos hy]
    refine ⟨by rw [h1, he]; exact (Bad.equivFin ⟨y, hy⟩).isLt, ?_⟩
    simp only [β, h1, dif_pos (Bad.equivFin ⟨y, hy⟩).isLt]
    simp
  have hββi : ∀ j < e, βi (β j) = j := fun j hj => by
    have hj' : j < #Bad := he ▸ hj
    have hb := hβ j hj
    simp only [βi, dif_pos hb]
    simp only [β, dif_pos hj']
    simp
  -- the steps
  obtain ⟨q, hq⟩ : ∃ q, q = #((setX G w vs ∪ setW G w).erase vs) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = q + e := ⟨_, rfl⟩
  let C : ℕ → SimpleGraph V := fun k =>
    if k < q then stairClass D G vs Bad ((k : ℤ) + 1)
    else if k < N then SimpleGraph.fromEdgeSet {s(vs, β (k - q))} else ⊥
  let mis : ℕ → V := fun k =>
    if k < q then
      (if h : ∃ y, y ∈ (setY G w vs) ∧ y ∉ Bad ∧ D.stair vs y = (k : ℤ) + 1 then σ h.choose else vs)
    else if k < N then σ (β (k - q)) else vs
  have hC1 : ∀ k < q, C k = stairClass D G vs Bad ((k : ℤ) + 1) := fun k hk => by
    simp only [C, if_pos hk]
  have hC2 : ∀ k, q ≤ k → k < N → C k = SimpleGraph.fromEdgeSet {s(vs, β (k - q))} :=
    fun k h1 h2 => by simp only [C, if_neg (show ¬ k < q by omega), if_pos h2]
  have hC3 : ∀ k, N ≤ k → C k = ⊥ := fun k h => by
    simp only [C, if_neg (show ¬ k < q by omega), if_neg (show ¬ k < N by omega)]
  have hedge : ∀ k, q ≤ k → k < N → ∀ a b,
      (C k).Adj a b ↔ s(a, b) = s(vs, β (k - q)) ∧ a ≠ b :=
    fun k h1 h2 a b => by rw [hC2 k h1 h2, fromEdgeSet_adj, Set.mem_singleton_iff]
  have hβY : ∀ j < e, β j ∈ (setY G w vs) := fun j hj => hBadY (hβ j hj)
  -- the missed vertices
  have hstair : ∀ y ∈ (setY G w vs), 1 ≤ D.stair vs y ∧ D.stair vs y ≤ q := fun y hy =>
    ⟨D.stair_pos ((hEvs y).2 hy), by have := D.stair_le ((hEvs y).2 hy); omega⟩
  let stepOf : V → ℕ := fun y => if y ∈ Bad then q + βi y else (D.stair vs y - 1).toNat
  have hmis_mem : ∀ k, mis k ∈ (setX G w vs) ∨ mis k = vs := by
    intro k
    simp only [mis]
    split_ifs with h1 h2 h3
    · exact Or.inl (hσX _ h2.choose_spec.1)
    · exact Or.inr rfl
    · exact Or.inl (hσX _ (hβY _ (by omega)))
    · exact Or.inr rfl
  have hmis_eq : ∀ y ∈ (setY G w vs), ∀ k, mis k = σ y ↔ k = stepOf y := by
    intro y hy k
    have hσy := hσX y hy
    have hσne : σ y ≠ vs := fun h => (mem_setX.1 (h ▸ hσy)).2.1 rfl
    simp only [mis, stepOf]
    constructor
    · intro hk
      split_ifs at hk with h1 h2 h3
      · have hy' := hσinj _ h2.choose_spec.1 y hy hk
        have hb := h2.choose_spec.2.1
        have hst := h2.choose_spec.2.2
        rw [hy'] at hb hst
        rw [if_neg hb, hst]; omega
      · exact absurd hk.symm hσne
      · have hj : k - q < e := by omega
        have hy' := hσinj _ (hβY _ hj) y hy hk
        rw [← hy', if_pos (hβ _ hj), hββi _ hj]; omega
      · exact absurd hk.symm hσne
    · intro hk
      by_cases hb : y ∈ Bad
      · rw [if_pos hb] at hk
        obtain ⟨hlt, hβy⟩ := hβi y hb
        rw [if_neg (by omega), if_pos (by omega), show k - q = βi y by omega, hβy]
      · rw [if_neg hb] at hk
        have hs := hstair y hy
        have hkq : k < q := by omega
        have hex : ∃ y', y' ∈ (setY G w vs) ∧ y' ∉ Bad ∧ D.stair vs y' = (k : ℤ) + 1 :=
          ⟨y, hy, hb, by omega⟩
        rw [if_pos hkq, dif_pos hex]
        have hy' := hex.choose_spec.1
        have hst' := hex.choose_spec.2.2
        congr 1
        refine D.stair_inj ((hEvs _).2 hy') ((hEvs _).2 hy) ?_
        rw [hst']; omega
  have hstep_lt : ∀ y ∈ (setY G w vs), stepOf y < N := fun y hy => by
    simp only [stepOf]
    split_ifs with hb
    · have := (hβi y hb).1; omega
    · have := hstair y hy; omega
  -- the factors
  have hdegM : ∀ v, M.degree v ≤ 1 := fun v => by
    by_cases hv : v ∈ cover M
    · rw [degree_eq_one_of_matching hM hv]
    · rw [degree_eq_zero_of_not_cover hv]; exact zero_le_one
  have hdegG' : ∀ v, v ≠ w → (keepAt G w ∅).degree v + (if G.Adj v w then 1 else 0) = d :=
    fun v hv => by rw [degree_keepAt_empty_add G w hv, hreg]
  have hCle : ∀ k, C k ≤ (keepAt G w ∅) \ M := by
    intro k a b hab
    rcases lt_or_ge k q with hk | hk
    · rw [hC1 k hk] at hab
      have hE := hab.1
      have ha := hE.1
      have hb := hE.2.1
      have hGab := hE.2.2.1
      exact ⟨(keepAt_empty_adj G w).2 ⟨hGab, fun h => hwHS (h ▸ ha), fun h => hwHS (h ▸ hb)⟩,
        fun hM' => hMnotE a b hM' hE⟩
    · rcases lt_or_ge k N with hk' | hk'
      · obtain ⟨he', hab'⟩ := (hedge k hk hk' a b).1 hab
        have hj : k - q < e := by omega
        have hGv : G.Adj vs (β (k - q)) := (mem_setY.1 (hβY _ hj)).2
        have hbH := hYHV (hβY _ hj)
        rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨(keepAt_empty_adj G w).2 ⟨hGv, hvsw, fun h => hwHV (h ▸ hbH)⟩, fun h => ?_⟩
          exact hvsHV (hMS _ _ h).1
        · refine ⟨(keepAt_empty_adj G w).2 ⟨hGv.symm, fun h => hwHV (h ▸ hbH), hvsw⟩,
            fun h => ?_⟩
          exact hvsHV (hMS _ _ h).2
      · rw [hC3 k hk'] at hab; exact absurd hab (by simp)
  have hCm : ∀ k, IsMatchingGraph (C k) := by
    intro k
    rcases lt_or_ge k q with hk | hk
    · rw [hC1 k hk]; exact stairClass_matching _
    · rcases lt_or_ge k N with hk' | hk'
      · intro v a b ha hb
        obtain ⟨h1, h2⟩ := (hedge k hk hk' v a).1 ha
        obtain ⟨h3, h4⟩ := (hedge k hk hk' v b).1 hb
        rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases Sym2.eq_iff.1 h3 with ⟨h5, rfl⟩ | ⟨h5, rfl⟩ <;>
          first
          | rfl
          | exact absurd h5 h2
          | exact absurd h5.symm h2
          | exact absurd h5 h4
          | exact absurd h5.symm h4
      · rw [hC3 k hk']; intro v a b h; exact absurd h (by simp)
  have hcov2 : ∀ k, q ≤ k → k < N → cover (C k) ⊆ {vs, β (k - q)} := by
    intro k h1 h2 v hv
    obtain ⟨u, hu⟩ := mem_cover.1 hv
    obtain ⟨h3, -⟩ := (hedge k h1 h2 v u).1 hu
    rcases Sym2.eq_iff.1 h3 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hCb : ∀ k < N, 2 * n + #(cover (C k)) + 2 * k ≤ 2 * (d - 2) := by
    intro k hk
    rcases lt_or_ge k q with hkq | hkq
    · rw [hC1 k hkq]
      have h1 := card_le_card (cover_stairClass_subset (D := D) (G := G) (vs := vs) (Bad := Bad)
        ((k : ℤ) + 1))
      have h2 := D.card_cls_le (G := G) (i := (k : ℤ) + 1) (by omega)
      omega
    · have h1 := card_le_card (hcov2 k hkq hk)
      have h2 : #({vs, β (k - q)} : Finset V) ≤ 2 := card_le_two
      omega
  have hmw : ∀ k, mis k ≠ w := fun k h => by
    rcases hmis_mem k with h' | h'
    · rw [h] at h'; exact (mem_setX.1 h').1.ne rfl
    · exact hwv (h.symm.trans h')
  have hmC : ∀ k u, ¬ (C k).Adj (mis k) u := by
    intro k u hadj
    rcases lt_or_ge k q with hkq | hkq
    · rw [hC1 k hkq] at hadj
      by_cases hex : ∃ y, y ∈ (setY G w vs) ∧ y ∉ Bad ∧ D.stair vs y = (k : ℤ) + 1
      · have hmk : mis k = σ hex.choose := by simp only [mis, if_pos hkq, dif_pos hex]
        have hy := hex.choose_spec.1
        have hb := hex.choose_spec.2.1
        have hst := hex.choose_spec.2.2
        rw [hmk] at hadj
        apply hgood' _ hy hb
        rw [hst]
        exact (StairData.mem_cls _ _).2 ⟨hadj.1.1, u, hadj.1, hadj.2.1⟩
      · have hmk : mis k = vs := by simp only [mis, if_pos hkq, dif_neg hex]
        rw [hmk] at hadj
        obtain ⟨hE, hst, hb1, -⟩ := hadj
        have huY := (hEvs u).1 hE
        exact hex ⟨u, huY, fun hb => hb1 ⟨rfl, hb⟩, hst⟩
    · rcases lt_or_ge k N with hk' | hk'
      · have hmk : mis k = σ (β (k - q)) := by
          simp only [mis, if_neg (show ¬ k < q by omega), if_pos hk']
        rw [hmk] at hadj
        obtain ⟨h1, -⟩ := (hedge k hkq hk' _ u).1 hadj
        have hj : k - q < e := by omega
        have hxX := hσX _ (hβY _ hj)
        rcases Sym2.eq_iff.1 h1 with ⟨h2, -⟩ | ⟨h2, -⟩
        · exact (mem_setX.1 (h2 ▸ hxX)).2.1 rfl
        · exact Finset.disjoint_left.1 hXYd hxX (by rw [h2]; exact hβY _ hj)
      · rw [hC3 k hk'] at hadj; exact absurd hadj (by simp)
  obtain ⟨F, hF, hdisj, hCF⟩ := exists_factors_var ((keepAt G w ∅) \ M) (n := n) (N := N) (D₀ := d - 2)
    hcard w (fun u h => ((keepAt_empty_adj G w).1 h.1).2.1 rfl)
    (fun v hv => by
      have h1 := Plantholt.degree_sdiff_add _ hMG v
      have h2 := hdegM v
      have h3 := hdegG' v hv
      split_ifs at h3 <;> omega)
    C mis hCle hCm hCb hmw hmC
  -- facts about the factors
  have hFle : ∀ k < N, F k ≤ (keepAt G w ∅) := fun k hk => (hF k hk).le.trans sdiff_le
  have hFM : ∀ k < N, ∀ a b, (F k).Adj a b → ¬ M.Adj a b := fun k hk a b h =>
    ((hF k hk).le h).2
  have hdisjR : ∀ j ∈ range N, ∀ k ∈ range N, j ≠ k → Disjoint (F j) (F k) :=
    fun j hj k hk hjk => by
      rcases lt_or_gt_of_ne hjk with h | h
      · exact hdisj j k h (mem_range.1 hk)
      · exact (hdisj k j h (mem_range.1 hj)).symm
  have hmatch : ∀ k ∈ range N, IsMatchingGraph (F k) := fun k hk =>
    (hF k (mem_range.1 hk)).matching
  have hUle : (range N).sup F ≤ (keepAt G w ∅) := Finset.sup_le fun k hk => hFle k (mem_range.1 hk)
  -- every staircase edge is in some factor
  have hHedge : ∀ a b, D.Eplus G a b → ∃ j < N, (F j).Adj a b := by
    intro a b hE
    have key : ∀ y ∈ Bad, ∃ j < N, (F j).Adj vs y := by
      intro y hy
      obtain ⟨hlt, hβy⟩ := hβi y hy
      have hk1 : q ≤ q + βi y := by omega
      have hk2 : q + βi y < N := by omega
      have hCk : (C (q + βi y)).Adj vs y := by
        rw [hedge _ hk1 hk2, show q + βi y - q = βi y by omega, hβy]
        exact ⟨rfl, fun h => hvsHV (h ▸ hYHV (hBadY hy))⟩
      obtain ⟨j, hj, hj'⟩ := (finsetSup_adj _).1 (hCF _ hk2 hCk)
      exact ⟨j, by have := mem_range.1 hj; omega, hj'⟩
    by_cases hb1 : a = vs ∧ b ∈ Bad
    · obtain ⟨rfl, hb⟩ := hb1; exact key b hb
    by_cases hb2 : b = vs ∧ a ∈ Bad
    · obtain ⟨rfl, ha⟩ := hb2
      obtain ⟨j, hj, hj'⟩ := key a ha
      exact ⟨j, hj, hj'.symm⟩
    have h1 := D.stair_pos hE
    have h2 := D.stair_le hE
    obtain ⟨k, hk⟩ : ∃ k, k = (D.stair a b - 1).toNat := ⟨_, rfl⟩
    have hkq : k < q := by omega
    have hCk : (C k).Adj a b := by
      rw [hC1 k hkq]
      exact ⟨hE, by omega, hb1, hb2⟩
    obtain ⟨j, hj, hj'⟩ := (finsetSup_adj _).1 (hCF k (by omega) hCk)
    exact ⟨j, by have := mem_range.1 hj; omega, hj'⟩
  -- the missed counts
  have hcntX : ∀ x ∈ (setX G w vs), ∀ T ⊆ range N, (∀ y ∈ (setY G w vs), σ y = x → stepOf y ∈ T) →
      #(T.filter fun k => x ≠ w ∧ x ≠ mis k) + 1 = #T := fun x hx T hT hst => by
    obtain ⟨y, hy, rfl⟩ := hσsurj x hx
    have : T.filter (fun k => σ y ≠ w ∧ σ y ≠ mis k) = T.erase (stepOf y) := by
      ext k
      simp only [mem_filter, mem_erase]
      have hxw : σ y ≠ w := (mem_setX.1 (hσX y hy)).1.ne'
      have key : σ y ≠ mis k ↔ k ≠ stepOf y := by
        rw [ne_comm, Ne, hmis_eq y hy k]
      rw [key]
      tauto
    rw [this, card_erase_add_one (hst y hy rfl)]
  have hcntO : ∀ v, v ≠ w → v ∉ (setX G w vs) → v ≠ vs → ∀ T : Finset ℕ,
      #(T.filter fun k => v ≠ w ∧ v ≠ mis k) = #T := fun v hvw hvX hvs T => by
    congr 1
    rw [filter_eq_self]
    intro k _
    refine ⟨hvw, fun he' => ?_⟩
    rcases hmis_mem k with h | h
    · exact hvX (he' ▸ h)
    · exact hvs (he'.trans h)
  have hNd : N + 2 ≤ d := by omega
  have hXadj : ∀ x ∈ (setX G w vs), G.Adj x w := fun x hx => (mem_setX.1 hx).1.symm
  have hnotW : ∀ v, v ≠ w → v ∉ (setW G w) → G.Adj v w := fun v hv hW => by
    by_contra h; exact hW (mem_setW.2 ⟨hv, fun h' => h h'.symm⟩)
  have hstepX : ∀ x ∈ (setX G w vs), ∀ y ∈ (setY G w vs), σ y = x → stepOf y ∈ range N :=
    fun x _ y hy _ => mem_range.2 (hstep_lt y hy)
  -- Phase 1: the core
  obtain ⟨U, hU⟩ : ∃ U, U = (range N).sup F := ⟨_, rfl⟩
  have hUle' : U ≤ (keepAt G w ∅) := hU ▸ hUle
  have hdegU : ∀ v, U.degree v = #((range N).filter fun k => v ≠ w ∧ v ≠ mis k) := fun v => by
    subst hU; exact degree_finsetSup_factors hF hdisjR subset_rfl v
  have hdegGU : ∀ v, ((keepAt G w ∅) \ U).degree v + U.degree v = (keepAt G w ∅).degree v :=
    fun v => Plantholt.degree_sdiff_add _ hUle' v
  have hdeg1 : ∀ v, (keepAt ((keepAt G w ∅) \ U) vs ∅).degree v ≤ ((keepAt G w ∅) \ U).degree v :=
    fun v => degree_le_of_le (keepAt_le _ vs ∅)
  have hmax1 : ∀ v, (keepAt ((keepAt G w ∅) \ U) vs ∅).degree v ≤ d - N := by
    intro v
    have h1 := hdeg1 v
    have h2 := hdegGU v
    have h3 := hdegU v
    by_cases hvw : v = w
    · subst hvw
      have := degree_keepAt_empty_self G v
      omega
    have h4 := hdegG' v hvw
    by_cases hvX : v ∈ (setX G w vs)
    · have h5 := hcntX v hvX _ subset_rfl (hstepX v hvX)
      rw [card_range] at h5
      rw [if_pos (hXadj v hvX)] at h4
      omega
    · by_cases hvs : v = vs
      · subst hvs; rw [degree_keepAt_empty_self]; exact Nat.zero_le _
      · have h5 := hcntO v hvw hvX hvs (range N)
        rw [card_range] at h5
        split_ifs at h4 <;> omega
  have hsmall1 : ∀ v, v ∉ ((setX G w vs ∪ setW G w).erase vs) → (keepAt ((keepAt G w ∅) \ U) vs ∅).degree v < d - N := by
    intro v hvH
    by_cases hvs : v = vs
    · subst hvs; rw [degree_keepAt_empty_self]; omega
    have h1 := hdeg1 v
    have h2 := hdegGU v
    have h3 := hdegU v
    by_cases hvw : v = w
    · subst hvw
      have := degree_keepAt_empty_self G v
      omega
    have hvX : v ∉ (setX G w vs) := fun h => hvH (hXHV h)
    have hvW : v ∉ (setW G w) := fun h => hvH (mem_erase.2 ⟨hvs, mem_union_right _ h⟩)
    have h4 := hdegG' v hvw
    rw [if_pos (hnotW v hvw hvW)] at h4
    have h5 := hcntO v hvw hvX hvs (range N)
    rw [card_range] at h5
    omega
  have hG1col : (keepAt ((keepAt G w ∅) \ U) vs ∅).lineGraph.Colorable (d - N) := by
    refine core_colorable D (subset_insert vs _) M _ hmax1 hsmall1 ?_ hM hMside ?_ ?_ ?_ ?_ ?_
    · -- the matching survives
      intro a b hab
      obtain ⟨ha, hb⟩ := hMS a b hab
      refine (keepAt_empty_adj _ vs).2 ⟨⟨hMG hab, fun hU' => ?_⟩, fun h => hvsHV (h ▸ ha),
        fun h => hvsHV (h ▸ hb)⟩
      rw [hU] at hU'
      obtain ⟨k, hk, hk'⟩ := (finsetSup_adj _).1 hU'
      exact hFM k (mem_range.1 hk) a b hk' hab
    · intro l r hl hr hsl hsr hlr
      have hlL := (hsideH l hl).1 hsl
      have hrL : r ∉ leftM M (setX G w vs) (setY G w vs) ((setX G w vs ∪ setW G w).erase vs) := fun h => by
        rw [(hsideH r hr).2 h] at hsr; exact absurd hsr (by simp)
      exact adj_of_idx_eq (hM := hM) (hMS := hMS) hvsHV hlL hr hrL (by rw [← hidx, ← hidx]; exact hlr)
    · intro v hv hs hpos
      by_contra hc
      have := idx_unm_le (M := M) (X := (setX G w vs)) (Y := (setY G w vs)) hvsHV (mem_unm.2 ⟨hv, hc⟩)
      rw [← hidx] at this
      omega
    · intro v hv hc
      refine ⟨?_, by rw [hidx]; exact idx_unm_le hvsHV (mem_unm.2 ⟨hv, hc⟩)⟩
      by_contra h
      have hL := (hsideH v hv).1 (by simpa using h)
      exact hc (mem_leftM.1 hL).2.1
    · intro u v hu hv huv
      have h1 := keepAt_le _ vs ∅ huv
      exact hMmax u v hu hv h1.1
    · intro u v hu hv huv
      have h1 := keepAt_le _ vs ∅ huv
      have hnE : ¬ D.Eplus G u v := by
        intro hE
        obtain ⟨j, hj, hj'⟩ := hHedge u v hE
        apply h1.2
        rw [hU]
        exact (finsetSup_adj _).2 ⟨j, mem_range.2 hj, hj'⟩
      have hGuv : G.Adj u v := ((keepAt_empty_adj G w).1 h1.1).1
      have huS : u ∈ insert vs ((setX G w vs ∪ setW G w).erase vs) := mem_insert_of_mem hu
      have hvS : v ∈ insert vs ((setX G w vs ∪ setW G w).erase vs) := mem_insert_of_mem hv
      cases hsu : D.side u <;> cases hsv : D.side v
      · exact Or.inl ⟨rfl, rfl⟩
      · right; right
        refine ⟨rfl, rfl, ?_⟩
        by_contra hlt
        exact hnE ⟨huS, hvS, hGuv, Or.inr (Or.inr ⟨hsu, hsv, by omega⟩)⟩
      · right; left
        refine ⟨rfl, rfl, ?_⟩
        by_contra hlt
        exact hnE ⟨huS, hvS, hGuv, Or.inr (Or.inl ⟨hsu, hsv, by omega⟩)⟩
      · exact absurd ⟨huS, hvS, hGuv, Or.inl ⟨hsu, hsv⟩⟩ hnE
  -- Phase 2: add the factors missing `v*`
  obtain ⟨J, hJ⟩ : ∃ J, J = (range N).filter fun k => mis k = vs := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (range N).filter fun k => ¬ mis k = vs := ⟨_, rfl⟩
  have hJsub : J ⊆ range N := hJ ▸ filter_subset _ _
  have hAsub : A ⊆ range N := hA ▸ filter_subset _ _
  have hAJ : #J + #A = N := by rw [hJ, hA, card_filter_add_card_filter_not, card_range]
  have hG2col : (keepAt ((keepAt G w ∅) \ U) vs ∅ ⊔ J.sup F).lineGraph.Colorable (d - N + #J) := by
    refine colorable_sup_family J (fun k hk => hmatch k (hJsub hk)) (fun k hk => ?_)
      (fun a ha b hb hab => hdisjR a (hJsub ha) b (hJsub hb) hab) hG1col
    have hFU : F k ≤ U := hU ▸ le_sup (f := F) (hJsub hk)
    exact (disjoint_sdiff_self_left.mono_left (keepAt_le _ vs ∅)).mono_right hFU
  -- Phase 3
  have hAle : A.sup F ≤ (keepAt G w ∅) := Finset.sup_le fun k hk => hFle k (mem_range.1 (hAsub hk))
  have heq : keepAt ((keepAt G w ∅) \ A.sup F) vs ∅ = keepAt ((keepAt G w ∅) \ U) vs ∅ ⊔ J.sup F := by
    ext a b
    rw [keepAt_empty_adj, sup_adj, keepAt_empty_adj, sdiff_adj, sdiff_adj, finsetSup_adj,
      finsetSup_adj, hU, finsetSup_adj]
    constructor
    · rintro ⟨⟨hab, hA'⟩, ha, hb⟩
      by_cases hU' : ∃ k ∈ range N, (F k).Adj a b
      · obtain ⟨k, hk, hk'⟩ := hU'
        have hmk : mis k = vs := by
          by_contra hne
          exact hA' ⟨k, by rw [hA]; exact mem_filter.2 ⟨hk, hne⟩, hk'⟩
        exact Or.inr ⟨k, by rw [hJ]; exact mem_filter.2 ⟨hk, hmk⟩, hk'⟩
      · exact Or.inl ⟨⟨hab, hU'⟩, ha, hb⟩
    · rintro (⟨⟨hab, hU'⟩, ha, hb⟩ | ⟨k, hk, hk'⟩)
      · exact ⟨⟨hab, fun ⟨j, hj, hj'⟩ => hU' ⟨j, hAsub hj, hj'⟩⟩, ha, hb⟩
      · have hkN := mem_range.1 (hJsub hk)
        have hmk : mis k = vs := by rw [hJ] at hk; exact (mem_filter.1 hk).2
        refine ⟨⟨hFle k hkN hk', fun ⟨j, hj, hj'⟩ => ?_⟩, fun ha => ?_, fun hb => ?_⟩
        · have hjk : j ≠ k := fun h => by
            rw [hA] at hj; exact (mem_filter.1 hj).2 (h ▸ hmk)
          exact (disjoint_iff_inf_le.1 (hdisjR j (hAsub hj) k (hJsub hk) hjk)) ⟨hj', hk'⟩
        · exact (hF k hkN).miss_m b (by rw [hmk, ← ha]; exact hk')
        · exact (hF k hkN).miss_m a (by rw [hmk, ← hb]; exact hk'.symm)
  have hG3col : (keepAt ((keepAt G w ∅) \ A.sup F) vs ∅).lineGraph.Colorable (d - #A) := by
    rw [heq]
    have : d - N + #J = d - #A := by omega
    rw [← this]; exact hG2col
  -- Phase 4: re-insert `v*`
  have hdegA : ∀ v, (A.sup F).degree v = #(A.filter fun k => v ≠ w ∧ v ≠ mis k) :=
    fun v => degree_finsetSup_factors hF hdisjR hAsub v
  have hdegG3 : ∀ v, ((keepAt G w ∅) \ A.sup F).degree v + (A.sup F).degree v = (keepAt G w ∅).degree v :=
    fun v => Plantholt.degree_sdiff_add _ hAle v
  have hstepA : ∀ x ∈ (setX G w vs), ∀ y ∈ (setY G w vs), σ y = x → stepOf y ∈ A := fun x hx y hy hxy => by
    rw [hA]
    refine mem_filter.2 ⟨mem_range.2 (hstep_lt y hy), fun h => ?_⟩
    have := (hmis_eq y hy (stepOf y)).2 rfl
    rw [h] at this
    exact (mem_setX.1 (this ▸ hσX y hy)).2.1 rfl
  have hAN : #A ≤ N := by omega
  have hmax3 : ∀ v, ((keepAt G w ∅) \ A.sup F).degree v ≤ d - #A := by
    intro v
    have h1 := hdegG3 v
    have h2 := hdegA v
    by_cases hvw : v = w
    · subst hvw
      have := degree_keepAt_empty_self G v
      omega
    have h4 := hdegG' v hvw
    by_cases hvX : v ∈ (setX G w vs)
    · have h5 := hcntX v hvX A hAsub (hstepA v hvX)
      rw [if_pos (hXadj v hvX)] at h4
      omega
    · by_cases hvs : v = vs
      · subst hvs
        have h5 : A.filter (fun k => v ≠ w ∧ v ≠ mis k) = A := by
          rw [filter_eq_self]
          intro k hk
          rw [hA] at hk
          exact ⟨hvw, fun he' => (mem_filter.1 hk).2 he'.symm⟩
        rw [h5] at h2
        split_ifs at h4 <;> omega
      · have h5 := hcntO v hvw hvX hvs A
        split_ifs at h4 <;> omega
  have hx3 : ∀ z, ((keepAt G w ∅) \ A.sup F).Adj vs z → ((keepAt G w ∅) \ A.sup F).degree z < d - #A := by
    intro z hz
    have hG'z : (keepAt G w ∅).Adj vs z := hz.1
    obtain ⟨hGz, hvsw', hzw⟩ := (keepAt_empty_adj G w).1 hG'z
    have hzX : z ∉ (setX G w vs) := fun h => (mem_setX.1 h).2.2 hGz
    have hzs : z ≠ vs := hGz.ne'
    have hzW : z ∉ (setW G w) := by
      intro hzW
      have hzY : z ∈ (setY G w vs) := mem_setY.2 ⟨mem_setW.1 hzW, hGz⟩
      obtain ⟨j, hj, hj'⟩ := hHedge vs z ((hEvs z).2 hzY)
      have hmj : ¬ mis j = vs := fun h => (hF j hj).miss_m z (by rw [h]; exact hj')
      exact hz.2 ((finsetSup_adj _).2 ⟨j, by rw [hA]; exact mem_filter.2 ⟨mem_range.2 hj, hmj⟩,
        hj'⟩)
    have h1 := hdegG3 z
    have h2 := hdegA z
    have h4 := hdegG' z hzw
    rw [if_pos (hnotW z hzw hzW)] at h4
    have h5 := hcntO z hzw hzX hzs A
    omega
  have hG3full := colorable_of_add_vertex _ hmax3 vs hx3 hG3col
  -- Phase 5: add the factors through `v*`
  have hG'col : (keepAt G w ∅).lineGraph.Colorable d := by
    have := colorable_sup_family (B := (keepAt G w ∅) \ A.sup F) A
      (fun k hk => hmatch k (hAsub hk))
      (fun k hk => disjoint_sdiff_self_left.mono_right (le_sup (f := F) hk))
      (fun a ha b hb hab => hdisjR a (hAsub ha) b (hAsub hb) hab) hG3full
    rw [sdiff_sup_cancel hAle, Nat.sub_add_cancel (by omega)] at this
    exact this
  -- Phase 6: re-insert `w`
  exact colorable_of_regular_keepAt G ⟨n, by omega⟩ hreg w hG'col

end OneFactor
