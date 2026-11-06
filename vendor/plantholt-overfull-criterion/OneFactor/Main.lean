/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Sup

/-!
# Regular graphs of high degree are 1-factorizable (a Chetwynd–Hilton type bound)

**Theorem** (`colorable_of_regular`). A `d`-regular graph on `2n` vertices with `11 n ≤ 6 d`
(degree at least `11/12` of the order) is `d`-edge-colourable, i.e. 1-factorizable.

The proof follows Chetwynd–Hilton, *1-factorizing regular graphs of high degree — an improved
bound* (Discrete Math. 75 (1989)), §4, with the round-robin classes on the labelled vertices in
place of the staircase matchings (see `NOTES_CH.md`): remove a vertex `w`, peel off `N`
edge-disjoint near 1-factors through the classes, colour the rest by Fournier's theorem, add back
the factors that miss `v*`, re-insert `v*`, add the remaining factors, and re-insert `w`.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w vs : V}

theorem missed_mem_X_or (k : ℕ) : missed G w vs k ∈ setX G w vs ∨ missed G w vs k = vs := by
  unfold missed
  split_ifs with h
  · exact Or.inl h.choose_spec.1
  · exact Or.inr rfl

theorem missed_eq_vs_iff (k : ℕ) :
    missed G w vs k = vs ↔ ¬ ∃ x ∈ setX G w vs, label G w vs x = k := by
  unfold missed
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    exact fun e => vs_notMem_X (e ▸ h.choose_spec.1)
  · simp [h]

theorem missed_eq_iff (hXY : #(setX G w vs) = #(setY G w vs)) {x : V} (hx : x ∈ setX G w vs)
    (k : ℕ) : missed G w vs k = x ↔ k = label G w vs x := by
  unfold missed
  split_ifs with h
  · constructor
    · rintro rfl; exact h.choose_spec.2.symm
    · rintro rfl
      exact label_injOn hXY (mem_setH.2 (Or.inr (Or.inl h.choose_spec.1)))
        (mem_setH.2 (Or.inr (Or.inl hx))) h.choose_spec.2
  · constructor
    · rintro rfl; exact absurd hx vs_notMem_X
    · rintro rfl; exact absurd ⟨x, hx, rfl⟩ h

theorem w_notMem_H (hwv : w ≠ vs) : w ∉ setH G w vs := by
  rw [mem_setH]
  rintro (h | h | h | h)
  · exact hwv h
  · exact (mem_setX.1 h).1.ne rfl
  · exact (mem_setY.1 h).1.1 rfl
  · exact (mem_setP.1 h).1.1 rfl

theorem degree_finsetSup_factors {F : ℕ → SimpleGraph V} {N : ℕ} {G' : SimpleGraph V}
    {m : ℕ → V} (hF : ∀ k < N, IsFactor G' w (m k) (F k))
    (hdisj : ∀ j ∈ range N, ∀ k ∈ range N, j ≠ k → Disjoint (F j) (F k))
    {T : Finset ℕ} (hT : T ⊆ range N) (v : V) :
    (T.sup F).degree v = #(T.filter fun k => v ≠ w ∧ v ≠ m k) := by
  rw [degree_finsetSup T (fun a ha b hb hab => hdisj a (hT ha) b (hT hb) hab), card_filter]
  exact sum_congr rfl fun k hk => (hF k (mem_range.1 (hT hk))).degree v

/-- **Regular graphs of degree at least `11/12` of the (even) order are 1-factorizable.** -/
theorem colorable_of_regular {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : ∀ v, G.degree v = d) (hd : 11 * n ≤ 6 * d) : G.lineGraph.Colorable d := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.1 (by omega)
    exact colorable_of_full_indep _ G le_rfl (fun v => (hreg v).le) fun u => isEmptyElim u
  haveI : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨w⟩ := ‹Nonempty V›
  obtain ⟨vs, hvsw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) w
  have hwv : w ≠ vs := Ne.symm hvsw
  have hXY := card_X_eq_card_Y (G := G) hreg hwv
  have hr : #(setW G w) + d + 1 = 2 * n := by rw [← hcard]; exact card_nonNbr G hreg w
  have hYP : #(setY G w vs) + #(setP G w vs) ≤ #(setW G w) := by
    rw [← card_union_of_disjoint]
    · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    · rw [Finset.disjoint_left]; intro u h1 h2; exact Y_notMem_P h1 h2
  have hH : #(setH G w vs) ≤ 1 + #(setX G w vs) + #(setW G w) := by
    unfold setH
    have := card_union_le (setX G w vs) (setW G w)
    have := card_insert_le vs (setX G w vs ∪ setW G w)
    omega
  have hNdef : modN G w vs = 4 * #(setX G w vs) + 2 * #(setP G w vs) + 1 := rfl
  haveI : NeZero (modN G w vs) := ⟨by omega⟩
  have hwH := w_notMem_H (G := G) hwv
  -- the near 1-factors
  let C : ℕ → SimpleGraph V := fun k => if k < modN G w vs then classGraph G w vs k else ⊥
  have hCk : ∀ k < modN G w vs, C k = classGraph G w vs k := fun k hk => if_pos hk
  obtain ⟨F, hF, hdisj, hCF⟩ := exists_factors (keepAt G w ∅) (n := n) (N := modN G w vs)
    (b := #(setW G w)) (D₀ := d - 1) hcard w
    (fun u h => ((keepAt_empty_adj G w).1 h).2.1 rfl)
    (fun v hv => by
      have := degree_keepAt_empty_add G w hv
      rw [hreg] at this
      split_ifs at this <;> omega)
    C (missed G w vs)
    (fun k => by
      by_cases hk : k < modN G w vs
      · rw [hCk k hk]; exact fun a b h => h.1
      · simp only [C, if_neg hk]; exact bot_le)
    (fun k => by
      by_cases hk : k < modN G w vs
      · rw [hCk k hk]; exact classGraph_matching hXY k
      · simp only [C, if_neg hk]; intro v a b h; exact absurd h (by simp))
    (fun k => by
      by_cases hk : k < modN G w vs
      · rw [hCk k hk]
        have hsub : cover (classGraph G w vs k) ⊆ (setH G w vs).erase (missed G w vs k) :=
          fun v hv => by
            obtain ⟨u, hu⟩ := mem_cover.1 hv
            refine mem_erase.2 ⟨fun he => ?_, hu.2.1⟩
            subst he; exact missed_not_adj hXY k hk u hu
        have h1 := card_le_card hsub
        rw [card_erase_of_mem (missed_mem hXY k)] at h1
        omega
      · simp only [C, if_neg hk]
        have : cover (⊥ : SimpleGraph V) = ∅ := by ext v; simp [mem_cover]
        rw [this, card_empty]; exact Nat.zero_le _)
    (fun k he => by have h := missed_mem hXY k; rw [he] at h; exact hwH h)
    (fun k u => by
      by_cases hk : k < modN G w vs
      · rw [hCk k hk]; exact missed_not_adj hXY k hk u
      · simp only [C, if_neg hk]; simp)
    (by omega)
  -- notation-free facts about the factors
  have hFle : ∀ k < modN G w vs, F k ≤ keepAt G w ∅ := fun k hk => (hF k hk).le
  have hdisjR : ∀ j ∈ range (modN G w vs), ∀ k ∈ range (modN G w vs), j ≠ k →
      Disjoint (F j) (F k) := fun j hj k hk hjk => by
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hdisj j k h (mem_range.1 hk)
    · exact (hdisj k j h (mem_range.1 hj)).symm
  have hmatch : ∀ k ∈ range (modN G w vs), IsMatchingGraph (F k) :=
    fun k hk => (hF k (mem_range.1 hk)).matching
  have hUle : (range (modN G w vs)).sup F ≤ keepAt G w ∅ :=
    Finset.sup_le fun k hk => hFle k (mem_range.1 hk)
  -- every edge inside `H` is in some factor
  have hHedge : ∀ a b, a ∈ setH G w vs → b ∈ setH G w vs → (keepAt G w ∅).Adj a b →
      ∃ j < modN G w vs, (F j).Adj a b := by
    intro a b ha hb hab
    set k := (cls G w vs a b).val
    have hk : k < modN G w vs := ZMod.val_lt _
    have hC : (C k).Adj a b := by
      rw [hCk k hk]; exact ⟨hab, ha, hb, by simp [k]⟩
    obtain ⟨j, hj, hj'⟩ := (finsetSup_adj _).1 (hCF k hk hC)
    exact ⟨j, by have := mem_range.1 hj; omega, hj'⟩
  -- degrees in `G − w`
  have hdegG' : ∀ v, v ≠ w → (keepAt G w ∅).degree v + (if G.Adj v w then 1 else 0) = d :=
    fun v hv => by rw [degree_keepAt_empty_add G w hv, hreg]
  have hdegw : (keepAt G w ∅).degree w = 0 := degree_keepAt_empty_self G w
  -- the factors miss: `x ∈ X` exactly once, other vertices `≠ v*` never
  have hcntX : ∀ x ∈ setX G w vs, ∀ T ⊆ range (modN G w vs), label G w vs x ∈ T →
      #(T.filter fun k => x ≠ w ∧ x ≠ missed G w vs k) + 1 = #T := fun x hx T hT hlT => by
    have : T.filter (fun k => x ≠ w ∧ x ≠ missed G w vs k) = T.erase (label G w vs x) := by
      ext k
      simp only [mem_filter, mem_erase]
      have hxw : x ≠ w := (mem_setX.1 hx).1.ne'
      have key : x ≠ missed G w vs k ↔ k ≠ label G w vs x := by
        rw [ne_comm, Ne, missed_eq_iff hXY hx]
      rw [key]
      tauto
    rw [this, card_erase_add_one hlT]
  have hcntO : ∀ v, v ≠ w → v ∉ setX G w vs → v ≠ vs → ∀ T : Finset ℕ,
      #(T.filter fun k => v ≠ w ∧ v ≠ missed G w vs k) = #T := fun v hvw hvX hvs T => by
    congr 1
    rw [filter_eq_self]
    intro k _
    refine ⟨hvw, fun he => ?_⟩
    rcases missed_mem_X_or (G := G) (w := w) (vs := vs) k with h | h
    · exact hvX (he ▸ h)
    · exact hvs (he.trans h)
  have hNd : modN G w vs < d := by omega
  have hlabX : ∀ x ∈ setX G w vs, label G w vs x < modN G w vs := fun x hx =>
    label_lt hXY (mem_setH.2 (Or.inr (Or.inl hx)))
  have hXadj : ∀ x ∈ setX G w vs, G.Adj x w := fun x hx => (mem_setX.1 hx).1.symm
  have hWH : ∀ v ∈ setW G w, v ∈ setH G w vs := fun v hv => mem_insert_of_mem (mem_union_right _ hv)
  have hXH : ∀ v ∈ setX G w vs, v ∈ setH G w vs := fun v hv => mem_insert_of_mem (mem_union_left _ hv)
  have hnotW : ∀ v, v ≠ w → v ∉ setW G w → G.Adj v w := fun v hv hW => by
    by_contra h; exact hW (mem_setW.2 ⟨hv, fun h' => h h'.symm⟩)
  -- Phase 1: Fournier on `G₁`
  obtain ⟨U, hU⟩ : ∃ U, U = (range (modN G w vs)).sup F := ⟨_, rfl⟩
  have hUle' : U ≤ keepAt G w ∅ := hU ▸ hUle
  have hdegU : ∀ v, U.degree v =
      #((range (modN G w vs)).filter fun k => v ≠ w ∧ v ≠ missed G w vs k) := fun v => by
    subst hU; exact degree_finsetSup_factors hF hdisjR subset_rfl v
  have hdegGU : ∀ v, (keepAt G w ∅ \ U).degree v + U.degree v = (keepAt G w ∅).degree v :=
    fun v => Plantholt.degree_sdiff_add _ hUle' v
  have hdeg1 : ∀ v, (keepAt (keepAt G w ∅ \ U) vs ∅).degree v ≤ (keepAt G w ∅ \ U).degree v :=
    fun v => degree_le_of_le (keepAt_le _ vs ∅)
  have hmax1 : ∀ v, (keepAt (keepAt G w ∅ \ U) vs ∅).degree v ≤ d - modN G w vs := by
    intro v
    have h1 := hdeg1 v
    have h2 := hdegGU v
    have h3 := hdegU v
    by_cases hvw : v = w
    · subst hvw; omega
    have h4 := hdegG' v hvw
    by_cases hvX : v ∈ setX G w vs
    · have h5 := hcntX v hvX _ subset_rfl (mem_range.2 (hlabX v hvX))
      rw [card_range] at h5
      rw [if_pos (hXadj v hvX)] at h4
      omega
    · by_cases hvs : v = vs
      · subst hvs; rw [degree_keepAt_empty_self]; exact Nat.zero_le _
      · have h5 := hcntO v hvw hvX hvs (range (modN G w vs))
        rw [card_range] at h5
        split_ifs at h4 <;> omega
  have hsmall1 : ∀ v, v ∉ setH G w vs →
      (keepAt (keepAt G w ∅ \ U) vs ∅).degree v < d - modN G w vs := by
    intro v hvH
    have h1 := hdeg1 v
    have h2 := hdegGU v
    have h3 := hdegU v
    by_cases hvw : v = w
    · subst hvw; omega
    have hvX : v ∉ setX G w vs := fun h => hvH (hXH v h)
    have hvs : v ≠ vs := fun h => hvH (h ▸ mem_insert_self _ _)
    have hvW : v ∉ setW G w := fun h => hvH (hWH v h)
    have h4 := hdegG' v hvw
    rw [if_pos (hnotW v hvw hvW)] at h4
    have h5 := hcntO v hvw hvX hvs (range (modN G w vs))
    rw [card_range] at h5
    omega
  have hG1col : (keepAt (keepAt G w ∅ \ U) vs ∅).lineGraph.Colorable (d - modN G w vs) := by
    refine colorable_of_full_indep _ _ le_rfl hmax1 fun u v huv hu => ?_
    by_contra hv
    have hv' : v ∈ setH G w vs := by
      by_contra h; exact hv (hsmall1 v h)
    have hu' : u ∈ setH G w vs := by
      by_contra h; have := hsmall1 u h; omega
    have h1 := keepAt_le _ vs ∅ huv
    obtain ⟨j, hj, hj'⟩ := hHedge u v hu' hv' h1.1
    apply h1.2
    rw [hU]
    exact (finsetSup_adj _).2 ⟨j, mem_range.2 hj, hj'⟩
  -- Phase 2: add the factors missing `v*`
  set J := (range (modN G w vs)).filter fun k => missed G w vs k = vs with hJ
  set A := (range (modN G w vs)).filter fun k => ¬ missed G w vs k = vs with hA
  have hJsub : J ⊆ range (modN G w vs) := filter_subset _ _
  have hAsub : A ⊆ range (modN G w vs) := filter_subset _ _
  have hAJ : #J + #A = modN G w vs := by
    rw [hJ, hA, card_filter_add_card_filter_not, card_range]
  have hG2col : (keepAt (keepAt G w ∅ \ U) vs ∅ ⊔ J.sup F).lineGraph.Colorable
      (d - modN G w vs + #J) := by
    refine colorable_sup_family J (fun k hk => hmatch k (hJsub hk)) (fun k hk => ?_)
      (fun a ha b hb hab => hdisjR a (hJsub ha) b (hJsub hb) hab) hG1col
    have hFU : F k ≤ U := hU ▸ le_sup (f := F) (hJsub hk)
    exact (disjoint_sdiff_self_left.mono_left (keepAt_le _ vs ∅)).mono_right hFU
  -- Phase 3: `G₃ = G − w − ∪_{A} F`; removing `v*` from it gives `G₂`
  have hAle : A.sup F ≤ keepAt G w ∅ := Finset.sup_le fun k hk => hFle k (mem_range.1 (hAsub hk))
  have heq : keepAt (keepAt G w ∅ \ A.sup F) vs ∅ = keepAt (keepAt G w ∅ \ U) vs ∅ ⊔ J.sup F := by
    ext a b
    rw [keepAt_empty_adj, sup_adj, keepAt_empty_adj, sdiff_adj, sdiff_adj, finsetSup_adj,
      finsetSup_adj, hU, finsetSup_adj]
    constructor
    · rintro ⟨⟨hab, hA'⟩, ha, hb⟩
      by_cases hU' : ∃ k ∈ range (modN G w vs), (F k).Adj a b
      · obtain ⟨k, hk, hk'⟩ := hU'
        refine Or.inr ⟨k, mem_filter.2 ⟨hk, ?_⟩, hk'⟩
        by_contra hne
        exact hA' ⟨k, mem_filter.2 ⟨hk, hne⟩, hk'⟩
      · exact Or.inl ⟨⟨hab, hU'⟩, ha, hb⟩
    · rintro (⟨⟨hab, hU'⟩, ha, hb⟩ | ⟨k, hk, hk'⟩)
      · exact ⟨⟨hab, fun ⟨j, hj, hj'⟩ => hU' ⟨j, hAsub hj, hj'⟩⟩, ha, hb⟩
      · have hkN := mem_range.1 (hJsub hk)
        have hmk : missed G w vs k = vs := (mem_filter.1 hk).2
        refine ⟨⟨hFle k hkN hk', fun ⟨j, hj, hj'⟩ => ?_⟩, fun ha => ?_, fun hb => ?_⟩
        · have hjk : j ≠ k := fun h => (mem_filter.1 hj).2 (h ▸ hmk)
          exact (disjoint_iff_inf_le.1 (hdisjR j (hAsub hj) k (hJsub hk) hjk)) ⟨hj', hk'⟩
        · exact (hF k hkN).miss_m b (by rw [hmk, ← ha]; exact hk')
        · exact (hF k hkN).miss_m a (by rw [hmk, ← hb]; exact hk'.symm)
  have hG3col : (keepAt (keepAt G w ∅ \ A.sup F) vs ∅).lineGraph.Colorable (d - #A) := by
    rw [heq]
    have : d - modN G w vs + #J = d - #A := by omega
    rw [← this]; exact hG2col
  -- Phase 4: re-insert `v*`
  have hdegA : ∀ v, (A.sup F).degree v = #(A.filter fun k => v ≠ w ∧ v ≠ missed G w vs k) :=
    fun v => degree_finsetSup_factors hF hdisjR hAsub v
  have hdegG3 : ∀ v, (keepAt G w ∅ \ A.sup F).degree v + (A.sup F).degree v =
      (keepAt G w ∅).degree v := fun v => Plantholt.degree_sdiff_add _ hAle v
  have hlabA : ∀ x ∈ setX G w vs, label G w vs x ∈ A := fun x hx =>
    mem_filter.2 ⟨mem_range.2 (hlabX x hx), fun h => by
      have := (missed_eq_iff hXY hx (label G w vs x)).2 rfl
      exact vs_notMem_X (h ▸ this ▸ hx)⟩
  have hAN : #A ≤ modN G w vs := by omega
  have hmax3 : ∀ v, (keepAt G w ∅ \ A.sup F).degree v ≤ d - #A := by
    intro v
    have h1 := hdegG3 v
    have h2 := hdegA v
    by_cases hvw : v = w
    · subst hvw; omega
    have h4 := hdegG' v hvw
    by_cases hvX : v ∈ setX G w vs
    · have h5 := hcntX v hvX A hAsub (hlabA v hvX)
      rw [if_pos (hXadj v hvX)] at h4
      omega
    · by_cases hvs : v = vs
      · subst hvs
        have h5 : A.filter (fun k => v ≠ w ∧ v ≠ missed G w v k) = A := by
          rw [filter_eq_self]
          intro k hk
          exact ⟨hvw, fun he => (mem_filter.1 hk).2 he.symm⟩
        rw [h5] at h2
        split_ifs at h4 <;> omega
      · have h5 := hcntO v hvw hvX hvs A
        split_ifs at h4 <;> omega
  have hx3 : ∀ z, (keepAt G w ∅ \ A.sup F).Adj vs z →
      (keepAt G w ∅ \ A.sup F).degree z < d - #A := by
    intro z hz
    have hG'z : (keepAt G w ∅).Adj vs z := hz.1
    obtain ⟨hGz, hvsw', hzw⟩ := (keepAt_empty_adj G w).1 hG'z
    have hzX : z ∉ setX G w vs := fun h => (mem_setX.1 h).2.2 hGz
    have hzs : z ≠ vs := hGz.ne'
    have hzW : z ∉ setW G w := by
      intro hzW
      obtain ⟨j, hj, hj'⟩ := hHedge vs z (mem_insert_self _ _) (hWH z hzW) hG'z
      have hmj : ¬ missed G w vs j = vs := fun h => (hF j hj).miss_m z (by rw [h]; exact hj')
      exact hz.2 ((finsetSup_adj _).2 ⟨j, mem_filter.2 ⟨mem_range.2 hj, hmj⟩, hj'⟩)
    have h1 := hdegG3 z
    have h2 := hdegA z
    have h4 := hdegG' z hzw
    rw [if_pos (hnotW z hzw hzW)] at h4
    have h5 := hcntO z hzw hzX hzs A
    omega
  have hG3full := colorable_of_add_vertex _ hmax3 vs hx3 hG3col
  -- Phase 5: add the factors through `v*`
  have hG'col : (keepAt G w ∅).lineGraph.Colorable d := by
    have := colorable_sup_family (B := keepAt G w ∅ \ A.sup F) A
      (fun k hk => hmatch k (hAsub hk))
      (fun k hk => disjoint_sdiff_self_left.mono_right (le_sup (f := F) hk))
      (fun a ha b hb hab => hdisjR a (hAsub ha) b (hAsub hb) hab) hG3full
    rw [sdiff_sup_cancel hAle, Nat.sub_add_cancel (by omega)] at this
    exact this
  -- Phase 6: re-insert `w`
  exact colorable_of_regular_keepAt G ⟨n, by omega⟩ hreg w hG'col

end OneFactor
