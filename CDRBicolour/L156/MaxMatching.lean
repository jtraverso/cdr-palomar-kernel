/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L156.Step

/-!
# L181, the paper's version: the maximum-matching count

COMPLETION PROOF of L181: for a maximum free matching `T` of the residual support `S` with
unmatched set `U` (`|U| = d₀ ≥ 2`):

* `U` is a used clique (otherwise `T` grows);
* every pair `ab ∈ T` receives at least `d₀` used incidences from `U` (no augmenting path of
  length three);
* every point of `S` has used degree `≤ m+1 = ρ-1`.

Hence `d₀ + |T| ≤ ρ` and `|S| + 2 ≤ 2ρ` (`maxmatch_bound`).  With `N ≥ 6ρ` this gives the room
inequality of the core loop, and `L181_NoAnchor`, `L181_Star` follow.
-/

@[expose] public section

namespace CDRBicolour.L156

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix CDRBicolour.L181

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  {G : SimpleGraph Rw} [DecidableRel G.Adj] {W : Finset Cl} {μ₀ : Cl → ℕ} {ρ c₀ : ℕ} {s₀ : Rw → ℕ}
  {H : Finset Cl}

/-- **The maximum-matching count.** -/
theorem maxmatch_boundQ {D : Finset Rw} {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hs : RowStateQ G W μ₀ ρ c₀ s₀ D χ M) {j₀ : Rw} (hj₀ : j₀ ∉ D) (heven : Even (s₀ j₀))
    {T : Finset (Sym2 Cl)} (hT : Tent G χ M j₀ T)
    (hmax : ∀ T', Tent G χ M j₀ T' → T'.card ≤ T.card)
    (hnp : ¬ (miss G χ j₀ \ cover (M j₀) ⊆ cover T)) :
    (miss G χ j₀ \ cover (M j₀)).card + 2 ≤ 2 * ρ := by
  classical
  set S := miss G χ j₀ \ cover (M j₀) with hS
  set U := S \ cover T with hU
  have hsup : ∀ r ∈ S, r ∈ miss G χ j₀ ∧ r ∉ cover (M j₀) ∧ r ∉ W :=
    fun r hr => hs.support hj₀ hr
  have hcovsub : cover (M j₀) ⊆ miss G χ j₀ := cover_subset_of_partial (hs.good.pairs j₀)
  have hTS : cover T ⊆ S := cover_subset_of_partial hT.1
  have hSc : S.card + (cover (M j₀)).card = s₀ j₀ := by
    rw [← hs.size j₀]; exact card_sdiff_add_card_eq_card hcovsub
  have hMc := card_cover_eq (hs.good.pairs j₀)
  have hTc := card_cover_eq hT.1
  have hUc : U.card + (cover T).card = S.card := card_sdiff_add_card_eq_card hTS
  have hUpos : 0 < U.card := by
    obtain ⟨v, hv, hv'⟩ := not_subset.1 hnp
    exact card_pos.2 ⟨v, mem_sdiff.2 ⟨hv, hv'⟩⟩
  have hU2 : 2 ≤ U.card := by obtain ⟨k, hk⟩ := heven; omega
  have hUS : ∀ {u}, u ∈ U → u ∈ S ∧ u ∉ cover T := fun h => mem_sdiff.1 h
  have hne : ∀ {y z : Cl}, y ∈ cover T → z ∉ cover T → z ≠ y := fun hy hz h => hz (h ▸ hy)
  -- `U` is a used clique
  have hclique : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∃ j, s(u, v) ∈ M j := by
    intro u hu v hv huv
    by_contra hno
    push_neg at hno
    have hT' : Tent G χ M j₀ (insert s(u, v) T) := by
      refine ⟨isPartialPairing_insert hT.1 (hUS hu).1 (hUS hv).1 huv (hUS hu).2 (hUS hv).2, ?_⟩
      intro e he j
      rcases mem_insert.1 he with rfl | he
      · exact hno j
      · exact hT.2 e he j
    have := hmax _ hT'
    rw [card_insert_of_notMem (fun h => (hUS hu).2 (mem_cover.2 ⟨_, h, Sym2.mem_mk_left _ _⟩))]
      at this
    omega
  -- no augmenting path of length three through a pair of `T`
  have hpair : ∀ a b, s(a, b) ∈ T →
      U.card ≤ (U.filter fun u => ∃ j, s(u, a) ∈ M j).card +
        (U.filter fun u => ∃ j, s(u, b) ∈ M j).card := by
    intro a b hab
    have hab' : a ≠ b := fun h => hT.1.1 _ hab (Sym2.mk_isDiag_iff.2 h)
    have haT : a ∈ cover T := mem_cover.2 ⟨_, hab, Sym2.mem_mk_left _ _⟩
    have hbT : b ∈ cover T := mem_cover.2 ⟨_, hab, Sym2.mem_mk_right _ _⟩
    set Fa := U.filter fun u => ¬ ∃ j, s(u, a) ∈ M j
    set Fb := U.filter fun u => ¬ ∃ j, s(u, b) ∈ M j
    have hcross : ∀ u₁ ∈ Fa, ∀ u₂ ∈ Fb, u₁ = u₂ := by
      intro u₁ h₁ u₂ h₂
      by_contra h12
      obtain ⟨hu₁, hfa⟩ := mem_filter.1 h₁
      obtain ⟨hu₂, hfb⟩ := mem_filter.1 h₂
      push_neg at hfa hfb
      set T₀ := T.erase s(a, b)
      have hT₀ := isPartialPairing_erase hT.1 s(a, b)
      have haT₀ : a ∉ cover T₀ := not_mem_cover_erase hT.1 hab (Sym2.mem_mk_left _ _)
      have hbT₀ : b ∉ cover T₀ := not_mem_cover_erase hT.1 hab (Sym2.mem_mk_right _ _)
      have hcovT₀ : cover T₀ ⊆ cover T := fun v hv => by
        obtain ⟨e, he, hve⟩ := mem_cover.1 hv
        exact mem_cover.2 ⟨e, mem_of_mem_erase he, hve⟩
      have hT₁ := isPartialPairing_insert hT₀ (hUS hu₂).1 (hTS hbT) (hne hbT (hUS hu₂).2)
        (fun h => (hUS hu₂).2 (hcovT₀ h)) hbT₀
      have hu₁T₁ : u₁ ∉ cover (insert s(u₂, b) T₀) := by
        rw [mem_cover_insert, not_or, Sym2.mem_iff, not_or]
        exact ⟨⟨h12, hne hbT (hUS hu₁).2⟩, fun h => (hUS hu₁).2 (hcovT₀ h)⟩
      have haT₁ : a ∉ cover (insert s(u₂, b) T₀) := by
        rw [mem_cover_insert, not_or, Sym2.mem_iff, not_or]
        exact ⟨⟨(hne haT (hUS hu₂).2).symm, hab'⟩, haT₀⟩
      have hT' : Tent G χ M j₀ (insert s(u₁, a) (insert s(u₂, b) T₀)) := by
        refine ⟨isPartialPairing_insert hT₁ (hUS hu₁).1 (hTS haT) (hne haT (hUS hu₁).2)
          hu₁T₁ haT₁, ?_⟩
        intro e he j
        rcases mem_insert.1 he with rfl | he
        · exact hfa j
        · rcases mem_insert.1 he with rfl | he
          · exact hfb j
          · exact hT.2 e (mem_of_mem_erase he) j
      have := hmax _ hT'
      rw [card_insert_of_notMem (fun h => hu₁T₁ (mem_cover.2 ⟨_, h, Sym2.mem_mk_left _ _⟩)),
        card_insert_of_notMem (fun h => (hUS hu₂).2 (hcovT₀ (mem_cover.2
          ⟨_, h, Sym2.mem_mk_left _ _⟩))), card_erase_of_mem hab] at this
      have := card_pos.2 ⟨_, hab⟩
      omega
    have hFF : Fa.card + Fb.card ≤ U.card := by
      by_cases hFa : Fa = ∅
      · rw [hFa, card_empty, zero_add]; exact card_le_card (filter_subset _ _)
      · by_cases hFb : Fb = ∅
        · rw [hFb, card_empty, add_zero]; exact card_le_card (filter_subset _ _)
        · obtain ⟨u₁, hu₁⟩ := nonempty_iff_ne_empty.2 hFa
          obtain ⟨u₂, hu₂⟩ := nonempty_iff_ne_empty.2 hFb
          have h1 : Fa.card ≤ 1 := card_le_one.2 fun x hx y hy =>
            (hcross x hx u₂ hu₂).trans (hcross y hy u₂ hu₂).symm
          have h2 : Fb.card ≤ 1 := card_le_one.2 fun x hx y hy =>
            (hcross u₁ hu₁ x hx).symm.trans (hcross u₁ hu₁ y hy)
          omega
    have ha : (U.filter fun u => ∃ j, s(u, a) ∈ M j).card + Fa.card = U.card :=
      card_filter_add_card_filter_not _
    have hb : (U.filter fun u => ∃ j, s(u, b) ∈ M j).card + Fb.card = U.card :=
      card_filter_add_card_filter_not _
    omega
  -- used degrees of the points of `U`
  have hdeg : ∀ u ∈ U, (U.erase u).card +
      ((cover T).filter fun c => ∃ j, s(u, c) ∈ M j).card ≤ ρ - 1 := by
    intro u hu
    have hsub : U.erase u ∪ (cover T).filter (fun c => ∃ j, s(u, c) ∈ M j) ⊆
        univ.filter fun v => ∃ j, s(u, v) ∈ M j := by
      intro v hv
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rcases mem_union.1 hv with hv | hv
      · obtain ⟨hvu, hvU⟩ := mem_erase.1 hv
        exact hclique u hu v hvU (Ne.symm hvu)
      · exact (mem_filter.1 hv).2
    have hdisj : Disjoint (U.erase u) ((cover T).filter fun c => ∃ j, s(u, c) ∈ M j) := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      exact (hUS (mem_of_mem_erase hv)).2 (mem_filter.1 hv').1
    rw [← card_union_of_disjoint hdisj]
    have hu' := hsup u (hUS hu).1
    exact (card_le_card hsub).trans (card_used_leQ hs.good hs.bound hu'.1 hu'.2.1 hu'.2.2)
  -- double counting
  have hswap : ∑ u ∈ U, ((cover T).filter fun c => ∃ j, s(u, c) ∈ M j).card =
      ∑ c ∈ cover T, (U.filter fun u => ∃ j, s(u, c) ∈ M j).card := by
    simp only [card_filter]
    exact sum_comm
  have hlow : T.card * U.card ≤
      ∑ c ∈ cover T, (U.filter fun u => ∃ j, s(u, c) ∈ M j).card := by
    rw [cover, sum_biUnion]
    · rw [← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun e he => ?_
      revert he
      refine Sym2.ind (fun a b hab => ?_) e
      have hab' : a ≠ b := fun h => hT.1.1 _ hab (Sym2.mk_isDiag_iff.2 h)
      rw [Sym2.toFinset_mk_eq, sum_pair hab']
      exact hpair a b hab
    · intro e he f hf hne'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hve hvf
      exact hne' (hT.1.2.2 e he f hf v (Sym2.mem_toFinset.1 hve) (Sym2.mem_toFinset.1 hvf))
  have hupper : ∑ u ∈ U, ((U.erase u).card +
      ((cover T).filter fun c => ∃ j, s(u, c) ∈ M j).card) ≤ U.card * (ρ - 1) := by
    calc _ ≤ ∑ _u ∈ U, (ρ - 1) := sum_le_sum hdeg
      _ = U.card * (ρ - 1) := by rw [sum_const, smul_eq_mul]
  rw [sum_add_distrib, sum_congr rfl fun u hu => card_erase_of_mem hu, sum_const, smul_eq_mul,
    hswap] at hupper
  obtain ⟨e, he⟩ : ∃ e, U.card = e + 1 := ⟨U.card - 1, by omega⟩
  rw [he, Nat.add_sub_cancel] at hupper
  rw [he] at hlow
  have key : (e + 1) * (e + T.card) ≤ (e + 1) * (ρ - 1) := by nlinarith
  have key' : e + T.card ≤ ρ - 1 := Nat.le_of_mul_le_mul_left key (Nat.succ_pos e)
  omega

/-- The room inequality from `|H| ≥ 6ρ` (L156). -/
theorem roomHypQ_of (heven : ∀ j, Even (s₀ j))
    (hN : 6 * ρ + c₀ < H.card + 6) : RoomHypQ G W μ₀ ρ c₀ s₀ H := by
  intro D χ M j₀ T hs hj₀ hT hmax hnp
  have hb := maxmatch_boundQ hs hj₀ (heven j₀) hT hmax hnp
  have hcovsub : cover (M j₀) ⊆ miss G χ j₀ := cover_subset_of_partial (hs.good.pairs j₀)
  have hSc : (miss G χ j₀ \ cover (M j₀)).card + (cover (M j₀)).card = s₀ j₀ := by
    rw [← hs.size j₀]; exact card_sdiff_add_card_eq_card hcovsub
  have hc := hs.openC j₀ hj₀
  omega

end CDRBicolour.L156
