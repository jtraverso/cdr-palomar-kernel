/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L181.Completion

/-!
# L181: the augmentation step and the completion loops

* `step`: one or two port moves enlarge a non-perfect tentative matching (room assumed).
* `complete_row`: complete the current row (strong induction on `s₀ j₀ - |T|`), passing through a
  maximum tentative matching, where the room hypothesis `hR` is required.
* `l181_core`: complete all rows (induction on the number of open rows).
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  {G : SimpleGraph Rw} [DecidableRel G.Adj] {W : Finset Cl} {m h₀ c₀ : ℕ} {s₀ : Rw → ℕ}

/-- **The augmentation step.** -/
theorem step {D : Finset Rw} {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hs : RowState G W m h₀ c₀ s₀ D χ M) {j₀ : Rw} (hj₀ : j₀ ∉ D)
    (hroom : s₀ j₀ + 4 * (m + 1) < Fintype.card Cl) (heven : Even (s₀ j₀))
    {T : Finset (Sym2 Cl)} (hT : Tent G χ M j₀ T)
    (hnp : ¬ (miss G χ j₀ \ cover (M j₀) ⊆ cover T)) :
    ∃ χ' M' T', RowState G W m h₀ c₀ s₀ D χ' M' ∧ M' j₀ = M j₀ ∧ Tent G χ' M' j₀ T' ∧
      T.card < T'.card := by
  classical
  set S := miss G χ j₀ \ cover (M j₀) with hS
  have hsup : ∀ r ∈ S, r ∈ miss G χ j₀ ∧ r ∉ cover (M j₀) ∧ r ∉ W :=
    fun r hr => hs.support hj₀ hr
  have hcovsub : cover (M j₀) ⊆ miss G χ j₀ := cover_subset_of_partial (hs.good.pairs j₀)
  have hTS : cover T ⊆ S := cover_subset_of_partial hT.1
  have hSc : S.card + (cover (M j₀)).card = s₀ j₀ := by
    rw [← hs.size j₀]; exact card_sdiff_add_card_eq_card hcovsub
  have hMc := card_cover_eq (hs.good.pairs j₀)
  have hTc := card_cover_eq hT.1
  have hUc : (S \ cover T).card + (cover T).card = S.card := card_sdiff_add_card_eq_card hTS
  have hUpos : 0 < (S \ cover T).card := by
    obtain ⟨v, hv, hv'⟩ := not_subset.1 hnp
    exact card_pos.2 ⟨v, mem_sdiff.2 ⟨hv, hv'⟩⟩
  have hU2 : 2 ≤ (S \ cover T).card := by obtain ⟨k, hk⟩ := heven; omega
  have hroomI : ∀ I : Finset Cl, I.card ≤ 4 →
      (miss G χ j₀).card + I.card * (m + 1) < Fintype.card Cl := by
    intro I hI; rw [hs.size j₀]; nlinarith
  have hxcov : ∀ x, x ∉ miss G χ j₀ → x ∉ cover (M j₀) := fun x hx h => hx (hcovsub h)
  have hne : ∀ {y z : Cl}, y ∈ cover T → z ∉ cover T → z ≠ y := fun hy hz h => hz (h ▸ hy)
  by_cases hT0 : T = ∅
  · -- empty tentative matching: three exposed points
    subst hT0
    have h4 : 4 ≤ S.card := by
      have := hs.openS j₀ hj₀; rw [hs.size j₀] at this; omega
    obtain ⟨p, hp, u, hu, v, hv, hpu, hpv, huv⟩ := two_lt_card.1 (by omega : 2 < S.card)
    obtain ⟨x, hx, hxc⟩ := exists_clean hs.good {p, u, v} (by
        intro r hr
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact hsup _ hp
        · exact hsup _ hu
        · exact hsup _ hv) (hroomI _ (card_le_three.trans (by omega)))
    obtain ⟨χ', M', hs', hmv⟩ := hs.move hj₀ (hsup p hp).1 (hsup p hp).2.1 hx
    have hroot := hmv.root {p, u, v} hxc
    have hfin : ∀ y ∈ S, y ≠ p → (∀ j, s(x, y) ∉ M' j) →
        ∃ χ' M' T', RowState G W m h₀ c₀ s₀ D χ' M' ∧ M' j₀ = M j₀ ∧ Tent G χ' M' j₀ T' ∧
          (∅ : Finset (Sym2 Cl)).card < T'.card := by
      intro y hy hyp hfree
      refine ⟨χ', M', insert s(x, y) ∅, hs', hmv.fixed, ⟨?_, ?_⟩, by simp⟩
      · rw [support_move hmv (hxcov x hx)]
        refine isPartialPairing_insert (isPartialPairing_empty _) (mem_insert_self _ _)
          (mem_insert_of_mem (mem_erase.2 ⟨hyp, hy⟩)) ?_ (by simp [cover]) (by simp [cover])
        rintro rfl; exact hx (hsup _ hy).1
      · intro e he j
        rw [mem_insert] at he
        rcases he with rfl | he
        · exact hfree j
        · exact absurd he (notMem_empty _)
    rcases one_free (by simp) (by simp) huv (Ne.symm hpu) (Ne.symm hpv) hroot with hy | hy
    · exact hfin u hu (Ne.symm hpu) hy
    · exact hfin v hv (Ne.symm hpv) hy
  · -- a pair `ab ∈ T` and two exposed points `p, u`
    obtain ⟨a, b, hab⟩ : ∃ a b, s(a, b) ∈ T := by
      obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hT0
      revert he
      exact Sym2.ind (fun a b he => ⟨a, b, he⟩) e
    have hab' : a ≠ b := fun h => hT.1.1 _ hab (Sym2.mk_isDiag_iff.2 h)
    have haT : a ∈ cover T := mem_cover.2 ⟨_, hab, Sym2.mem_mk_left _ _⟩
    have hbT : b ∈ cover T := mem_cover.2 ⟨_, hab, Sym2.mem_mk_right _ _⟩
    obtain ⟨p, hp, u, hu, hpu⟩ := one_lt_card.1 (by omega : 1 < (S \ cover T).card)
    rw [mem_sdiff] at hp hu
    obtain ⟨x, hx, hxc⟩ := exists_clean hs.good {p, u, a, b} (by
        intro r hr
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hsup _ hp.1
        · exact hsup _ hu.1
        · exact hsup _ (hTS haT)
        · exact hsup _ (hTS hbT)) (hroomI _ card_le_four)
    obtain ⟨χ₁, M₁, hs₁, hmv₁⟩ := hs.move hj₀ (hsup p hp.1).1 (hsup p hp.1).2.1 hx
    have hT₁ : Tent G χ₁ M₁ j₀ T := tent_move hT hp.2 hx (hxcov x hx) hmv₁
    have hS₁ := support_move hmv₁ (hxcov x hx)
    have hxu : x ≠ u := fun h => hx (h ▸ (hsup _ hu.1).1)
    have hxT : x ∉ cover T := fun h => hx (hsup _ (hTS h)).1
    have huS₁ : u ∈ miss G χ₁ j₀ \ cover (M₁ j₀) := by
      rw [hS₁]; exact mem_insert_of_mem (mem_erase.2 ⟨Ne.symm hpu, hu.1⟩)
    have hxS₁ : x ∈ miss G χ₁ j₀ \ cover (M₁ j₀) := by rw [hS₁]; exact mem_insert_self _ _
    have hTS₁ : cover T ⊆ miss G χ₁ j₀ \ cover (M₁ j₀) := cover_subset_of_partial hT₁.1
    by_cases hxu_free : ∀ j, s(x, u) ∉ M₁ j
    · refine ⟨χ₁, M₁, insert s(x, u) T, hs₁, hmv₁.fixed,
        ⟨isPartialPairing_insert hT₁.1 hxS₁ huS₁ hxu hxT hu.2, ?_⟩, ?_⟩
      · intro e he j
        rcases mem_insert.1 he with rfl | he
        · exact hxu_free j
        · exact hT₁.2 e he j
      · rw [card_insert_of_notMem (fun h => hxT (mem_cover.2 ⟨_, h, Sym2.mem_mk_left _ _⟩))]
        omega
    · have hused : ¬ ∀ j, s(x, u) ∉ M₁ j := hxu_free
      have hroot₁ := hmv₁.root {p, u, a, b} hxc
      have hua : u ≠ a := hne haT hu.2
      have hub : u ≠ b := hne hbT hu.2
      have hxa : ∀ j, s(x, a) ∉ M₁ j :=
        (one_free (u := u) (v := a) (by simp) (by simp) hua (Ne.symm hpu)
          (hne haT hp.2).symm hroot₁).resolve_left hused
      have hxb : ∀ j, s(x, b) ∉ M₁ j :=
        (one_free (u := u) (v := b) (by simp) (by simp) hub (Ne.symm hpu)
          (hne hbT hp.2).symm hroot₁).resolve_left hused
      -- second move `u → z`
      have hsup₁ : ∀ r ∈ miss G χ₁ j₀ \ cover (M₁ j₀),
          r ∈ miss G χ₁ j₀ ∧ r ∉ cover (M₁ j₀) ∧ r ∉ W := fun r hr => hs₁.support hj₀ hr
      have haS₁ := hTS₁ haT
      have hbS₁ := hTS₁ hbT
      obtain ⟨z, hz, hzc⟩ := exists_clean hs₁.good {u, x, a, b} (by
          intro r hr
          simp only [mem_insert, mem_singleton] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact hsup₁ _ huS₁
          · exact hsup₁ _ hxS₁
          · exact hsup₁ _ haS₁
          · exact hsup₁ _ hbS₁) (by
          rw [hs₁.size j₀]
          have h4 : ({u, x, a, b} : Finset Cl).card ≤ 4 := card_le_four
          nlinarith)
      have hzc₁ : z ∉ cover (M₁ j₀) :=
        fun h => hz (cover_subset_of_partial (hs₁.good.pairs j₀) h)
      obtain ⟨χ₂, M₂, hs₂, hmv₂⟩ := hs₁.move hj₀ (hsup₁ u huS₁).1 (hsup₁ u huS₁).2.1 hz
      have hT₂ : Tent G χ₂ M₂ j₀ T := tent_move hT₁ hu.2 hz hzc₁ hmv₂
      have hS₂ := support_move hmv₂ hzc₁
      have hzx : z ≠ x := fun h => hz (h ▸ (hsup₁ _ hxS₁).1)
      have hza : z ≠ a := fun h => hz (h ▸ (hsup₁ _ haS₁).1)
      have hzb : z ≠ b := fun h => hz (h ▸ (hsup₁ _ hbS₁).1)
      have hzT : z ∉ cover T := fun h => hz (hsup₁ _ (hTS₁ h)).1
      have hxa₂ : ∀ j, s(x, a) ∉ M₂ j := free_move hmv₂
        (by rw [Sym2.mem_iff, not_or]; exact ⟨Ne.symm hxu, hua⟩)
        (by rw [Sym2.mem_iff, not_or]; exact ⟨hzx, hza⟩) hxa
      have hxS₂ : x ∈ miss G χ₂ j₀ \ cover (M₂ j₀) := by
        rw [hS₂]; exact mem_insert_of_mem (mem_erase.2 ⟨hxu, hxS₁⟩)
      have hzS₂ : z ∈ miss G χ₂ j₀ \ cover (M₂ j₀) := by rw [hS₂]; exact mem_insert_self _ _
      have hTS₂ : cover T ⊆ miss G χ₂ j₀ \ cover (M₂ j₀) := cover_subset_of_partial hT₂.1
      have hfix : M₂ j₀ = M j₀ := hmv₂.fixed.trans hmv₁.fixed
      by_cases hxz_free : ∀ j, s(x, z) ∉ M₂ j
      · refine ⟨χ₂, M₂, insert s(x, z) T, hs₂, hfix,
          ⟨isPartialPairing_insert hT₂.1 hxS₂ hzS₂ (Ne.symm hzx) hxT hzT, ?_⟩, ?_⟩
        · intro e he j
          rcases mem_insert.1 he with rfl | he
          · exact hxz_free j
          · exact hT₂.2 e he j
        · rw [card_insert_of_notMem (fun h => hxT (mem_cover.2 ⟨_, h, Sym2.mem_mk_left _ _⟩))]
          omega
      · have hzx_used : ¬ ∀ j, s(z, x) ∉ M₂ j :=
          fun h => hxz_free (fun j hj => h j (by rw [Sym2.eq_swap]; exact hj))
        have hroot₂ := hmv₂.root {u, x, a, b} hzc
        have hxa' : x ≠ a := hne haT hxT
        have hxb' : x ≠ b := hne hbT hxT
        have hzb₂ : ∀ j, s(z, b) ∉ M₂ j :=
          (one_free (u := x) (v := b) (by simp) (by simp) hxb' hxu
            (Ne.symm hub) hroot₂).resolve_left hzx_used
        -- exchange `ab ↦ xa, zb`
        set T₀ := T.erase s(a, b) with hT₀def
        have hT₀ := isPartialPairing_erase hT₂.1 s(a, b)
        have haT₀ : a ∉ cover T₀ := not_mem_cover_erase hT₂.1 hab (Sym2.mem_mk_left _ _)
        have hbT₀ : b ∉ cover T₀ := not_mem_cover_erase hT₂.1 hab (Sym2.mem_mk_right _ _)
        have hcovT₀ : cover T₀ ⊆ cover T := fun v hv => by
          obtain ⟨e, he, hve⟩ := mem_cover.1 hv
          exact mem_cover.2 ⟨e, mem_of_mem_erase he, hve⟩
        have hT₁' := isPartialPairing_insert hT₀ hzS₂ (hTS₂ hbT) hzb
          (fun h => hzT (hcovT₀ h)) hbT₀
        have hxT₁ : x ∉ cover (insert s(z, b) T₀) := by
          rw [mem_cover_insert, not_or, Sym2.mem_iff, not_or]
          exact ⟨⟨Ne.symm hzx, hxb'⟩, fun h => hxT (hcovT₀ h)⟩
        have haT₁ : a ∉ cover (insert s(z, b) T₀) := by
          rw [mem_cover_insert, not_or, Sym2.mem_iff, not_or]
          exact ⟨⟨Ne.symm hza, hab'⟩, haT₀⟩
        have hT₂' := isPartialPairing_insert hT₁' hxS₂ (hTS₂ haT) hxa' hxT₁ haT₁
        refine ⟨χ₂, M₂, insert s(x, a) (insert s(z, b) T₀), hs₂, hfix, ⟨hT₂', ?_⟩, ?_⟩
        · intro e he j
          rcases mem_insert.1 he with rfl | he
          · exact hxa₂ j
          · rcases mem_insert.1 he with rfl | he
            · exact hzb₂ j
            · exact hT₂.2 e (mem_of_mem_erase he) j
        · rw [card_insert_of_notMem (fun h => hxT₁ (mem_cover.2 ⟨_, h, Sym2.mem_mk_left _ _⟩)),
            card_insert_of_notMem (fun h => hzT (hcovT₀ (mem_cover.2 ⟨_, h, Sym2.mem_mk_left _ _⟩))),
            card_erase_of_mem hab]
          have := card_pos.2 ⟨_, hab⟩
          omega

/-- The room hypothesis of the loop: needed only at a maximum non-perfect tentative matching. -/
def RoomHyp (G : SimpleGraph Rw) [DecidableRel G.Adj] (W : Finset Cl) (m h₀ c₀ : ℕ)
    (s₀ : Rw → ℕ) : Prop :=
  ∀ (D : Finset Rw) (χ : Sym2 Rw → Cl) (M : Rw → Finset (Sym2 Cl)) (j₀ : Rw)
    (T : Finset (Sym2 Cl)), RowState G W m h₀ c₀ s₀ D χ M → j₀ ∉ D → Tent G χ M j₀ T →
    (∀ T', Tent G χ M j₀ T' → T'.card ≤ T.card) →
    ¬ (miss G χ j₀ \ cover (M j₀) ⊆ cover T) → s₀ j₀ + 4 * (m + 1) < Fintype.card Cl

/-- Closing the current row with a perfect tentative matching. -/
theorem close_row {D : Finset Rw} {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hs : RowState G W m h₀ c₀ s₀ D χ M) {j₀ : Rw} (hj₀ : j₀ ∉ D) {T : Finset (Sym2 Cl)}
    (hT : Tent G χ M j₀ T) (hp : miss G χ j₀ \ cover (M j₀) ⊆ cover T) :
    RowState G W m h₀ c₀ s₀ (insert j₀ D) χ (Function.update M j₀ (M j₀ ∪ T)) := by
  classical
  have hperf : IsPerfectPairing (M j₀ ∪ T) (miss G χ j₀) :=
    isPerfectPairing_union (hs.good.pairs j₀) (isPerfectPairing_of_cover hT.1 hp)
  have hupd : ∀ j, j ≠ j₀ → Function.update M j₀ (M j₀ ∪ T) j = M j :=
    fun j hj => Function.update_of_ne hj _ _
  refine ⟨⟨hs.good.proper, hs.good.avoid, ?_, ?_, hs.good.two⟩, hs.high, ?_, ?_, ?_, ?_, hs.size⟩
  · intro j
    by_cases hj : j = j₀
    · subst hj; rw [Function.update_self]; exact isPartialPairing_of_perfect hperf
    · rw [hupd j hj]; exact hs.good.pairs j
  · have hdisj : ∀ j, j ≠ j₀ → Disjoint (M j₀ ∪ T) (M j) := by
      intro j hj
      rw [disjoint_union_left]
      exact ⟨hs.good.disj j₀ j (Ne.symm hj),
        Finset.disjoint_left.2 fun e he hej => hT.2 e he j hej⟩
    intro j j' hne
    by_cases hj : j = j₀
    · subst hj; rw [Function.update_self, hupd j' (Ne.symm hne)]; exact hdisj j' (Ne.symm hne)
    · by_cases hj' : j' = j₀
      · subst hj'; rw [Function.update_self, hupd j hj]; exact (hdisj j hj).symm
      · rw [hupd j hj, hupd j' hj']; exact hs.good.disj j j' hne
  · intro j hj
    by_cases hj' : j = j₀
    · subst hj'; rw [Function.update_self]; exact hperf
    · rw [hupd j hj']; exact hs.done j ((mem_insert.1 hj).resolve_left hj')
  · intro j hj
    rw [hupd j (fun h => hj (h ▸ mem_insert_self _ _))]
    exact hs.openW j (fun h => hj (mem_insert_of_mem h))
  · intro j hj
    rw [hupd j (fun h => hj (h ▸ mem_insert_self _ _))]
    exact hs.openC j (fun h => hj (mem_insert_of_mem h))
  · intro j hj
    rw [hupd j (fun h => hj (h ▸ mem_insert_self _ _))]
    exact hs.openS j (fun h => hj (mem_insert_of_mem h))

/-- **Completion of one row.** -/
theorem complete_row (hR : RoomHyp G W m h₀ c₀ s₀) (heven : ∀ j, Even (s₀ j)) {j₀ : Rw}
    {D : Finset Rw} (hj₀ : j₀ ∉ D) :
    ∀ n (χ : Sym2 Rw → Cl) (M : Rw → Finset (Sym2 Cl)) (T : Finset (Sym2 Cl)),
      RowState G W m h₀ c₀ s₀ D χ M → Tent G χ M j₀ T → s₀ j₀ - T.card = n →
      ∃ χ' M', RowState G W m h₀ c₀ s₀ (insert j₀ D) χ' M' := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro χ M T hs hT hn
  set S := miss G χ j₀ \ cover (M j₀) with hS
  -- a maximum tentative matching
  obtain ⟨Tm, hTm, hmax⟩ := exists_max_image ((S.sym2).powerset.filter fun T' => Tent G χ M j₀ T')
    Finset.card ⟨T, mem_filter.2 ⟨mem_powerset.2 fun e he => mem_sym2_iff.2
      fun v hv => hT.1.2.1 e he v hv, hT⟩⟩
  have hTmT := (mem_filter.1 hTm).2
  have hmax' : ∀ T', Tent G χ M j₀ T' → T'.card ≤ Tm.card := fun T' hT' =>
    hmax T' (mem_filter.2 ⟨mem_powerset.2 fun e he => mem_sym2_iff.2
      fun v hv => hT'.1.2.1 e he v hv, hT'⟩)
  by_cases hp : S ⊆ cover Tm
  · exact ⟨χ, _, close_row hs hj₀ hTmT hp⟩
  · have hroom := hR D χ M j₀ Tm hs hj₀ hTmT hmax' hp
    obtain ⟨χ', M', T', hs', hfix, hT', hlt⟩ := step hs hj₀ hroom (heven j₀) hTmT hp
    have hle : Tm.card ≤ T'.card := hlt.le
    have hT'le : 2 * T'.card ≤ s₀ j₀ := by
      rw [← card_cover_eq hT'.1, ← hs'.size j₀]
      exact (card_le_card (cover_subset_of_partial hT'.1)).trans (card_le_card sdiff_subset)
    have hTTm : T.card ≤ Tm.card := hmax' T hT
    exact ih (s₀ j₀ - T'.card) (by omega) χ' M' T' hs' hT' rfl

/-- **Completion of all rows.** -/
theorem complete_all (hR : RoomHyp G W m h₀ c₀ s₀) (heven : ∀ j, Even (s₀ j)) :
    ∀ n (D : Finset Rw) (χ : Sym2 Rw → Cl) (M : Rw → Finset (Sym2 Cl)),
      RowState G W m h₀ c₀ s₀ D χ M → (univ \ D).card = n →
      ∃ χ' M', RowState G W m h₀ c₀ s₀ univ χ' M' := by
  classical
  intro n
  induction n with
  | zero =>
    intro D χ M hs hn
    have : D = univ := by
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hn
      exact eq_univ_of_forall fun j => hn (mem_univ j)
    subst this
    exact ⟨χ, M, hs⟩
  | succ n ih =>
    intro D χ M hs hn
    obtain ⟨j₀, hj₀⟩ := card_pos.1 (by omega : 0 < (univ \ D).card)
    have hj₀D : j₀ ∉ D := (mem_sdiff.1 hj₀).2
    obtain ⟨χ', M', hs'⟩ := complete_row hR heven hj₀D _ χ M ∅ hs
      ⟨isPartialPairing_empty _, by simp⟩ rfl
    refine ih _ χ' M' hs' ?_
    have h1 : univ \ insert j₀ D = (univ \ D).erase j₀ := by
      ext j; simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_erase, not_or]
    rw [h1, card_erase_of_mem hj₀, hn]; omega

/-- **L181 core.** From an initial state with no complete row, all rows are completed. -/
theorem l181_core (hR : RoomHyp G W m h₀ c₀ s₀) (heven : ∀ j, Even (s₀ j))
    {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)} (hs : RowState G W m h₀ c₀ s₀ ∅ χ M) :
    ∃ χ' M', Good G W m χ' M' ∧
      (univ.filter fun v => v ∉ W ∧ mult G χ' v = m + 2).card = h₀ ∧
      ∀ j, IsPerfectPairing (M' j) (miss G χ' j) := by
  obtain ⟨χ', M', hs'⟩ := complete_all hR heven _ ∅ χ M hs rfl
  exact ⟨χ', M', hs'.good, hs'.high, fun j => hs'.done j (mem_univ j)⟩

end CDRBicolour.L181
