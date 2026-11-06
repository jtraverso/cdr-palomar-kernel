/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Plantholt.Cases2

/-!
# Plantholt 2004, proof of Theorem 1.2: Subcase 3 and the dispatch of Case 2

Subcase 3: an odd number of vertices of degree `D`, every other vertex of the minimum degree `δ`,
at least three of them. Three matchings are removed (`M₁` on `H ∪ {v₁}`, `M₂` on `H ∪ {v₂}`,
`M₃` on `V − v₁ − v₂`); the result has degrees `D − 3` and `δ − 1`.
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {c : ℝ} {G : SimpleGraph V} {D δ0 : ℕ}

/-- **Subcase 3.** -/
theorem remove_three (X : Ctx c G D δ0) (hhigh : Fintype.card V < 2 * #(high G D))
    (hHodd : Odd #(high G D)) {δa : ℕ} (hδa : ∀ v, δa ≤ G.degree v)
    (hboth : ∀ v, G.degree v = D ∨ G.degree v = δa) (hgap : δa + 2 ≤ D)
    {a b d : V} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (ha : G.degree a = δa)
    (hb : G.degree b = δa) (hd : G.degree d = δa) : G.lineGraph.Colorable D := by
  set H := high G D with hH
  have hmax := X.hmax
  have h4 := X.h4
  have hδ0a : δ0 ≤ δa := ha ▸ X.hmin a
  have hD1 := X.hD1
  have hn12 : 12 ≤ Fintype.card V := by omega
  have hδ := X.hδ
  have hcH := card_add_card_compl H
  have haH : a ∉ H := fun h => by have := mem_high.1 h; omega
  have hbH : b ∉ H := fun h => by have := mem_high.1 h; omega
  have hlowδ : ∀ v, v ∉ H → G.degree v = δa := fun v hv => by
    rcases hboth v with h | h
    · exact absurd (mem_high.2 h) hv
    · exact h
  -- `M₁` on `H ∪ {a}`
  set W₁ := insert a H
  have hW₁ : #W₁ = #H + 1 := card_insert_of_notMem haH
  have hW₁c := card_add_card_compl W₁
  obtain ⟨M₁, hM₁⟩ := exists_matchingOn G (W := W₁)
    (by rw [hW₁]; exact hHodd.add_one) fun v hv => by
      have h1 := deg_le_nbIn_add G W₁ v
      have := X.hmin v
      omega
  set G₁ := G \ M₁
  have hdeg₁ : ∀ v, G₁.degree v + (if v ∈ W₁ then 1 else 0) = G.degree v := fun v => by
    split_ifs with hv
    · exact deg_sdiff_mem hM₁ hv
    · rw [deg_sdiff_not_mem hM₁ hv, add_zero]
  -- `M₂` on `H ∪ {b}` in `G₁`
  set W₂ := insert b H
  have hW₂ : #W₂ = #H + 1 := card_insert_of_notMem hbH
  have hW₂c := card_add_card_compl W₂
  have hbW₁ : b ∉ W₁ := by simp [W₁, hab.symm, hbH]
  obtain ⟨M₂, hM₂⟩ := exists_matchingOn G₁ (W := W₂)
    (by rw [hW₂]; exact hHodd.add_one) fun v hv => by
      have h1 := deg_le_nbIn_add G₁ W₂ v
      have h2 := hdeg₁ v
      rcases mem_insert.1 hv with rfl | hvH
      · rw [if_neg hbW₁] at h2
        have := X.hmin v
        omega
      · rw [if_pos (mem_insert_of_mem hvH), mem_high.1 hvH] at h2
        omega
  set G₂ := G₁ \ M₂
  have hdeg₂ : ∀ v, G₂.degree v + (if v ∈ W₂ then 1 else 0) = G₁.degree v := fun v => by
    split_ifs with hv
    · exact deg_sdiff_mem hM₂ hv
    · rw [deg_sdiff_not_mem hM₂ hv, add_zero]
  -- `M₃` on `V − a − b` in `G₂`
  set W₃ := (univ.erase a).erase b
  have hW₃ := card_erase_erase hab
  have hW₃c := card_compl_erase_erase hab
  have hmem₃ : ∀ v, v ∈ W₃ ↔ v ≠ a ∧ v ≠ b := fun v => mem_erase_erase
  obtain ⟨M₃, hM₃⟩ := exists_matchingOn G₂ (W := W₃)
    (by rw [hW₃]; obtain ⟨t, ht⟩ := X.hev; exact ⟨t - 1, by omega⟩) fun v hv => by
      have h1 := deg_le_nbIn_add G₂ W₃ v
      rw [hW₃c] at h1
      rw [hW₃]
      have h2 := hdeg₂ v
      have h3 := hdeg₁ v
      obtain ⟨hva, hvb⟩ := (hmem₃ v).1 hv
      by_cases hvH : v ∈ H
      · rw [if_pos (mem_insert_of_mem hvH)] at h2 h3
        rw [mem_high.1 hvH] at h3
        omega
      · have hv1 : v ∉ W₁ := by simp [W₁, hva, hvH]
        have hv2 : v ∉ W₂ := by simp [W₂, hvb, hvH]
        rw [if_neg hv2] at h2
        rw [if_neg hv1, hlowδ v hvH] at h3
        omega
  set G₃ := G₂ \ M₃
  have hdeg₃ : ∀ v, G₃.degree v = if v ∈ H then D - 3 else δa - 1 := by
    intro v
    have h1 := hdeg₁ v
    have h2 := hdeg₂ v
    have h3 : G₃.degree v + (if v ∈ W₃ then 1 else 0) = G₂.degree v := by
      split_ifs with hv
      · exact deg_sdiff_mem hM₃ hv
      · rw [deg_sdiff_not_mem hM₃ hv, add_zero]
    by_cases hvH : v ∈ H
    · have hva : v ≠ a := fun h => haH (h ▸ hvH)
      have hvb : v ≠ b := fun h => hbH (h ▸ hvH)
      rw [if_pos (mem_insert_of_mem hvH)] at h1 h2
      rw [if_pos ((hmem₃ v).2 ⟨hva, hvb⟩)] at h3
      rw [if_pos hvH, ← mem_high.1 hvH]
      omega
    · rw [if_neg hvH]
      have hlow := hlowδ v hvH
      by_cases hva : v = a
      · subst hva
        rw [if_pos (mem_insert_self _ _)] at h1
        rw [if_neg (by simp [W₂, hab, haH])] at h2
        rw [if_neg (by simp [hmem₃])] at h3
        omega
      · by_cases hvb : v = b
        · subst hvb
          rw [if_neg hbW₁] at h1
          rw [if_pos (mem_insert_self _ _)] at h2
          rw [if_neg (by simp [hmem₃])] at h3
          omega
        · rw [if_neg (by simp [W₁, hva, hvH])] at h1
          rw [if_neg (by simp [W₂, hvb, hvH])] at h2
          rw [if_pos ((hmem₃ v).2 ⟨hva, hvb⟩)] at h3
          omega
  have hmax₃ : ∀ v, G₃.degree v ≤ D - 3 := fun v => by
    rw [hdeg₃]; split_ifs <;> omega
  have hmin₃ : ∀ v, δa - 1 ≤ G₃.degree v := fun v => by
    rw [hdeg₃]; split_ifs <;> omega
  have hno₃ : NoOverfull G₃ (D - 3) := by
    refine noOverfull_of_erase G₃ X.hev hmax₃ hmin₃ (by omega) (by omega) fun w => ?_
    refine erase_bound_of_three G₃ hmax₃ hab had hbd (t := δa - 1) ?_ ?_ ?_ hmin₃ (by omega) w
    · rw [hdeg₃, if_neg haH]
    · rw [hdeg₃, if_neg hbH]
    · rw [hdeg₃, if_neg (fun h => by have := mem_high.1 h; omega)]
  have hcond := X.good.2.2.1
  have hc₃ := X.ih G₃ (D - 3) (δ0 - 1) (by omega)
    ⟨hmax₃, fun v => (Nat.sub_le_sub_right hδ0a 1).trans (hmin₃ v), by
      push_cast [show 3 ≤ D by omega, show 1 ≤ δ0 by omega]; linarith, hno₃⟩
  have hc₂ := colorable_succ_of_matching G₂ hM₃.1 hM₃.degree_le_one hc₃
  have hc₁ := colorable_succ_of_matching G₁ hM₂.1 hM₂.degree_le_one hc₂
  have hc₀ := colorable_succ_of_matching G hM₁.1 hM₁.degree_le_one hc₁
  rwa [show D - 3 + 1 + 1 + 1 = D by omega] at hc₀

/-- **Case 2**: no `D`-full set, and the vertices below `D` are pairwise adjacent. -/
theorem case2 (X : Ctx c G D δ0) (hnf : ∀ S, ¬ IsFull G D S)
    (hcomp : ∀ u v, u ≠ v → G.degree u < D → G.degree v < D → G.Adj u v)
    (hx0 : ∃ x, G.degree x = D) (hnr : ∃ v, G.degree v < D) : G.lineGraph.Colorable D := by
  have hhigh := card_high X.hmax X.hD1 hx0 hcomp
  set H := high G D
  have hmax := X.hmax
  have h4 := X.h4
  have hδ := X.hδ
  by_cases hall : ∀ v, D ≤ G.degree v + 1
  · exact case2_a X hhigh hall hnr
  push_neg at hall
  obtain ⟨v₀, hv₀⟩ := hall
  obtain ⟨a, -, hamin⟩ := (univ : Finset V).exists_min_image (fun v => G.degree v) ⟨v₀, mem_univ _⟩
  set δa := G.degree a with hδa_def
  have hδa : ∀ v, δa ≤ G.degree v := fun v => hamin v (mem_univ v)
  have hgap : δa + 2 ≤ D := by have := hδa v₀; omega
  have hδ0a : δ0 ≤ δa := X.hmin a
  have hbnd := case2_bound X hnf
  set L := univ.filter fun v => G.degree v = δa
  by_cases hL : #L ≤ 2
  · -- Subcase 1
    have hrest : D - δa + 2 ≤ ∑ v ∈ univ.erase a, (D - G.degree v) := by
      have h1 := dfc_add_dsum G hmax
      have h2 := dfc_erase G (D := D) a
      have h3 := hbnd a
      have h5 := mul_sub_two (D := D) (show 2 ≤ Fintype.card V by have := X.hn4; omega)
      omega
    obtain ⟨v₁, hv₁a, hv₁⟩ := exists_lt_of_dfc G (D := D) a (by omega)
    obtain ⟨y, hy, hymin⟩ := (univ.erase a).exists_min_image (fun v => G.degree v)
      ⟨v₁, mem_erase.2 ⟨hv₁a, mem_univ _⟩⟩
    have hya : y ≠ a := ne_of_mem_erase hy
    have hyD : G.degree y < D := (hymin v₁ (mem_erase.2 ⟨hv₁a, mem_univ _⟩)).trans_lt hv₁
    have hz : ∀ z, z ≠ a → z ≠ y → δa + 1 ≤ G.degree z := by
      intro z hza hzy
      by_contra hlt
      have hzδ : G.degree z = δa := by have := hδa z; omega
      have hyδ : G.degree y = δa := by
        have := hymin z (mem_erase.2 ⟨hza, mem_univ _⟩); have := hδa y; omega
      have : #({a, y, z} : Finset V) ≤ #L := by
        apply card_le_card
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> simp [L, hyδ, hzδ, hδa_def]
      rw [card_insert_of_notMem (by simp [hya.symm, hza.symm]),
        card_pair (Ne.symm hzy)] at this
      omega
    refine remove_two X hya.symm (by omega) hyD (fun z h1 h2 => ?_) (fun z _ _ => hbnd z)
      (by have := hbnd a; omega) (by have := hbnd y; omega)
    have := hz z h1 h2; omega
  · -- at least three vertices of minimum degree
    push_neg at hL
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := two_lt_card.1 hL
    simp only [L, mem_filter, mem_univ, true_and] at hp hq hr
    have hHall : ∀ v ∈ H, G.degree v = D := fun v hv => mem_high.1 hv
    have h4D : 3 * Fintype.card V ≤ 4 * D := by omega
    by_cases hHev : Even #H
    · -- Subcase 2, `|H|` even
      refine remove_set X (W := H) hHev subset_rfl hδa (fun v hv => ?_) (fun v hv => ?_)
        hpq hpr hqr hp hq hr (by omega)
      · rw [hHall v hv]; omega
      · rw [hHall v hv]; omega
    · rw [Nat.not_even_iff_odd] at hHev
      by_cases hk : ∃ vk, G.degree vk ≠ D ∧ G.degree vk ≠ δa
      · -- Subcase 2, a vertex of intermediate degree
        obtain ⟨vk, hvkD, hvkδ⟩ := hk
        have hvkH : vk ∉ H := fun h => hvkD (mem_high.1 h)
        have hW : #(insert vk H) = #H + 1 := card_insert_of_notMem hvkH
        refine remove_set X (W := insert vk H) (by rw [hW]; exact hHev.add_one)
          (subset_insert _ _) hδa (fun v hv => ?_) (fun v hv => ?_) hpq hpr hqr hp hq hr
          (by omega)
        · rcases mem_insert.1 hv with rfl | hv
          · have := hδa v; omega
          · rw [hHall v hv]; omega
        · rw [hW]
          rcases mem_insert.1 hv with rfl | hv
          · have := hδa v; omega
          · rw [hHall v hv]; omega
      · -- Subcase 3
        push_neg at hk
        refine remove_three X hhigh hHev hδa (fun v => ?_) hgap hpq hpr hqr hp hq hr
        by_cases h : G.degree v = D
        · exact Or.inl h
        · exact Or.inr (hk v h)

end Plantholt
