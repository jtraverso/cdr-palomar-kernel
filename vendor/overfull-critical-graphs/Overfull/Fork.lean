/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork59

/-!
# The fork lemma (CCJS Lemma 2.6; Cao–Chen 2020, Proposition B)

Let `G` be `Δ`-critical and `ab ∈ E(G)`. If `Δ ≥ d(a) + d(t₁) + d(t₂) + 1`, then for no colouring
`φ` of `G − ab` with `Δ` colours is there a fork on `a b u s₁ s₂ t₁ t₂`.

`no_fork` proves this under the counting hypothesis `ForkHyp`, assembling Claims 5.6–5.10;
`forkHyp_of_degree` derives `ForkHyp` from the degree condition.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

theorem TFull.swap {k : ℕ} {c : PEC G (Fin k)} {α β₁ β₂ : Fin k}
    (h : TFull c t₁ t₂ α β₁ β₂) : TFull c t₂ t₁ α β₂ β₁ :=
  ⟨both_swap.2 h.1, both_swap.2 h.2.2, both_swap.2 h.2.1⟩

/-- **Fork lemma, counting form.** -/
theorem no_fork (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hH : ForkHyp G a b t₁ t₂) (c : PEC G (Fin G.maxDegree))
    (α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree) (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : False := by
  refine claim56 hG hd hH (fun c α β₁ β₂ γ₁ γ₂ h hr => ?_) c α β₁ β₂ γ₁ γ₂ h
  refine claim57 hG hd hH hr (fun c' h' h0 h1 h2 => ?_) c h
  exact claim58 hG hd hr (fun _ h'' hT hb => claim59 hG hd h'' hr hT hb) hH
    (fun _ h'' hT hb => claim59 hG hd.swap h''.swap hr.swap hT.swap hb) h' ⟨h0, h1, h2⟩

/-- At a vertex outside `{a, b}`, the colours present are exactly as many as its degree. -/
theorem card_compl_missing {c : PEC G (Fin G.maxDegree)} (hcm : IsColMinus c a b) {t : V}
    (hta : t ≠ a) (htb : t ≠ b) : #(univ \ missing c t) = G.degree t := by
  have h1 := card_missing_add_colNbrs c t
  have h2 := hcm.card_colNbrs t
  simp only [hta, htb, or_self, if_false, add_zero] at h2
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  omega

/-- **The degree condition gives the counting hypothesis.** -/
theorem forkHyp_of_degree (hG : IsClassTwo G)
    (hdeg : G.degree a + G.degree t₁ + G.degree t₂ + 1 ≤ G.maxDegree)
    (h₁ : 2 ≤ G.degree t₁) (h₂ : 2 ≤ G.degree t₂) (hat₁ : a ≠ t₁) (hbt₁ : b ≠ t₁)
    (hat₂ : a ≠ t₂) (hbt₂ : b ≠ t₂) : ForkHyp G a b t₁ t₂ := by
  intro c hcm
  obtain ⟨hdis, -⟩ := hcm.ab_facts hG
  set A := missing c a ∪ missing c b with hA
  have hAcard : #A = #(missing c a) + #(missing c b) := by
    refine card_union_of_disjoint (disjoint_left.2 fun θ ha hb => ?_)
    exact hdis θ (mem_missing.1 ha) (mem_missing.1 hb)
  have hma : #(missing c a) + G.degree a = G.maxDegree + 1 := by
    have e1 := card_missing_add_colNbrs c a
    have e2 := hcm.card_colNbrs a
    simp only [true_or, if_true] at e2
    omega
  have hmb : 1 ≤ #(missing c b) := by
    obtain ⟨η, hη⟩ := hcm.exists_free_right
    exact card_pos.2 ⟨η, mem_missing.2 hη⟩
  have hN₁ := card_compl_missing hcm hat₁.symm hbt₁.symm
  have hN₂ := card_compl_missing hcm hat₂.symm hbt₂.symm
  have hmemA : ∀ {θ}, θ ∈ A → InA c a b θ := fun hθ => by
    rcases mem_union.1 hθ with h | h
    · exact Or.inl (mem_missing.1 h)
    · exact Or.inr (mem_missing.1 h)
  -- `A ∩ φ̄(t₁) ∩ φ̄(t₂)` has at least three colours
  have hS : 3 ≤ #(A ∩ (missing c t₁ ∩ missing c t₂)) := by
    have hsub : A ⊆ (A ∩ (missing c t₁ ∩ missing c t₂)) ∪ (univ \ missing c t₁) ∪
        (univ \ missing c t₂) := by
      intro θ hθ
      by_cases e1 : θ ∈ missing c t₁
      · by_cases e2 : θ ∈ missing c t₂
        · exact mem_union_left _ (mem_union_left _ (mem_inter.2 ⟨hθ, mem_inter.2 ⟨e1, e2⟩⟩))
        · exact mem_union_right _ (mem_sdiff.2 ⟨mem_univ _, e2⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_sdiff.2 ⟨mem_univ _, e1⟩))
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    omega
  have hSi : ∀ {t}, t ≠ a → t ≠ b → G.degree a + G.degree t + 3 ≤ G.maxDegree →
      5 ≤ #(A ∩ missing c t) := by
    intro t hta htb hle
    have hsub : A ⊆ (A ∩ missing c t) ∪ (univ \ missing c t) := by
      intro θ hθ
      by_cases e : θ ∈ missing c t
      · exact mem_union_left _ (mem_inter.2 ⟨hθ, e⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨mem_univ _, e⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    have hN := card_compl_missing hcm hta htb
    omega
  have hS₁ := hSi hat₁.symm hbt₁.symm (by omega)
  have hS₂ := hSi hat₂.symm hbt₂.symm (by omega)
  refine ⟨fun x y => ?_, fun x y z w => ?_, fun x y z w => ?_⟩
  · obtain ⟨θ, hθ, hn⟩ := exists_mem_notMem_of_card_lt_card
      (s := ({x, y} : Finset (Fin G.maxDegree))) ((card_le_two).trans_lt hS)
    simp only [mem_insert, mem_singleton, not_or] at hn
    obtain ⟨hθA, hθt⟩ := mem_inter.1 hθ
    exact ⟨θ, hn.1, hn.2, hmemA hθA, mem_missing.1 (mem_inter.1 hθt).1,
      mem_missing.1 (mem_inter.1 hθt).2⟩
  · obtain ⟨θ, hθ, hn⟩ := exists_mem_notMem_of_card_lt_card
      (s := ({x, y, z, w} : Finset (Fin G.maxDegree))) ((card_le_four).trans_lt hS₁)
    simp only [mem_insert, mem_singleton, not_or] at hn
    obtain ⟨hθA, hθt⟩ := mem_inter.1 hθ
    exact ⟨θ, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hmemA hθA, mem_missing.1 hθt⟩
  · obtain ⟨θ, hθ, hn⟩ := exists_mem_notMem_of_card_lt_card
      (s := ({x, y, z, w} : Finset (Fin G.maxDegree))) ((card_le_four).trans_lt hS₂)
    simp only [mem_insert, mem_singleton, not_or] at hn
    obtain ⟨hθA, hθt⟩ := mem_inter.1 hθ
    exact ⟨θ, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hmemA hθA, mem_missing.1 hθt⟩

/-- In a `Δ`-critical graph every vertex with a neighbour has degree at least two (from VAL). -/
theorem two_le_degree (hG : IsDeltaCritical G) {s t : V} (hst : G.Adj s t) : 2 ≤ G.degree t := by
  obtain ⟨c, hcm⟩ := exists_colMinus_of_colorable hst (hG.2.2 s(s, t) (G.mem_edgeSet.2 hst))
  have hv := val hG.2.1 hcm
  have hsub : ((G.neighborFinset s).filter fun z => z ≠ t ∧ G.degree z = G.maxDegree) ⊆
      (G.neighborFinset s).erase t := fun z hz => by
    simp only [mem_filter] at hz
    exact mem_erase.2 ⟨hz.2.1, hz.1⟩
  have h1 := card_le_card hsub
  rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hst), card_neighborFinset_eq_degree] at h1
  have h2 := G.degree_le_maxDegree s
  have h3 : 0 < G.degree s := (G.degree_pos_iff_exists_adj s).2 ⟨t, hst⟩
  omega

/-- **Fork lemma** (CCJS Lemma 2.6; Cao–Chen, JCTB 145 (2020), Proposition B). Let `G` be
`Δ`-critical, `ab ∈ E(G)`, and `Δ ≥ d(a) + d(t₁) + d(t₂) + 1`. Then for every colouring of `G − ab`
with `Δ` colours there is no fork on the seven distinct vertices `a, b, u, s₁, s₂, t₁, t₂`. -/
theorem fork_lemma (hG : IsDeltaCritical G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hdeg : G.degree a + G.degree t₁ + G.degree t₂ + 1 ≤ G.maxDegree)
    (c : PEC G (Fin G.maxDegree)) (α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree)
    (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : False :=
  no_fork hG.2.1 hd (forkHyp_of_degree hG.2.1 hdeg (two_le_degree hG (c.col_adj h.cst₁))
    (two_le_degree hG (c.col_adj h.cst₂)) hd.at₁ hd.bt₁ hd.at₂ hd.bt₂) c α β₁ β₂ γ₁ γ₂ h

end Overfull
