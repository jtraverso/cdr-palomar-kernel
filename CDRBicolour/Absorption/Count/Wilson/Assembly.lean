/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.GlobalSeed
public import CDRBicolour.Absorption.Completion

/-!
# Optimal counting constant, part 8: counting (item 4)

The residual host `rG(L)` does not depend on the Latin squares (`LX_eq`).  Fix one decomposition `D`
of it; then every family `Λ` gives the realisation `crossP Λ ∪ D`, and `Λ ↦ crossP Λ ∪ D` is
injective (`card_LFam_le`).  So `realCount ≥ L(t)^{9 |OT|}` and `|OT| ≥ g(g−1)/6`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Count

variable {a b c g t : ℕ} (h : WCond a b c g t) {S : Finset (Finset (Fin g))}

/-- The residual host does not depend on the Latin squares. -/
theorem LX_eq (hS : _root_.STS.IsSTS S) (Λ Λ' : LFam S t) : LX h Λ = LX h Λ' := by
  ext e
  induction e using Sym2.ind with
  | _ u v => rw [mem_crossEdges h hS, mem_crossEdges h hS]

theorem crossP_disjoint_D (hS : _root_.STS.IsSTS S) (Λ : LFam S t) {D : Finset (Finset (Fin (a + b + c)))}
    (hD : ∀ T ∈ D, IsAllowed (rHost (col3 a b c) (LX h Λ)) cdrF T) : Disjoint (crossP h Λ) D := by
  rw [disjoint_left]
  intro X hX hXD
  obtain ⟨x, -, rfl⟩ := mem_image.1 hX
  have hA := hD _ hXD
  have hadj : (rG (LX h Λ)).Adj (pos h Λ x 0) (pos h Λ x 1) :=
    hA.2.1 _ ((mem_blk h).2 ⟨0, rfl⟩) _ ((mem_blk h).2 ⟨1, rfl⟩) (pos_ne h Λ x (by decide))
  rw [rG_adj] at hadj
  apply hadj.1
  refine mem_biUnion.2 ⟨blk h Λ x, mem_image.2 ⟨x, mem_univ _, rfl⟩, ?_⟩
  exact mem_tE.2 ⟨(mem_blk h).2 ⟨0, rfl⟩, (mem_blk h).2 ⟨1, rfl⟩, pos_ne h Λ x (by decide)⟩

open Classical in
/-- **Counting**: distinct Latin families give distinct realisations. -/
theorem card_LFam_le (hS : _root_.STS.IsSTS S) (Λ₀ : LFam S t)
    {D : Finset (Finset (Fin (a + b + c)))}
    (hD : IsDecomposition (rHost (col3 a b c) (LX h Λ₀)) cdrF
      (edges (rHost (col3 a b c) (LX h Λ₀))) D) :
    Fintype.card (LFam S t) ≤ realCount a b c := by
  classical
  have hDΛ : ∀ Λ : LFam S t, IsDecomposition (rHost (col3 a b c) ((crossP h Λ).biUnion triEdges))
      cdrF (edges (rHost (col3 a b c) ((crossP h Λ).biUnion triEdges))) D := by
    intro Λ
    have : (crossP h Λ).biUnion triEdges = LX h Λ₀ := LX_eq h hS Λ Λ₀
    rw [this]; exact hD
  have hreal : ∀ Λ : LFam S t, ∃ S' : CDRBicolour.STS (Fin (a + b + c)),
      S'.blocks = crossP h Λ ∪ D ∧ IsStrictBicolouring S' (col3 a b c) := by
    intro Λ
    obtain ⟨S', hS', hcol, -⟩ := sts_of_packing_union (crossP h Λ) D (crossP_allowed h Λ)
      (crossP_disj h hS Λ) (hDΛ Λ)
    exact ⟨S', hS', hcol⟩
  have hdisj : ∀ Λ : LFam S t, Disjoint (crossP h Λ) D := fun Λ =>
    crossP_disjoint_D h hS Λ fun T hT => by
      have := (hDΛ Λ).1 T hT
      exact this
  unfold realCount
  rw [← card_univ]
  refine card_le_card_of_injOn (fun Λ => crossP h Λ ∪ D) (fun Λ _ => ?_) (fun Λ _ Λ' _ he => ?_)
  · obtain ⟨S', hS', hcol⟩ := hreal Λ
    show crossP h Λ ∪ D ∈ (realBlocks a b c : Set _)
    rw [mem_coe, ← hS']
    exact mem_realBlocks_of S' hcol
  · have e1 : crossP h Λ = (crossP h Λ ∪ D) \ D := by
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint (hdisj Λ)]
    have e2 : crossP h Λ' = (crossP h Λ' ∪ D) \ D := by
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint (hdisj Λ')]
    have : crossP h Λ = crossP h Λ' := by
      rw [e1, e2]; simp only at he; rw [he]
    exact crossP_inj h hS this

open Classical in
/-- The number of Latin families. -/
theorem card_LFam (t : ℕ) :
    Fintype.card (LFam S t) = (_root_.STS.L t) ^ (9 * #(OT S)) := by
  rw [Fintype.card_fun]
  congr 1
  · unfold _root_.STS.L; rw [Nat.card_eq_fintype_card]
  · simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]; ring

/-- An oriented block for every block. -/
theorem card_S_le_OT (hS : _root_.STS.IsSTS S) : #S ≤ #(OT S) := by
  refine le_trans (card_le_card ?_) (card_image_le (s := OT S) (f := tri3))
  intro B hB
  obtain ⟨x, y, z, h1, h2, h3, rfl⟩ := card_eq_three.1 (hS.1 B hB)
  obtain ⟨o, ho1, ho2, hoB⟩ := exists_sorted h1 h2 h3
  exact mem_image.2 ⟨o, mem_OT.2 ⟨ho1, ho2, hoB ▸ hB⟩, hoB⟩

/-- A Steiner triple system on `g` points has at least `g(g−1)/6` blocks. -/
theorem card_S_ge (hS : _root_.STS.IsSTS S) : g * (g - 1) ≤ 6 * #S := by
  classical
  -- every ordered pair of distinct points lies in a block
  have hsub : (univ : Finset (Fin g)).offDiag ⊆ S.biUnion fun B => B.offDiag := by
    intro p hp
    rw [mem_offDiag] at hp
    obtain ⟨B, ⟨hB, h1, h2⟩, -⟩ := hS.2 _ _ hp.2.2
    exact mem_biUnion.2 ⟨B, hB, mem_offDiag.2 ⟨h1, h2, hp.2.2⟩⟩
  have h1 := card_le_card hsub
  rw [offDiag_card, card_univ, Fintype.card_fin] at h1
  have h2 : #(S.biUnion fun B => B.offDiag) ≤ ∑ B ∈ S, #B.offDiag := card_biUnion_le
  have h3 : ∑ B ∈ S, #B.offDiag = 6 * #S := by
    rw [sum_congr rfl fun B hB => by rw [offDiag_card, hS.1 B hB], sum_const, smul_eq_mul]; ring
  have h4 : g * g - g = g * (g - 1) := by rw [Nat.mul_sub_one]
  omega

end CDRBicolour.Absorption.Count.Wilson
