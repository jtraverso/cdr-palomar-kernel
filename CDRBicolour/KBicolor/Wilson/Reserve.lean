/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.Assembly

/-!
# The reserve in a Wilson residual

Every point outside the embedded groups is adjacent in the residual to every
other point. A linear reserve in each colour therefore supplies H3 even though
the deleted cross packing has large maximum degree. This uses the geometry of
the Wilson residual, not the sparse-deletion completion theorem.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}

/-- Points not used by any group. -/
def reserve : Finset (Fin n) := univ \ univ.image h.embed

theorem mem_reserve {v : Fin n} : v ∈ reserve h ↔ ∀ i P α, v ≠ gv h i P α := by
  simp only [reserve, mem_sdiff, mem_univ, mem_image, true_and, not_exists, not_and,
    forall_const]
  constructor
  · intro hv i P α he
    exact hv (i, P, α) he.symm
  · intro hv u he
    exact hv u.1 u.2.1 u.2.2 he.symm

/-- No cross edge touches the reserve, for any choice of Latin squares. -/
theorem reserve_adj (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) {u v : Fin n}
    (hu : u ∈ reserve h) (huv : u ≠ v) :
    (rG ((crossP h Λ).biUnion triEdges)).Adj u v := by
  rw [rG_adj]
  refine ⟨?_, huv⟩
  intro he
  obtain ⟨p, q, P, Q, α, β, -, heq, -⟩ := (mem_crossEdges h hS Λ).mp he
  exact (mem_reserve h).mp hu p P α heq

theorem reserved_commonNbr_bound (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    {u v : Fin n} (X : Fin k) :
    #((reserve h).filter fun w => lab w = X) ≤
      #(commonNbrs (rHostK lab ((crossP h Λ).biUnion triEdges)) X u v) + 2 := by
  let R := (reserve h).filter fun w => lab w = X
  have hsub : (R.erase u).erase v ⊆
      commonNbrs (rHostK lab ((crossP h Λ).biUnion triEdges)) X u v := by
    intro w hw
    simp only [mem_erase, R, mem_filter] at hw
    simp only [commonNbrs, mem_filter, mem_univ, true_and, rHostK]
    exact ⟨(reserve_adj h hS Λ hw.2.2.1 hw.2.1).symm,
      (reserve_adj h hS Λ hw.2.2.1 hw.1).symm, hw.2.2.2⟩
  have h1 := card_le_card hsub
  have h2 := pred_card_le_card_erase (s := R.erase u) (a := v)
  have h3 := pred_card_le_card_erase (s := R) (a := u)
  change #R ≤ _
  omega

/-- H3 follows from the reserve sizes, without a bound on deleted degree. -/
theorem residual_H3_of_reserve (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) {δR : ℝ}
    (hcls : ∀ X, δR * n ≤ #((reserve h).filter fun w => lab w = X))
    (h4 : 4 ≤ δR * n) :
    CommonNbrCond (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) (δR / 2) := by
  intro u v _ X _
  have hbound := reserved_commonNbr_bound h hS Λ (u := u) (v := v) X
  have hboundR : (#((reserve h).filter fun w => lab w = X) : ℝ) ≤
      #(commonNbrs (rHostK lab ((crossP h Λ).biUnion triEdges)) X u v) + 2 := by
    exact_mod_cast hbound
  rw [Fintype.card_fin]
  linarith [hcls X]

end CDRBicolour.KBicolor.Wilson
