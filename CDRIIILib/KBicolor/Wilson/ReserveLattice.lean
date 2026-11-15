/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.Reserve

/-!
# The physical lattice certificate of a Wilson residual

More than `k+4` reserve vertices in every colour provide the density `BigRk`:
one avoids any prescribed set of at most `k+4` vertices, and every reserve vertex
is universal in the residual. The existing quotient proof `residual_physicalK`
then applies to the actual cross packing. No small deleted-degree bound is used.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}

theorem residual_big_of_reserve (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    (hcls : ∀ X, k + 4 < #((reserve h).filter fun v => lab v = X)) :
    BigRk lab ((crossP h Λ).biUnion triEdges) := by
  intro X B hB
  have hlt : #B < #((reserve h).filter fun v => lab v = X) :=
    lt_of_le_of_lt hB (hcls X)
  obtain ⟨w, hw, hwB⟩ := exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hwR, hwX⟩ := mem_filter.mp hw
  refine ⟨w, hwX, fun v hv => reserve_adj h hS Λ hwR ?_⟩
  intro he
  exact hwB (he ▸ hv)

/-- H2 for the actual Wilson residual, with the original parity and pair identity. -/
theorem residual_H2_of_reserve (hk : 2 ≤ k) (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    (hcls : ∀ X, k + 4 < #((reserve h).filter fun v => lab v = X))
    (hodd : Odd n) (heven : ∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y))
    (hdiv : 3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1)) :
    IsPhysical (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
      (edges (rHostK lab ((crossP h Λ).biUnion triEdges))) := by
  have hbig := residual_big_of_reserve h hS Λ hcls
  let X₀ : Fin k := ⟨0, by omega⟩
  obtain ⟨v₀, -, -⟩ := hbig X₀ ∅ (by simp)
  obtain ⟨o, ho, hoadj⟩ := exists_baseK hbig v₀
  let nx : Fin k → Fin k := fun X => if X.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hnx : ∀ X, nx X ≠ X := by
    intro X he
    simp only [nx] at he
    split_ifs at he with h0
    · have := congrArg Fin.val he
      simp at this
      omega
    · have := congrArg Fin.val he
      simp at this
      omega
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  have hn : Even (Fintype.card (Fin n) - 1) := by
    rw [Fintype.card_fin]
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  exact residual_physicalK hbig ho hnx hoadj X₀ (crossP h Λ) (crossP_allowed h Λ)
    (crossP_disj h hS Λ) rfl hn heven (pair_of_div (ksz lab) hsum hdiv)

end CDRBicolour.KBicolor.Wilson
